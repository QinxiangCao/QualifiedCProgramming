#!/usr/bin/env python3
"""Generate Rocq examples on Linux, macOS and Windows with Python 3."""

import argparse
import asyncio
import os
import shutil
import sys
import tempfile
import time
from contextlib import ExitStack

from generation_tasks import (
    ROOT, TASK_TYPES, BuiltinExport, GenerationTask, ProgramVC, StrategyVC,
    command, discover, task_name, temporary_outputs,
)

class Job:
    """One subprocess and its result; the outer ExitStack owns its log."""

    def __init__(self, task: GenerationTask, log):
        self.task = task
        self.log = log
        self.since = time.monotonic()
        self.output = None
        self.process = None
        self.code = 1
        self.cancelled = False

    @property
    def display_path(self):
        return task_name(self.task)

    @property
    def succeeded(self):
        return self.code == 0 and not self.cancelled

    async def run(self):
        try:
            args, self.output = command(self.task)
            self.output.mkdir(parents=True, exist_ok=True)
            await self.run_process(args)
        except OSError as error:
            self.log.write((str(error) + "\n").encode("utf-8"))
        self.cleanup_output()

    async def run_process(self, args):
        launch = asyncio.ensure_future(
            asyncio.create_subprocess_exec(
                *args,
                cwd=ROOT,
                stdin=asyncio.subprocess.DEVNULL,
                stdout=self.log,
                stderr=asyncio.subprocess.STDOUT,
            )
        )
        try:
            self.process = await asyncio.shield(launch)
        except asyncio.CancelledError:
            # Obtain the handle even when cancellation interrupts creation.
            self.cancelled = True
            self.process = await launch
            await self.stop()
            return
        try:
            self.code = await self.process.wait()
        except asyncio.CancelledError:
            self.cancelled = True
            await self.stop()

    async def stop(self):
        if self.process.returncode is not None:
            self.code = self.process.returncode
            return
        try:
            self.process.terminate()
        except ProcessLookupError:
            pass
        try:
            self.code = await asyncio.wait_for(self.process.wait(), timeout=3)
        except asyncio.TimeoutError:  # noqa: UP041 -- Distinct from TimeoutError before Python 3.11.
            self.process.kill()
            self.code = await self.process.wait()

    def cleanup_output(self):
        """Remove only this job's staging files, after its child has exited."""
        if self.output is None:
            return
        for path in temporary_outputs(self.task, self.output):
            self.remove_temporary(path)

    def remove_temporary(self, path):
        try:
            path.unlink()
        except FileNotFoundError:
            pass
        except OSError as error:
            self.log.write(
                ("Temporary-file cleanup: " + str(error) + "\n").encode("utf-8")
            )
            self.code = self.code or 1

    def report_failure(self):
        label = "INTERRUPTED" if self.cancelled else "FAILED"
        print(
            f"\n--- {label}: {self.display_path} (exit {self.code}) ---",
            flush=True,
        )
        self.log.seek(0)
        print(
            self.log.read().decode("utf-8", errors="replace").rstrip()
            or "(no subprocess output)",
            flush=True,
        )


class Runner:
    def __init__(self, total, logs):
        self.total = total
        self.logs = logs
        self.failures: list[Job] = []
        self.started = self.completed = self.succeeded = 0
        self.interrupted = False
        self.began = time.monotonic()
        self.interactive = sys.stdout.isatty() and not os.environ.get("CI")
        self.progress_width = 0

    def clear_progress(self):
        if self.progress_width:
            print("\r" + " " * self.progress_width + "\r", end="", flush=True)
            self.progress_width = 0

    def show_progress(self):
        if not self.interactive:
            return
        self.clear_progress()
        cancelled = sum(job.cancelled for job in self.failures)
        failed = len(self.failures) - cancelled
        text = (
            f"Progress {self.completed}/{self.total} | Running {self.started - self.completed}"
            f" | OK {self.succeeded} | Failed {failed} | Interrupted {cancelled}"
        )
        width = max(0, shutil.get_terminal_size().columns - 1)
        text = text[:width]
        print(text, end="", flush=True)
        self.progress_width = len(text)

    def start(self, task: GenerationTask):
        log = self.logs.enter_context(tempfile.TemporaryFile())  # noqa: SIM115 -- ExitStack retains logs until the final report.
        job = Job(task, log)
        self.started += 1
        self.show_progress()
        return job

    def finish(self, job):
        self.completed += 1
        status = "INTERRUPTED" if job.cancelled else "OK" if job.succeeded else "FAIL"
        self.clear_progress()
        print(
            f"[{status}] {job.display_path} ({time.monotonic() - job.since:.1f}s)",
            flush=True,
        )
        if job.succeeded:
            self.succeeded += 1
            job.log.close()
        else:
            self.failures.append(job)
        self.show_progress()

    def report(self):
        self.clear_progress()
        cancelled = sum(job.cancelled for job in self.failures)
        failed = len(self.failures) - cancelled
        print(
            f"\nSummary: {self.succeeded} succeeded, {failed} failed, {cancelled} interrupted, {self.total - self.started} not started ({time.monotonic() - self.began:.1f}s)",
            flush=True,
        )
        for job in self.failures:
            if job.cancelled:
                continue
            job.report_failure()
        if self.interrupted:
            return 130
        if self.failures:
            code = self.failures[0].code
            return code if code > 0 else 1
        return 0


async def worker(runner, pending):
    for task in pending:
        if runner.interrupted:
            return
        job = runner.start(task)
        await job.run()
        runner.finish(job)


async def run_phase(runner, phase, label, jobs):
    if not phase:
        return
    runner.clear_progress()
    print(f"\n{label}: {len(phase)} tasks, {jobs} jobs", flush=True)
    pending = iter(phase)
    workers = [
        asyncio.ensure_future(worker(runner, pending))
        for _ in range(min(jobs, len(phase)))
    ]
    group = asyncio.gather(*workers)
    try:
        await asyncio.shield(group)
    except asyncio.CancelledError:
        runner.interrupted = True
        runner.clear_progress()
        print("\nInterrupted; stopping running tasks...", flush=True)
        for task in workers:
            task.cancel()
        await group


async def run_phases(runner, tasks: list[GenerationTask], jobs: int):
    for kind, label, concurrency in (
        (BuiltinExport, "Builtin strategies", 1),
        (StrategyVC, "Strategies", jobs),
        (ProgramVC, "C examples", jobs),
    ):
        phase = [task for task in tasks if isinstance(task, kind)]
        await run_phase(runner, phase, label, concurrency)
        if runner.failures or runner.interrupted:
            return


async def _run_tasks(tasks: list[GenerationTask], jobs: int):
    """Run bounded workers, with a barrier between strategies and C."""
    with ExitStack() as logs:
        runner = Runner(len(tasks), logs)
        await run_phases(runner, tasks, jobs)
        return runner.report()


def run_tasks(tasks: list[GenerationTask], jobs: int) -> int:
    return asyncio.run(_run_tasks(tasks, jobs))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "task_types",
        nargs="*",
        choices=TASK_TYPES,
        help="task types to run (default: all)",
    )
    parser.add_argument(
        "--list", action="store_true", help="list inputs without generating files"
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="maximum concurrent tasks (default: 1)",
    )
    options = parser.parse_args()
    if options.jobs < 1:
        parser.error("--jobs must be at least 1")
    os.chdir(ROOT)
    tasks = discover()
    if options.task_types:
        selected_types = tuple(TASK_TYPES[name] for name in set(options.task_types))
        tasks = [task for task in tasks if isinstance(task, selected_types)]
    if options.list:
        for task in tasks:
            print(task_name(task) if isinstance(task, BuiltinExport) else task.source.as_posix())
        return 0
    return run_tasks(tasks, options.jobs)


if __name__ == "__main__":
    sys.exit(main())
