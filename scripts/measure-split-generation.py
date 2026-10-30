"""Measure generation units in an external directory without replacing proofs."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from binaries import find_binary
from generation_tasks import ProgramVC, command as generation_command

ROOT = Path(__file__).resolve().parents[1]


def normalized(text):
    return re.sub(r'\s+', '', re.sub(r'\(\*[\s\S]*?\*\)', '', text))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--exclude', action='append', default=[], help='source stem to omit (repeatable)')
    parser.add_argument('--manifest', type=Path, default=ROOT / 'scripts/split-generation-manifest.json')
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout <= 0:
        parser.error('jobs and timeout must be positive')
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error('output must be outside the repository to protect saved proofs')
    output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads(args.manifest.read_text())
    binary = find_binary("symexec")
    metadata = dict(base_commit=manifest['base_commit'], jobs=args.jobs,
                    timeout_seconds=args.timeout, platform=os.name,
                    measurement='wall-clock seconds under the specified concurrency',
                    binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest())
    units = [u for c in manifest['cases'] for u in c['units']]
    units = [u for u in units if Path(u['source']).stem not in args.exclude]

    def run(unit):
        name = Path(unit['source']).stem
        folder = output / name
        folder.mkdir()
        command, _ = generation_command(ProgramVC(Path(unit['source'])), output=folder)
        start = time.perf_counter()
        with (folder / 'generation.log').open('wb') as log:
            try:
                proc = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                      timeout=args.timeout)
                code = proc.returncode
                status = 'completed' if code == 0 else 'failed'
            except subprocess.TimeoutExpired:
                code, status = None, 'timeout'
        elapsed = round(time.perf_counter() - start, 3)
        generated = folder / (name + '_goal.v')
        saved = ROOT / (unit['rocq_stem'] + '_goal.v')
        match = None
        if status == 'completed':
            match = generated.is_file() and normalized(generated.read_text(encoding='utf-8')) == normalized(saved.read_text(encoding='utf-8'))
        result = dict(source=unit['source'], name=unit['name'], functions=unit['functions'], status=status,
                      seconds=elapsed, exit_code=code, goal_matches_saved=match,
                      log=str(folder / 'generation.log'), command=command)
        (folder / 'result.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
        return result

    results = []
    def save():
        (output / 'results.json').write_text(json.dumps(dict(**metadata, results=results), indent=2), encoding='utf-8')

    save()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = [pool.submit(run, unit) for unit in units]
        for future in concurrent.futures.as_completed(pending):
            result = future.result()
            results.append(result)
            save()
            print(f"{len(results)}/{len(units)} {result['name']}: {result['status']} "
                  f"{result['seconds']:.3f}s goal_match={result['goal_matches_saved']}", flush=True)


if __name__ == '__main__':
    main()
