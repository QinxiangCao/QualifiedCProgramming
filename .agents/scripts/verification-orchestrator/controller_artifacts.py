"""Owner report contract and public validation using the runtime validators."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any
from controller_state import _json_load, validate_state

TERMINAL_REPORT_STATUSES = ("completed", "blocked")
BLOCKER_FIELDS = {"failure_class", "kind", "vcs", "message", "repair_boundary"}
BLOCKER_VC_FIELDS = {"name", "parent", "annotation_location"}


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _report_errors(payload: dict[str, Any], *, context: str) -> list[str]:
    errors: list[str] = []
    allowed = {"status", "blocker"} if payload.get("status") == "blocked" else {"status"}
    if set(payload) != allowed:
        errors.append(f"{context} report contains unsupported fields")
    if payload.get("status") not in TERMINAL_REPORT_STATUSES:
        errors.append(f"{context} report requires a terminal status")
    if payload.get("status") == "blocked":
        blocker = payload.get("blocker")
        if not isinstance(blocker, dict) or set(blocker) != BLOCKER_FIELDS:
            errors.append(f"{context} blocked report requires one complete blocker")
        else:
            for field in ("failure_class", "kind", "message", "repair_boundary"):
                if not _nonempty_string(blocker.get(field)):
                    errors.append(f"{context} blocker.{field} must be non-empty")
            vcs = blocker.get("vcs")
            if not isinstance(vcs, list):
                errors.append(f"{context} blocker.vcs must be a list")
            else:
                for index, vc in enumerate(vcs):
                    if not isinstance(vc, dict) or set(vc) != BLOCKER_VC_FIELDS:
                        errors.append(
                            f"{context} blocker.vcs[{index}] requires exact fields"
                        )
                    elif (
                        not _nonempty_string(vc.get("name"))
                        or not _nonempty_string(vc.get("annotation_location"))
                        or (
                            vc.get("parent") is not None
                            and not _nonempty_string(vc.get("parent"))
                        )
                    ):
                        errors.append(f"{context} blocker.vcs[{index}] is invalid")
    return errors


def _run_log_errors(path: Path | None) -> list[str]:
    if path is None or not path.is_file():
        return ["run-log validation requires an existing --path"]
    errors: list[str] = []
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            errors.append(f"line {line_number}: {exc}")
            continue
        if not isinstance(record, dict):
            errors.append(f"line {line_number}: run log record must be an object")
        elif (
            set(record) != {"at", "event", "phase", "details"}
            or not _nonempty_string(record.get("at"))
            or not _nonempty_string(record.get("event"))
            or not _nonempty_string(record.get("phase"))
            or not isinstance(record.get("details"), dict)
        ):
            errors.append(f"line {line_number}: invalid run log record")
    return errors


def validate_artifact_payload(kind: str, payload: Any, *, path: Path | None = None) -> list[str]:
    if kind == "run-log":
        return _run_log_errors(path)
    if not isinstance(payload, dict):
        return ["artifact must be a JSON object"]
    if kind in {"agent-report", "group-worker-report"}:
        return _report_errors(payload, context=kind)
    if kind == "controller-state":
        return validate_state(payload)
    if kind == "annotation-plan":
        from annotation_design import annotation_plan_errors
        return annotation_plan_errors(payload, require_ready=False)
    return [f"unsupported artifact kind: {kind}"]


def validate_artifact(args) -> int:
    path = Path(args.path).expanduser().absolute()
    try:
        payload = None if args.kind == "run-log" else _json_load(path)
        errors = validate_artifact_payload(args.kind, payload, path=path)
    except (OSError, ValueError, SystemExit) as exc:
        errors = [f"artifact cannot be read: {exc}"]
    print(json.dumps({"status": "invalid" if errors else "valid", "errors": errors}, indent=2))
    return int(bool(errors))
