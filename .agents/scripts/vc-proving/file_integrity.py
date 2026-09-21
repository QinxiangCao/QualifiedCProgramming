"""Read complete, ordinary files without following path redirections."""

from __future__ import annotations

import os
import stat
from collections.abc import Mapping
from typing import Any
from pathlib import Path

from path_utils import fixed_path_under


def _fixed_artifact_leaf(
    *,
    root: Path,
    relative: str,
    label: str,
) -> Path:
    """Return one confined lexical leaf without resolving that leaf itself."""

    owner_input = Path(os.path.abspath(os.fspath(root.expanduser())))
    relative_path = Path(relative)
    if (
        relative_path.is_absolute()
        or ".." in relative_path.parts
        or not relative_path.name
    ):
        raise ValueError(f"{label} must be a repository-relative file: {relative}")
    try:
        owner = fixed_path_under(owner_input, owner_input, label=f"{label} root")
        parent = fixed_path_under(
            (owner / relative_path).parent,
            owner,
            label=f"{label} parent",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    return parent / relative_path.name


def _metadata_is_link_like(metadata: os.stat_result) -> bool:
    return stat.S_ISLNK(metadata.st_mode) or bool(
        int(getattr(metadata, "st_file_attributes", 0) or 0)
        & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)
    )


def _stable_metadata(metadata: os.stat_result) -> tuple[int, int, int, int]:
    return (
        int(metadata.st_dev),
        int(metadata.st_ino),
        int(metadata.st_size),
        int(metadata.st_mtime_ns),
    )


def _lexical_regular_file_snapshot(
    *,
    root: Path,
    relative: str,
    label: str,
) -> dict[str, Any]:
    """Read one stable non-link regular leaf without following a replacement.

    ``lstat`` rejects directories, FIFOs, and link/reparse leaves before open;
    ``O_NONBLOCK`` ensures a FIFO swapped in during the race cannot stall the
    controller. The descriptor and a second lexical stat must identify the
    same unchanged regular file before any bytes are accepted.
    """

    try:
        path = _fixed_artifact_leaf(root=root, relative=relative, label=label)
    except ValueError as exc:
        return {
            "path": Path(os.path.abspath(os.fspath(root.expanduser()))) / relative,
            "state": "invalid",
            "message": str(exc),
        }
    try:
        before = os.lstat(path)
    except FileNotFoundError:
        return {"path": path, "state": "missing"}
    except OSError as exc:
        return {"path": path, "state": "unreadable", "message": str(exc)}
    if _metadata_is_link_like(before) or not stat.S_ISREG(before.st_mode):
        return {
            "path": path,
            "state": "nonregular",
            "message": f"{label} is not a non-link regular file: {relative}",
        }

    flags = os.O_RDONLY
    for name in ("O_BINARY", "O_CLOEXEC", "O_NOFOLLOW", "O_NONBLOCK"):
        flags |= int(getattr(os, name, 0) or 0)
    descriptor: int | None = None
    try:
        descriptor = os.open(path, flags)
        opened = os.fstat(descriptor)
        if (
            not stat.S_ISREG(opened.st_mode)
            or (opened.st_dev, opened.st_ino) != (before.st_dev, before.st_ino)
        ):
            raise OSError("file changed to a non-regular or different leaf")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        after_open = os.fstat(descriptor)
        after_lexical = os.lstat(path)
        if (
            _metadata_is_link_like(after_lexical)
            or not stat.S_ISREG(after_lexical.st_mode)
            or _stable_metadata(before) != _stable_metadata(opened)
            or _stable_metadata(opened) != _stable_metadata(after_open)
            or _stable_metadata(after_open) != _stable_metadata(after_lexical)
        ):
            raise OSError("file changed while it was being read")
    except OSError as exc:
        return {"path": path, "state": "unreadable", "message": str(exc)}
    finally:
        if descriptor is not None:
            os.close(descriptor)

    payload = b"".join(chunks)
    return {
        "path": path,
        "state": "present",
        "size": len(payload),
        "data": payload,
        "identity": (int(after_open.st_dev), int(after_open.st_ino)),
    }


def _snapshot_text(snapshot: Mapping[str, Any], *, label: str) -> str:
    if snapshot.get("state") != "present" or not isinstance(
        snapshot.get("data"), bytes
    ):
        raise ValueError(f"{label} is not a readable non-link regular file")
    try:
        return snapshot["data"].decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{label} is not valid UTF-8: {exc}") from exc
