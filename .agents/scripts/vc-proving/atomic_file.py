"""Small, shared primitives for durable same-directory file replacement.

Callers remain responsible for validating ownership and symlink boundaries
before invoking these helpers.  This module owns only the mechanical write:
an unpredictable regular temporary file, flush/fsync, and ``os.replace`` in
the destination directory.
"""

from __future__ import annotations

import os
import shutil
import tempfile
from collections.abc import Callable
from pathlib import Path


def atomic_write_bytes(
    destination: Path,
    payload: bytes,
    *,
    suffix: str = ".tmp",
    validate_prepared: Callable[[Path], None] | None = None,
    validate_commit: Callable[[], None] | None = None,
) -> None:
    """Durably replace ``destination`` with ``payload``.

    ``validate_prepared`` can seal or inspect the fully flushed temporary
    file. ``validate_commit`` runs immediately before the replace and can
    enforce a caller-owned compare-and-swap condition. Either callback may
    raise; the destination then remains untouched and the temporary is
    removed.
    """

    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{destination.name}.",
        suffix=suffix,
        dir=destination.parent,
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        if validate_prepared is not None:
            validate_prepared(temporary)
        if validate_commit is not None:
            validate_commit()
        os.replace(temporary, destination)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def atomic_write_text(
    destination: Path,
    text: str,
    *,
    suffix: str = ".tmp",
) -> None:
    """Durably replace ``destination`` with UTF-8/LF text."""

    atomic_write_bytes(destination, text.encode("utf-8"), suffix=suffix)


def atomic_copy_file(
    source: Path,
    destination: Path,
    *,
    suffix: str = ".tmp",
    preserve_metadata: bool = True,
) -> None:
    """Durably replace ``destination`` with the bytes from ``source``."""

    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{destination.name}.",
        suffix=suffix,
        dir=destination.parent,
    )
    temporary = Path(temporary_name)
    try:
        with source.open("rb") as source_handle, os.fdopen(
            descriptor, "wb"
        ) as destination_handle:
            shutil.copyfileobj(source_handle, destination_handle)
            destination_handle.flush()
            os.fsync(destination_handle.fileno())
        if preserve_metadata:
            shutil.copystat(source, temporary, follow_symlinks=False)
            # Windows rejects fsync on a read-only descriptor with ``bad fd``.
            # The payload was already flushed through the writable descriptor;
            # metadata preservation must not reopen the file read-only merely
            # to repeat that durability step.
        os.replace(temporary, destination)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
