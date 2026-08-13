#!/usr/bin/env python3
"""Select the repository build backend from one deliberately simple marker."""

from __future__ import annotations

from pathlib import Path


DUNE_BUILD_MODE = "dune"
MAKEFILE_BUILD_MODE = "makefile"
BUILD_MODES = frozenset({DUNE_BUILD_MODE, MAKEFILE_BUILD_MODE})


def detect_build_mode(workspace_root: Path) -> str:
    """Use Dune exactly when ``<workspace-root>/_build`` is a directory."""

    root = workspace_root.expanduser().resolve()
    return (
        DUNE_BUILD_MODE
        if (root / "_build").is_dir()
        else MAKEFILE_BUILD_MODE
    )


def uses_dune(workspace_root: Path) -> bool:
    return detect_build_mode(workspace_root) == DUNE_BUILD_MODE
