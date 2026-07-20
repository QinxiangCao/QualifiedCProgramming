from __future__ import annotations

from pathlib import Path
import re


def _term(*codes: int) -> str:
    return "".join(chr(code) for code in codes)


BANNED_TERMS = (
    _term(97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 95, 115, 99, 114, 97, 116, 99, 104, 95, 108, 105, 98),
    _term(119, 111, 114, 107, 101, 114, 95, 104, 101, 108, 112, 101, 114, 95, 115, 99, 114, 97, 116, 99, 104, 95, 108, 105, 98),
    _term(116, 97, 115, 107, 95, 108, 111, 99, 97, 108, 95, 115, 99, 114, 97, 116, 99, 104, 95, 108, 105, 98),
    _term(99, 111, 109, 109, 111, 110, 95, 99, 97, 115, 101, 95, 102, 111, 114, 109, 97, 108, 95, 108, 105, 98),
    _term(68, 101, 108, 101, 103, 97, 116, 105, 111, 110, 32, 84, 105, 99, 107, 101, 116),
    _term(83, 117, 98, 97, 103, 101, 110, 116, 32, 82, 101, 116, 117, 114, 110, 32, 82, 101, 112, 111, 114, 116),
    _term(67, 97, 115, 101, 32, 66, 114, 105, 101, 102),
    _term(87, 105, 116, 110, 101, 115, 115, 32, 76, 101, 100, 103, 101, 114),
    _term(80, 104, 97, 115, 101, 32, 83, 116, 97, 116, 117, 115),
    _term(97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 45, 103, 97, 116, 101),
    _term(118, 99, 45, 112, 108, 97, 110, 45, 103, 97, 116, 101),
    _term(118, 99, 45, 112, 114, 111, 118, 105, 110, 103, 45, 103, 97, 116, 101),
    _term(46, 116, 109, 112, 32, 115, 99, 114, 97, 116, 99, 104),
    _term(46, 119, 111, 114, 107, 116, 114, 101, 101, 115),
    _term(111, 108, 100, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 112, 97, 116, 104),
    _term(111, 108, 100, 32, 105, 110, 112, 117, 116, 47, 108, 111, 103, 47, 114, 101, 112, 111, 114, 116, 47, 111, 117, 116, 112, 117, 116, 32, 102, 105, 108, 101, 115),
    _term(26087, 32, 103, 114, 111, 117, 112, 32, 119, 111, 114, 107, 116, 114, 101, 101),
    _term(26087, 32, 114, 111, 117, 110, 100),
    _term(26087, 32, 109, 101, 114, 103, 101),
    _term(26087, 29256),
    _term(26087, 31995, 32479),
    _term(38544, 34255, 30446, 24405),
)

REMOVED_ARTIFACT_TERMS = (
    _term(115, 117, 109, 109, 97, 114, 121, 95, 97, 103, 101, 110, 116),
    _term(97, 103, 101, 110, 116, 95, 111, 117, 116, 112, 117, 116, 115, 46, 116, 120, 116),
    _term(46, 99, 111, 100, 101, 120, 47, 115, 101, 115, 115, 105, 111, 110, 115),
    _term(114, 101, 117, 115, 101, 95, 110, 111, 116, 101, 46, 106, 115, 111, 110),
    _term(99, 111, 109, 109, 111, 110, 95, 99, 97, 115, 101, 95, 102, 111, 114, 109, 97, 108, 95, 108, 105, 98),
    _term(102, 111, 114, 98, 105, 100, 100, 101, 110, 95, 108, 101, 109, 109, 97, 46, 109, 100),
    _term(114, 101, 112, 111, 114, 116, 95, 115, 104, 97, 50, 53, 54),
)

MIGRATION_BANNED_TERMS = (
    "dune build",
    "dune_utils.py",
    "rocq-mcp",
    "rocq_",
    'direct_coqc.status == "forbidden"',
    '"direct_coqc": {"status": "forbidden"}',
    "_dune_builds",
    "dune_build",
    "dune_workspace",
    _term(100, 117, 110, 101, 95, 99, 97, 99, 104, 101),
)


def _active_paths(repo: Path) -> list[Path]:
    paths = [repo / "AGENTS.md", repo / "AGENTS_WIN.md"]
    paths.extend((repo / ".agents" / "skills").rglob("SKILL.md"))
    paths.extend((repo / ".agents" / "skills").rglob("*.md"))
    paths.extend((repo / ".agents" / "skills" / "vc-proving" / "scripts").glob("*.py"))
    paths.extend((repo / ".agents" / "skills" / "verification-orchestrator" / "scripts").glob("*.py"))
    return sorted(
        {
            path
            for path in paths
            if path.name != "scheduler-mechanism.md"
            and "skills-en" not in path.parts
            and "skills-zh" not in path.parts
            and "test" not in path.parts
        }
    )


def test_active_docs_and_scripts_use_current_terms() -> None:
    repo = Path(__file__).resolve().parents[5]

    offenders: list[str] = []
    for path in _active_paths(repo):
        text = path.read_text(encoding="utf-8")
        for term in BANNED_TERMS + REMOVED_ARTIFACT_TERMS:
            if term in text:
                offenders.append(f"{path.relative_to(repo)}: {term}")
        if "worktree" in text.lower():
            offenders.append(f"{path.relative_to(repo)}: removed Git isolation term")
        if "group_merged_result" in text:
            offenders.append(f"{path.relative_to(repo)}: replaced merge result term")
        if re.search(r"(?<!formal_)(?<!worker_)(?<!merged_)case_lib", text):
            offenders.append(f"{path.relative_to(repo)}: unqualified lib role")

    assert offenders == []


def test_core_contract_defines_all_three_lib_roles_and_fixed_roots() -> None:
    repo = Path(__file__).resolve().parents[5]
    core = (repo / "AGENTS.md").read_text(encoding="utf-8")
    for term in ("formal_case_lib", "group_worker_lib", "proving_merged_lib"):
        assert term in core
    assert "verification_runs/<run>/" in core
    assert "reports/<run>/" in core
    assert "reports/<run>/annotation-attempts/annotation-attemptN/" in core
    assert "每个 run 只能 spawn 一次 `annotation-subagent`" in core
    assert "append-annotation-agent" in core
    assert "annotation-summary-ready" in core
    assert "controller_state.json" in core
    assert "path-configuration.md" in core


def test_active_docs_and_scripts_do_not_use_replaced_coq_tooling_terms() -> None:
    repo = Path(__file__).resolve().parents[5]

    offenders: list[str] = []
    for path in _active_paths(repo):
        text = path.read_text(encoding="utf-8")
        for term in MIGRATION_BANNED_TERMS:
            if term in text:
                offenders.append(f"{path.relative_to(repo)}: {term}")

    assert offenders == []
