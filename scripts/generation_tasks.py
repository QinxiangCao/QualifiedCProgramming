"""Generation tasks, input discovery and command construction for QCP examples."""

from collections import OrderedDict
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import TypeAlias

from binaries import find_binary

ROOT = Path(__file__).resolve().parents[1]
SOURCES = Path("QCP_examples")
BUILTIN_SOURCES = SOURCES / "verification/builtin"
BUILTIN_PROOFS = Path("Rocq/Verification/BuiltIn")

EXCLUDED = {
    "Applications_human/typeinfer_rc/post_transport.c",  # Diagnostic fixture, not a verification case.
    "Applications_human/minisat/main_qcp.c",  # Native command-line frontend.
    # Generated through the split wrappers; keep aggregate proof modules intact.
    "Applications_human/CDCL/CDCL_qcp.c",
    # Codeforces
    "LLM_bench/Codeforces/examples_shard00/P025_1207B_square_filling.c",
    "LLM_bench/Codeforces/examples_shard00/P028_1941D_rudolf_and_the_ball_game.c",
    "LLM_bench/Codeforces/examples_shard00/P060_1725M_moving_both_hands.c",
    "LLM_bench/Codeforces/examples_shard00/P065_2001D_longest_max_min_subsequence.c",
    "LLM_bench/Codeforces/examples_shard00/P066_1280C_jeremy_bearimy.c",
    "LLM_bench/Codeforces/examples_shard00/P069_2014F_sheriffs_defense.c",
    "LLM_bench/Codeforces/examples_shard00/P072_276E_little_girl_and_problem_on_trees.c",
    "LLM_bench/Codeforces/examples_shard00/P074_507E_breaking_good.c",
    "LLM_bench/Codeforces/examples_shard00/P075_796D_police_stations.c",
    "LLM_bench/Codeforces/examples_shard00/P076_1039C_network_safety.c",
    "LLM_bench/Codeforces/examples_shard00/P077_1704E_count_seconds.c",
    "LLM_bench/Codeforces/examples_shard00/P079_505D_mr_kitayutas_technology.c",
    "LLM_bench/Codeforces/examples_shard00/P083_547C_mike_and_foam.c",
    "LLM_bench/Codeforces/examples_shard00/P084_1527D_mex_tree.c",
    "LLM_bench/Codeforces/examples_shard00/P085_375D_tree_and_queries.c",
    "LLM_bench/Codeforces/examples_shard00/P086_83C_track.c",
    "LLM_bench/Codeforces/examples_shard00/P088_1725E_electrical_efficiency.c",
    "LLM_bench/Codeforces/examples_shard00/P090_317C_balance.c",
    "LLM_bench/Codeforces/examples_shard00/P092_1495D_bfs_trees.c",
    "LLM_bench/Codeforces/examples_shard00/P093_541D_super_j.c",
    "LLM_bench/Codeforces/examples_shard00/P094_500F_new_year_shopping.c",
    "LLM_bench/Codeforces/examples_shard00/P095_827D_best_edge_weight.c",
    "LLM_bench/Codeforces/examples_shard00/P097_1612F_armor_and_weapons.c",
    "LLM_bench/Codeforces/examples_shard00/P099_1535F_string_distance.c",
    "LLM_bench/Codeforces/examples_shard00/P100_896E_welcome_home_chtholly.c",
    "LLM_bench/Codeforces/examples_shard03/P001_110A_nearly_lucky_number.c",
    "LLM_bench/Codeforces/examples_shard03/P002_1398B_substring_removal_game.c",
    "LLM_bench/Codeforces/examples_shard03/P003_1656A_good_pairs.c",
    "LLM_bench/Codeforces/examples_shard03/P004_1684A_digit_minimization.c",
    "LLM_bench/Codeforces/examples_shard03/P005_1900A_cover_in_water.c",
    "LLM_bench/Codeforces/examples_shard03/P006_1935A_entertainment_in_mac.c",
    "LLM_bench/Codeforces/examples_shard03/P007_1808A_lucky_numbers.c",
    "LLM_bench/Codeforces/examples_shard03/P008_1927B_following_the_string.c",
    "LLM_bench/Codeforces/examples_shard03/P009_2042B_game_with_colored_marbles.c",
    "LLM_bench/Codeforces/examples_shard03/P010_215A_bicycle_chain.c",
    "LLM_bench/Data_structures/union_find/union_find.c",  # Implementation sketch.
    "QCP_demos_LLM/simple_arith/test.c",  # Local scratch example.
}

# Per-example options
EXTRA_ARGS = {
    "LLM_bench/Algorithms/convex_hull_float/convex_hull_float.c": ["--float-finite-vc"],
}

# Public source roots, their Rocq output directories and logical namespaces.
LIBRARIES = OrderedDict(
    [
        ("verification", ("Rocq/Verification", "SimpleC.Verification")),
        ("stdlib", ("Rocq/stdlib", "SimpleC.StdLib")),
    ]
)

# Array/data-structure headers still in demos until the next extraction phase.
EXTRA_INCLUDE_DIRS = OrderedDict(
    [
        ("LLM_bench", ["QCP_demos_LLM"]),
        ("Applications_human/CDCL", ["QCP_demos_LLM"]),
    ]
)


@dataclass(frozen=True)
class ProgramVC:
    source: Path


@dataclass(frozen=True)
class StrategyVC:
    source: Path


@dataclass(frozen=True)
class BuiltinExport:
    pass


GenerationTask: TypeAlias = ProgramVC | StrategyVC | BuiltinExport
TASK_TYPES = {"builtin": BuiltinExport, "strategy": StrategyVC, "program": ProgramVC}


@dataclass(frozen=True)
class GeneratedFile:
    """A source-tree destination and its path inside a candidate output directory."""

    source: Path
    candidate: Path
    manual: bool = False
    optional: bool = False


def outputs(task: GenerationTask, builtin_names=()) -> list[GeneratedFile]:
    match task:
        case BuiltinExport():
            files = []
            for name in builtin_names:
                files.append(GeneratedFile(BUILTIN_SOURCES / f"{name}.strategies",
                                           Path("strategies") / f"{name}.strategies"))
                for suffix in ("goal", "proof", "goal_check"):
                    filename = f"{name}_strategy_{suffix}.v"
                    manual = suffix == "proof"
                    files.append(GeneratedFile(BUILTIN_PROOFS / filename,
                        Path("proofs") / (filename + (".in" if manual else "")), manual))
            return files
        case ProgramVC(source):
            suffixes = ("goal", "proof_auto", "goal_check", "def", "proof_manual")
            manual_suffix = "proof_manual"
        case StrategyVC(source):
            suffixes = ("strategy_goal", "strategy_goal_check", "strategy_proof")
            manual_suffix = "strategy_proof"
        case _:
            raise TypeError(f"Unknown generation task: {task!r}")
    return [GeneratedFile(
        output_directory(source.parent) / f"{source.stem}_{suffix}.v",
        Path(f"{source.stem}_{suffix}.v" + (".in" if suffix == manual_suffix else "")),
        manual=suffix == manual_suffix, optional=suffix == "def",
    ) for suffix in suffixes]


@cache
def strategy_directories() -> frozenset[Path]:
    """Only scan when constructing a tool command, once per CLI process."""
    return frozenset(
        path.parent.relative_to(ROOT) for path in (ROOT / SOURCES).rglob("*.strategies")
        if (ROOT / BUILTIN_SOURCES) not in path.parents
    )


def task_name(task: GenerationTask) -> str:
    match task:
        case ProgramVC(source) | StrategyVC(source):
            return source.relative_to(SOURCES).as_posix()
        case BuiltinExport():
            return "builtin strategies"
    raise TypeError(f"Unknown generation task: {task!r}")


def logic_path(directory: Path) -> str:
    relative = directory.relative_to(SOURCES)
    if relative.parts[:2] == ("verification", "builtin"):
        return ".".join(("SimpleC.Verification.BuiltIn", *relative.parts[2:]))
    if relative.parts and relative.parts[0] in LIBRARIES:
        return ".".join((LIBRARIES[relative.parts[0]][1], *relative.parts[1:]))
    return ".".join(("SimpleC", "EE", *relative.parts))


def search_args(source: Path) -> list[str]:
    # Nearest directory first, then ancestors and the shared example library.
    directories = list(source.parents)[: len(source.relative_to(SOURCES).parts) - 1]
    relative = source.relative_to(SOURCES)
    directories += [SOURCES / name for name in LIBRARIES]
    for prefix, names in EXTRA_INCLUDE_DIRS.items():
        if Path(prefix) in relative.parents:
            directories += [SOURCES / name for name in names]
    directories.append(SOURCES)
    args = []
    for directory in OrderedDict.fromkeys(directories):
        args += [
            "-I" + directory.as_posix() + "/",
            "-slp",
            directory.as_posix() + "/",
            logic_path(directory),
        ]
    # -slp is not recursive: also map sibling strategy libraries (e.g. GMP).
    for directory in sorted(strategy_directories() - set(directories)):
        args += ["-slp", directory.as_posix() + "/", logic_path(directory)]
    return args


def output_directory(directory: Path) -> Path:
    relative = directory.relative_to(SOURCES)
    if relative.parts[:2] == ("verification", "builtin"):
        return Path("Rocq/Verification/BuiltIn").joinpath(*relative.parts[2:])
    if relative.parts and relative.parts[0] in LIBRARIES:
        return Path(LIBRARIES[relative.parts[0]][0]).joinpath(*relative.parts[1:])
    return Path("Rocq/examples") / relative


def command(task: GenerationTask, *, output: Path | None = None,
            builtin_export: Path | None = None,
            manual_templates: bool = False) -> tuple[list[str], Path]:
    template_args = ["--proof-manual-as-template"] if manual_templates else []
    match task:
        case BuiltinExport():
            output = output if output is not None else BUILTIN_PROOFS
            export = builtin_export if builtin_export is not None else BUILTIN_SOURCES
            return [
                str(find_binary("StrategyCheck")),
                "--builtin-strategy-export-dir", export.as_posix(),
                "--builtin-strategy-proof-dir", output.as_posix(),
                "--coq-logic-path", "SimpleC.Verification.BuiltIn",
                "--no-exec-info",
            ] + template_args, output
        case ProgramVC(source):
            executable = find_binary("symexec")
        case StrategyVC(source):
            executable = find_binary("StrategyCheck")
        case _:
            raise TypeError(f"Unknown generation task: {task!r}")
    relative = source.relative_to(SOURCES)
    output = output if output is not None else output_directory(source.parent)
    args = [
        str(executable),
        "--input-file",
        source.as_posix(),
        "--coq-output-dir",
        output.as_posix() + "/",
        "--coq-logic-path",
        logic_path(source.parent),
        "--no-exec-info",
    ]
    args += search_args(source)
    args += EXTRA_ARGS.get(relative.as_posix(), [])
    return args + template_args, output


def is_builtin_snapshot(path: Path) -> bool:
    with path.open(encoding="utf-8") as source:
        return source.readline().startswith("// qcp-builtin: builtin/")


def discover_programs(root: Path = ROOT, directory: Path | None = None) -> list[ProgramVC]:
    """Discover all programs, or only direct children of a SOURCES-relative directory."""
    paths = ((root / SOURCES).rglob("*.c") if directory is None
             else (root / SOURCES / directory).glob("*.c"))
    return [
        ProgramVC(path.relative_to(root))
        for path in sorted(paths)
        if path.relative_to(root / SOURCES).as_posix() not in EXCLUDED
    ]


def discover_strategies(root: Path = ROOT, directory: Path | None = None) -> list[StrategyVC]:
    # Builtins come from the tool, not from their exported snapshots.
    paths = ((root / SOURCES).rglob("*.strategies") if directory is None
             else (root / SOURCES / directory).glob("*.strategies"))
    return [
        StrategyVC(path.relative_to(root))
        for path in sorted(paths)
        if path.relative_to(root / SOURCES).as_posix() not in EXCLUDED
        and not is_builtin_snapshot(path)
    ]


def discover_vcs(root: Path = ROOT, directory: Path | None = None) -> list[ProgramVC | StrategyVC]:
    return [*discover_strategies(root, directory), *discover_programs(root, directory)]


def discover(root: Path = ROOT) -> list[GenerationTask]:
    return [BuiltinExport(), *discover_vcs(root)]


def temporary_outputs(task: GenerationTask, output: Path) -> list[Path]:
    """List only this task's generator staging files, never final outputs."""
    names = (source.stem for source in (ROOT / BUILTIN_SOURCES).glob("*.strategies")
             if is_builtin_snapshot(source)) if isinstance(task, BuiltinExport) else ()
    return [output / (file.source.name + ".sacgen.tmp")
            for file in outputs(task, names) if file.source.suffix == ".v"]
