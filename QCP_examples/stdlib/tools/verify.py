#!/usr/bin/env python3
"""Regenerate libc VCs in .tmp, compare goals, and build their Rocq interfaces."""
from pathlib import Path
import argparse
import hashlib
import json
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
# family, C source, formal stem, pointer width, generator byte-order option
CASES = [
    ('musl', 'strstr_RL.c', 'strstr_rel', 64, 'big'),
    ('glibc', 'two-way_RL.c', 'two_way_rel', 32, 'big'),
    ('glibc', 'horspool_memmem_RL.c', 'horspool_memmem_rel', 32, 'big'),
    ('glibc', 'available.c', 'available', 32, 'big'),
    ('glibc', 'two-way_dynamic_RL.c', 'two_way_dynamic', 32, 'big'),
    ('glibc', 'horspool_dynamic_RL.c', 'horspool_dynamic', 32, 'big'),
    ('glibc', 'strstr_tw_bridge.c', 'strstr_tw_bridge', 32, 'big'),
    ('glibc', 'strstr_RL.c', 'strstr', 32, 'big'),
    ('glibc', 'strlen_word.c', 'strlen_word', 64, 'little'),
    ('glibc', 'memmove_bytes.c', 'memmove_bytes', 64, 'little'),
    ('glibc', 'memmove_loops.c', 'memmove_loops', 64, 'little'),
    ('glibc', 'memmove.c', 'memmove', 64, 'little'),
]

def default_symexec():
    if sys.platform == 'darwin':
        directory = 'macos-arm64' if platform.machine() == 'arm64' else 'macos-x86_64'
    elif sys.platform == 'win32':
        directory = 'windows'
    else:
        directory = 'linux'
    return ROOT / 'bin' / directory / ('symexec.exe' if sys.platform == 'win32' else 'symexec')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--symexec', type=Path, default=default_symexec())
    ap.add_argument('--dune', default='dune')
    ap.add_argument('--case', action='append', choices=[f'{c[0]}/{c[2]}' for c in CASES],
                    help='select a translation unit; repeat to select several')
    ap.add_argument('--generate-only', action='store_true')
    ap.add_argument('--build-only', action='store_true')
    args = ap.parse_args()
    if args.generate_only and args.build_only:
        ap.error('choose at most one of --generate-only / --build-only')
    out = ROOT / '.tmp/stdlib-verification'
    out.mkdir(parents=True, exist_ok=True)
    records = []
    selected = [c for c in CASES if not args.case or f'{c[0]}/{c[2]}' in args.case]
    if not args.build_only:
        for name in ('check_memmove_core_source.py', 'check_strstr_source.py'):
            subprocess.run([sys.executable, str(Path(__file__).with_name(name))], cwd=ROOT, check=True)
        for family, source, stem, arch, endian in selected:
            dest = out / family / stem
            dest.mkdir(parents=True, exist_ok=True)
            srcdir = ROOT / 'QCP_examples/stdlib' / family
            formal = ROOT / 'Rocq/examples/stdlib' / family
            # Strategy outputs are isolated too: a copied input prevents any generator
            # path derived from the source filename from touching checked-in files.
            inputs = dest / 'inputs'
            inputs.mkdir(exist_ok=True)
            for p in srcdir.iterdir():
                if p.is_file() and p.suffix in ('.c', '.h', '.strategies'):
                    shutil.copy2(p, inputs / p.name)
            command = [str(args.symexec.resolve()), '--input-file', str(inputs / source),
                '-I' + str(ROOT / 'QCP_examples/verification') + '/', '-I' + str(inputs) + '/',
                '--goal-file', str(dest / (stem + '_goal.v')),
                '--proof-auto-file', str(dest / (stem + '_proof_auto.v')),
                '--proof-manual-file', str(dest / (stem + '_proof_manual.v')),
                '--proof-manual-as-template', '--coq-logic-path', 'SimpleC.EE.stdlib.' + family,
                '-slp', str(inputs), 'SimpleC.EE.stdlib.' + family,
                '--no-exec-info', '--arch', str(arch), '--endian', endian]
            # Match the original checked prelude; the explicitly imported
            # StrlenLittleEndian module supplies the case's actual memory model.
            if stem == 'strlen_word':
                command += ['--CRules', 'naive_C_Rules']
            with (dest / 'symexec.log').open('w') as log:
                result = subprocess.run(command, cwd=dest, stdout=log, stderr=subprocess.STDOUT)
            fresh = dest / (stem + '_goal.v')
            expected = formal / fresh.name
            matches = fresh.exists() and fresh.read_bytes() == expected.read_bytes()
            records.append({'case': family + '/' + stem, 'returncode': result.returncode,
                'goal_matches_formal': matches,
                'source_sha256': hashlib.sha256((srcdir / source).read_bytes()).hexdigest()})
            (dest / 'result.json').write_text(json.dumps(records[-1], indent=2) + '\n')
            (out / 'generation.json').write_text(json.dumps(records, indent=2) + '\n')
            print(f'{family}/{stem}: exit={result.returncode}, goal_matches={matches}', flush=True)
            if result.returncode or not matches:
                print(f'Inspect {dest}', file=sys.stderr)
                return 1
    if not args.generate_only:
        targets = [f'Rocq/examples/stdlib/{family}/{stem}_goal_check.vo'
                   for family, _, stem, _, _ in selected]
        targets += ['Rocq/examples/stdlib/glibc/' + name + '.vo' for name in
                    ('check_memmove_core', 'check_strstr_composed', 'check_strlen_word')]
        with (out / 'dune.log').open('w') as log:
            result = subprocess.run([args.dune, 'build', '--root', str(ROOT),
                '--cache=disabled', '--display=short', *targets], cwd=ROOT,
                stdout=log, stderr=subprocess.STDOUT)
        (out / 'build.json').write_text(json.dumps({'returncode': result.returncode,
            'targets': targets}, indent=2) + '\n')
        print(f'Rocq build: exit={result.returncode}; log: {out / "dune.log"}', flush=True)
        if result.returncode:
            return result.returncode
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
