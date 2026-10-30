"""Compile independent MiniSat objects and check DIMACS answers and models."""
import itertools
from pathlib import Path
import random
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'QCP_examples/Applications_human/minisat'


def formulas():
    yield 1, []
    yield 1, [[]]
    yield 1, [[1], [-1]]
    yield 2, [[1, 2], [-1, 2], [1, -2], [-1, -2]]
    rng = random.Random(1741)
    for _ in range(100):
        size = rng.randint(2, 8)
        clauses = [[rng.choice((-1, 1)) * v for v in rng.sample(range(1, size + 1), rng.randint(1, min(4, size)))]
                   for _ in range(rng.randint(1, 40))]
        yield size, clauses


def satisfies(clauses, values):
    return all(any(values[abs(lit) - 1] == (lit > 0) for lit in clause)
               for clause in clauses)


def check_solver(binary):
    for size, clauses in formulas():
        # Ensure every declared variable exists even when all clauses simplify.
        problem = clauses + [[v, -v] for v in range(1, size + 1)]
        dimacs = f'p cnf {size} {len(problem)}\n' + ''.join(
            ' '.join(map(str, clause + [0])) + '\n' for clause in problem)
        expected = any(satisfies(clauses, values)
                       for values in itertools.product((False, True), repeat=size))
        with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf') as source:
            source.write(dimacs)
            source.flush()
            result = subprocess.run([str(binary), source.name], text=True,
                                    capture_output=True, timeout=10)
        assert result.returncode in (0, 20), result.stderr
        verdict = re.findall(r'^(?:UN)?SATISFIABLE$', result.stdout, re.M)
        assert verdict == ['SATISFIABLE' if expected else 'UNSATISFIABLE'], dimacs + result.stdout
        if expected:
            assignments = {int(v): bool(int(value)) for v, value in
                           re.findall(r'x(\d+)=(\d)', result.stdout)}
            assert set(assignments) == set(range(size)), result.stdout
            assert satisfies(clauses, assignments), dimacs + result.stdout


def test_minisat_native_translation_units():
    with tempfile.TemporaryDirectory(prefix='minisat-native-') as folder:
        subprocess.run(['make', '-C', str(SOURCE), f'BUILD_DIR={folder}', '-j4'],
                       check=True, capture_output=True, text=True)
        assert len(list(Path(folder).glob('*.o'))) == 6
        check_solver(Path(folder) / 'minisat')


if __name__ == '__main__':
    test_minisat_native_translation_units()
    print('MiniSat: separate compilation and 104 formula/model checks passed')
