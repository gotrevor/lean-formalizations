"""Tests for polyomino-halving, driving the real CLI through subprocess.

Expected values: A(n) from OEIS A001168 (external b-file); H(2) = 2 and H(4) = 14 counted by
hand (dominoes: both halve; tetrominoes: I(2), L(8), S/Z(4) are paths whose middle edge halves,
O(1) has no bridge and T(4) only splits 1+3, so 2 + 8 + 4 = 14 of 19).
Run: `./polyomino-halving test`.
"""
import subprocess
from pathlib import Path

TOOL = Path(__file__).parent / "polyomino-halving"
OEIS_A001168 = [1, 2, 6, 19, 63, 216, 760, 2725, 9910, 36446, 135268, 505861]


def table(*args):
    out = subprocess.run([str(TOOL), "run", *args], capture_output=True, text=True,
                         check=True).stdout.split("\n")[1:]
    rows = {}
    for line in out:
        if line.strip():
            n, a, h, e, _, _ = line.split()
            rows[int(n)] = (int(a), None if h == "-" else int(h), None if e == "-" else int(e))
    return rows


def test_counts_match_oeis():
    rows = table("12")
    for n in range(1, 13):
        assert rows[n][0] == OEIS_A001168[n - 1]


def test_parallel_counts_match_oeis_at_split_depth():
    # 2026-10-05: jobs other than 0 dropped size == SPLITDEPTH, so A(9) summed to 620.
    rows = table("12", "--jobs", "3", "--split", "5")
    for n in range(1, 13):
        assert rows[n][0] == OEIS_A001168[n - 1]


def test_hand_counted_halvings():
    rows = table("4")
    assert rows[2][1] == 2
    assert rows[4][1] == 14


def test_halving_edge_is_unique():
    # A second m+m bridge would sit inside one side and cut off fewer than m cells.
    rows = table("12")
    assert all(h == e for _, h, e in rows.values() if h is not None)


def test_injection_bound():
    # H(2m) ≤ 4 m² A(m)²: a halvable polyomino is fixed by its halves, a cell of each, a direction.
    rows = table("12")
    for n in range(2, 13, 2):
        m = n // 2
        assert rows[n][1] <= 4 * m * m * OEIS_A001168[m - 1] ** 2


def test_parallel_split_matches_serial():
    assert table("12") == table("12", "--jobs", "3", "--split", "5")
