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


def profile(*args):
    out = subprocess.run([str(TOOL), "profile", *args], capture_output=True, text=True,
                         check=True).stdout.split("\n")[1:]
    rows = {}
    for line in out:
        if line.strip():
            n, k, b, g, *_ = line.split()
            rows[(int(n), int(k))] = (int(b), int(g))
    return rows


def test_profile_hand_counts():
    # B(n,k): bridges whose smaller side has k cells; G(n,k): polyominoes with at least one.
    # Trominoes: all 6 are paths of 3, two 1+2 bridges each -> B = 12, G = 6.
    # Tetrominoes, smaller side 1: I 2x2, L 8x2, S/Z 4x2, T 4x3 (centre has 3 leaves), O 0
    #   -> B = 4 + 16 + 8 + 12 = 40, G = 18.  Smaller side 2: the 14 halvable ones, one each.
    rows = profile("4")
    assert rows[(3, 1)] == (12, 6)
    assert rows[(4, 1)] == (40, 18)
    assert rows[(4, 2)] == (14, 14)


def test_profile_half_column_matches_halving():
    rows = profile("12")
    halving = table("12")
    for n in range(2, 13, 2):
        assert rows[(n, n // 2)][1] == halving[n][1]


def test_profile_parallel_matches_serial():
    assert profile("11") == profile("11", "--jobs", "3", "--split", "6")


def switching(*args):
    out = subprocess.run([str(TOOL), "switch", *args], capture_output=True, text=True,
                         check=True).stdout.split("\n")
    rows = {}
    for line in out:
        if line.startswith("S "):
            _, n, j, t, o, sl, ss, x = line.split()
            rows[(int(n), int(j))] = tuple(map(int, (t, o, sl, ss, x)))
    return rows


def test_switching_hand_counts_trominoes():
    # Marked triples (P, bridge, side S), |S| = j.  Move: delete a leaf c of the other side L (not
    # the bridge end), add a free cell d with exactly one S-neighbour and none in L - {c}.
    # Trominoes are paths a-b-c; each has 2 bridges, so 12 triples at j = 1 and 12 at j = 2.
    # j = 1, S = {a}: L = {b, c} has one eligible leaf (c).  Free cells beside a:
    #   I3: 3 cells, none touching b or c -> spots 3, out 3.
    #   L3 (corner b): the cell diagonal to b touches a and c, so it is not a spot, but it is a
    #   legal d (its L-neighbour is the leaf c being deleted) -> spots 2, out 3.
    #   O = 12*3 = 36; spots: I 4 triples * 3 + L 8 * 2 = 28; leaves of S: 0.
    #   leaves(L) * spots(S) summed: 28.
    # j = 2, S = {b, c}: the other side {a} has no eligible leaf, so out = 0.
    #   Leaves of S: c, one each -> 12.  Spots of {b, c} avoiding a: I3 5, L3 4 -> 4*5 + 8*4 = 52.
    rows = switching("3")
    assert rows[(3, 1)] == (12, 36, 0, 28, 28)
    assert rows[(3, 2)] == (12, 0, 12, 52, 0)


def test_switching_identity():
    # The move's inverse is the same move on the complement-marked triple, so the move count out
    # of size-j markings equals the count out of size-(n-1-j) markings.  Computed from disjoint
    # triples, so it can fail.
    rows = switching("11")
    for n in range(3, 12):
        for j in range(1, n - 1):
            assert rows[(n, j)][1] == rows[(n, n - 1 - j)][1], (n, j)
        assert rows[(n, n - 1)][1] == 0


def test_switching_triples_match_profile():
    # Triples marked with the smaller side are bridges B(n,k); the half column counts each bridge twice.
    sw, pr = switching("10"), profile("10")
    for (n, k), (b, _) in pr.items():
        assert sw[(n, k)][0] == (2 * b if 2 * k == n else b)
        assert sw[(n, n - k)][0] == sw[(n, k)][0]


def test_switching_parallel_matches_serial():
    assert switching("10") == switching("10", "--jobs", "3", "--split", "6")
