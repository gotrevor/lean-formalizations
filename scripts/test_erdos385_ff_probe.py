#!/usr/bin/env -S uv run --quiet --with pytest python3 -m pytest
"""Tests for erdos385-ff-probe.py, driven through the real CLI.

Expected values are hand-derived, not captured from the tool:
  * A bad f must vanish on all of F_q: if f(a) != 0 then g = f - f(a) is reducible with a linear
    factor, and deg(f - g) = 0 < 1 = mfd(g).
  * Bad f must also have f + c irreducible for every c in F_q^*.
  * Up to degree 3 only degree-0 shifts can witness (mfd(g) <= floor(n/2) = 1), so bad f are
    exactly the f with T^q - T | f and every f + c (c != 0) irreducible.
      q=2, n=2: T^2+T (T^2+T+1 irreducible).                        -> 1 bad
      q=2, n=3: T^3+T and T^3+T^2 (+1 gives the two irreducible cubics). -> 2 bad
      q=3, n=3: T^3-T only (Artin-Schreier: T^3-T+c irreducible for c != 0). -> 1 bad
"""
import pathlib
import re
import subprocess

PROBE = pathlib.Path(__file__).with_name("erdos385-ff-probe.py")


def run(q, n):
    out = subprocess.run([str(PROBE), str(q), str(n), "--list"], capture_output=True, text=True,
                         check=True).stdout
    rows = {int(m.group(1)): int(m.group(2)) for m in re.finditer(r"n=\s*(\d+) \|\s*(\d+)", out)}
    bad = re.findall(r"bad f = (.*)", out)
    return rows, bad


def test_q2_small_degrees():
    rows, bad = run(2, 3)
    assert rows[2] == 1 and rows[3] == 2
    assert "1T^2 + 1T^1" in bad
    assert {"1T^3 + 1T^1", "1T^3 + 1T^2"} <= set(bad)


def test_q3_artin_schreier():
    rows, bad = run(3, 3)
    assert rows[2] == 0 and rows[3] == 1
    assert bad == ["1T^3 + 2T^1"]


def _eval(term_str, q, a):
    total = 0
    for t in term_str.split(" + "):
        m = re.fullmatch(r"(\d+)T\^(\d+)", t)
        c, e = (int(m.group(1)), int(m.group(2))) if m else (int(t), 0)
        total += c * a**e
    return total % q


def test_every_bad_f_vanishes_on_Fq():
    for q, n in ((2, 8), (3, 7), (5, 5)):
        _, bad = run(q, n)
        assert bad, (q, n)
        for f in bad:
            assert all(_eval(f, q, a) == 0 for a in range(q)), (q, f)
