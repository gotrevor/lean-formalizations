#!/usr/bin/env -S uv run --quiet python3
"""Sweep: which shifts h survive the prime-as-modulus filter for u(c^n) + h?

Filter (phases 29/32/33): if u(c^n) + h = p_n is prime for all large n, where u(N) is read off
A^N for a 2x2 integer matrix A (det A = -Q), then v_c|GL2(F_p)| > n, so p_n = +-1 mod c^(~n/2).
Hence h survives only if u(c^n) + h = +-1 c-adically along EVERY large n.  u(c^n) mod c^K
cycles through finitely many c-adic limit points; h must be +-1 - (each of them).

Families: U_N(P,Q) (an ENTRY of A^N, A = [[P,-Q],[1,0]]) and V_N(P,Q) = tr A^N (a TRACE).
A survivor h is printed as the least-absolute residue mod c^K at two precisions; 'stable' means
the same small integer at both, i.e. an integer survivor (a genuinely open case, or a trivial
one like h = 0 or a parity kill).  Everything else is settled by the filter."""
import sys

def seq(P, Q, N, m, kind):
    a, b = (0, 1) if kind == "U" else (2, P)
    # fast doubling is overkill; use matrix power mod m
    def mul(X, Y):
        return [[(X[0][0]*Y[0][0] + X[0][1]*Y[1][0]) % m, (X[0][0]*Y[0][1] + X[0][1]*Y[1][1]) % m],
                [(X[1][0]*Y[0][0] + X[1][1]*Y[1][0]) % m, (X[1][0]*Y[0][1] + X[1][1]*Y[1][1]) % m]]
    R, A, e = [[1, 0], [0, 1]], [[P % m, (-Q) % m], [1, 0]], N
    while e:
        if e & 1: R = mul(R, A)
        A = mul(A, A); e >>= 1
    return R[1][0] if kind == "U" else (R[0][0] + R[1][1]) % m

def survivors(P, Q, c, K, kind):
    m = c**K
    vals = {seq(P, Q, c**n, m, kind) for n in range(3*K, 3*K + 12)}
    hs = None
    for u in vals:
        s = {(1 - u) % m, (-1 - u) % m}
        hs = s if hs is None else hs & s
    sym = lambda x: x - m if x > m // 2 else x
    return sorted(sym(h) for h in hs), len(vals)

def report(P, Q, c, kind):
    a, n1 = survivors(P, Q, c, 6, kind)
    b, _ = survivors(P, Q, c, 9, kind)
    stable = [h for h in a if h in b and abs(h) < 1000]
    if not a: verdict = "ALL h settled"
    elif stable: verdict = f"integer survivors {stable}"
    else: verdict = "survivors are non-integral c-adics -> ALL h settled"
    return f"{kind}({P:>2},{Q:>2}) c={c}: {n1} limit pt(s); {verdict}"

if __name__ == "__main__":
    pairs = [(1, -1), (3, 1), (1, 3), (3, -1), (5, 3), (2, -1), (4, 1), (1, 2), (3, 2)]
    for c in (2, 3, 5, 7):
        for kind in ("U", "V"):
            for P, Q in pairs:
                print(report(P, Q, c, kind))
        print()
