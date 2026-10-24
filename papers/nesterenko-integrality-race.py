#!/usr/bin/env -S uv run --quiet python3
"""
Nesterenko integrality race for the odd-zeta extension.

Nesterenko's method needs the auxiliary series to have integer Taylor coefficients.
The extended Ramanujan system adds g_{0,3}(q) = sum sigma_{-3}(n) q^n, whose
coefficients have denominators dividing n^3.  A degree-d polynomial in the system,
expanded to order r, then needs clearing by

    D(r, d) = lcm of denominators of [q^i] g^j,  i <= r, j <= d

(E2, E4, E6, q have integer coefficients, and g_{1,3}, g_{2,3} have smaller
denominators, so g_{0,3}-powers carry the cost.)  The analytic gain at
q = e^{-2 pi} is r * 2 pi.

Prediction (napkin, p-adic count): log D(r, d) ~ 3 r (1 + log d).
  - d = 1 is the known-answer control: log D(r,1) ~ 3 psi(r) ~ 3 r (PNT).
  - If log D / r grows like 3 log d, the race is lost by a log factor for every v,
    since Nesterenko needs d -> infinity with r ~ d^n.
  - If log D / r saturates at a constant, it is a constant race against 2 pi.
"""

import math
import sys
from fractions import Fraction


def sigma_minus3(n: int) -> Fraction:
    return Fraction(sum(d**3 for d in range(1, n + 1) if n % d == 0), n**3)


def log_lcm_denoms(r: int, dmax: int) -> list[float]:
    g = [Fraction(0)] + [sigma_minus3(n) for n in range(1, r + 1)]
    power = [Fraction(1)] + [Fraction(0)] * r  # g^0
    lcm = 1
    out = []
    for _ in range(dmax):
        nxt = [Fraction(0)] * (r + 1)
        for i, a in enumerate(power):
            if a:
                for k in range(1, r + 1 - i):
                    nxt[i + k] += a * g[k]
        power = nxt
        for c in power:
            lcm = math.lcm(lcm, c.denominator)
        out.append(math.log(lcm))
    return out


def psi(r: int) -> float:
    return sum(math.log(p) * int(math.log(r) / math.log(p) + 1e-9)
               for p in range(2, r + 1) if all(p % q for q in range(2, int(p**0.5) + 1)))


def main() -> int:
    r = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    dmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    logs = log_lcm_denoms(r, dmax)
    print(f"r = {r},  gain 2*pi = {2 * math.pi:.3f} per order,  3*psi(r)/r = {3 * psi(r) / r:.3f}")
    print(f"{'d':>3} {'logD/r':>8} {'pred 3(1+log d)':>16} {'logD/r - 3 log d':>17}")
    for d, L in enumerate(logs, 1):
        print(f"{d:>3} {L / r:8.3f} {3 * (1 + math.log(d)):16.3f} {L / r - 3 * math.log(d):17.3f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
