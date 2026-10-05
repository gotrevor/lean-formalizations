#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Check log tau(n!) ~ C n / log n with C = sum_k log(k+1)/(k(k+1)), and the counting bound
h(n!) >= log(n!) / log(tau(n!) + 1) against the exact values h(n!) for n = 3..11 posted on the
erdosproblems.com/18 thread (securehedgehog999, 2026-06-10): 2,3,4,5,5,6,7,7,7.
Used by docs/notes/practical-numbers.md and Practical/Erdos18.lean (practicalH_factorial_ge)."""
import math
from sympy import primerange

def log_tau_fact(n):
    s = 0.0
    for p in primerange(2, n + 1):
        v, q = 0, p
        while q <= n:
            v += n // q; q *= p
        s += math.log(v + 1)
    return s

C = sum(math.log(k + 1) / (k * (k + 1)) for k in range(1, 10**7))
C += math.log(10**7) / 10**7  # tail ~ int log x / x^2
print(f"C = {C:.5f}")
for n in (10**3, 10**4, 10**5, 10**6):
    lt = log_tau_fact(n)
    print(f"n={n:>8}  log tau(n!) * log n / n = {lt * math.log(n) / n:.4f}   "
          f"counting bound h(n!) >= {math.lgamma(n + 1) / lt:.2f}   (log n)^2 / C = {math.log(n)**2 / C:.2f}")
known = {3: 2, 4: 3, 5: 4, 6: 5, 7: 5, 8: 6, 9: 7, 10: 7, 11: 7}
for n, h in known.items():
    bound = math.ceil(math.lgamma(n + 1) / math.log(math.exp(log_tau_fact(n)) + 1) - 1e-9)
    assert bound <= h, (n, bound, h)
    print(f"n={n:2d}  exact h(n!)={h}  counting bound {bound}")
