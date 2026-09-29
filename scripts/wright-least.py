#!/usr/bin/env -S uv run --quiet --with sympy --with mpmath python3
# Least Wright constant: greedy q1=2, q_{k+1}=nextprime(2^{q_k}); omega = lim invtower(q_k, k).
from sympy import nextprime
from mpmath import mp, mpf, log
mp.dps = 60
q = [None, 2]
for _ in range(3):
    q.append(int(nextprime(2 ** q[-1])))
print("q:", q[1:4], "q4 =", q[4])
def invtower(x, n):
    x = mpf(x)
    for _ in range(n):
        x = log(x, 2)
    return x
for k in range(1, 5):
    print(k, invtower(q[k], k))
