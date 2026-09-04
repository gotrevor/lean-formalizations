#!/usr/bin/env -S uv run --quiet python3
"""Exact probe of two monomial families from arXiv:2510.20648.

The paper constructs rational linear forms

    integral_Delta F(x,y) / (1-x^2-y^2)^(t+1) dxdy = a + b*G.

This script implements its simple-pole formulas and even-pole reduction for
the monomial families x^(2n)y^(2n) and x^(4n)y^(4n), t=2n.  It uses only
exact Fraction arithmetic; the decimal value of G is used only to display
the size of the minimally cleared linear form.
"""

from decimal import Decimal, getcontext
from fractions import Fraction as Q
from math import comb, gcd


getcontext().prec = 80
CATALAN = Decimal(
    "0.91596559417721901505460351493238411077414937428167213426649811962176301977625477"
)


def poly_mul(left, right):
    result = [Q(0)] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return result


def poly_integral_01(poly):
    return sum(coefficient / Q(i + 1) for i, coefficient in enumerate(poly))


def poly_add(left, right, scale=Q(1)):
    result = [Q(0)] * max(len(left), len(right))
    for i, x in enumerate(left):
        result[i] += x
    for i, x in enumerate(right):
        result[i] += scale * x
    return result


def gaussian_poly_power(k, sign):
    """Return coefficients of (1-y + sign*i*y)^k as pairs (real, imag)."""
    base = [(Q(1), Q(0)), (Q(-1), Q(sign))]
    result = [(Q(1), Q(0))]
    for _ in range(k):
        product = [(Q(0), Q(0))] * (len(result) + 1)
        for i, (ar, ai) in enumerate(result):
            for j, (br, bi) in enumerate(base):
                cr, ci = product[i + j]
                product[i + j] = (cr + ar * br - ai * bi, ci + ar * bi + ai * br)
        result = product
    return result


def gaussian_poly_mul(left, right):
    result = [(Q(0), Q(0))] * (len(left) + len(right) - 1)
    for i, (ar, ai) in enumerate(left):
        for j, (br, bi) in enumerate(right):
            cr, ci = result[i + j]
            result[i + j] = (cr + ar * br - ai * bi, ci + ar * bi + ai * br)
    return result


def off_diagonal_integral(k, ell):
    """Lemma 8.2.1 integral for z^k w^ell + z^ell w^k."""
    first = gaussian_poly_mul(gaussian_poly_power(k, 1), gaussian_poly_power(ell, -1))
    second = gaussian_poly_mul(gaussian_poly_power(ell, 1), gaussian_poly_power(k, -1))
    numerator = [-(x[1] - y[1]) for x, y in zip(first, second)]

    # Divide exactly by 2y(1-y), then multiply by 2y-1.
    divided_by_y = numerator[1:]
    quotient = []
    accumulator = Q(0)
    for coefficient in divided_by_y[:-1]:
        accumulator += coefficient
        quotient.append(accumulator)
    assert divided_by_y[-1] == -accumulator
    integrand = poly_mul(quotient, [Q(-1, 2), Q(1)])
    return poly_integral_01(integrand) / Q(k - ell)


def diagonal_integral(k):
    """Lemma 8.2.3 integral for (z^k w^k - 1)/(1-zw)."""
    quadratic = [Q(1), Q(-2), Q(2)]
    power = [Q(1)]
    total = [Q(0)]
    for j in range(k):
        total = poly_add(total, power, Q(1, j + 1))
        power = poly_mul(power, quadratic)
    return -poly_integral_01(total) / 2


def lcm(left, right):
    return left // gcd(left, right) * right


def cleared_value(a, b):
    denominator = lcm(a.denominator, b.denominator)
    value = Decimal(a.numerator) / Decimal(a.denominator)
    value += Decimal(b.numerator) / Decimal(b.denominator) * CATALAN
    return denominator, value * Decimal(denominator)


def simple_pole_monomial(n):
    """Coefficients for integral x^(2n)y^(2n)/(1-x^2-y^2)."""
    b = Q(comb(2 * n, n), 2 ** (4 * n))
    a = b * diagonal_integral(2 * n)
    for r in range(n):
        k, ell = 4 * n - 2 * r, 2 * r
        coefficient = Q((-1) ** (n + r) * comb(2 * n, r), 2 ** (4 * n))
        a += coefficient * off_diagonal_integral(k, ell)
    denominator, value = cleared_value(a, b)
    return a, b, denominator, value


def high_pole_monomial(n):
    """Coefficients for integral x^(4n)y^(4n)/(1-x^2-y^2)^(2n+1)."""
    a, b, _, _ = simple_pole_monomial(n)
    exponent = 2 * n
    for pole_index in range(2, 2 * n + 1, 2):
        exponent += 2
        residual_degree = exponent - pole_index
        scale = Q((exponent - 1) ** 2, 4 * pole_index * (pole_index - 1))
        boundary = -Q(
            1,
            4
            * pole_index
            * (pole_index - 1)
            * 2 ** (pole_index - 1)
            * comb(2 * residual_degree, residual_degree),
        )
        a, b = boundary + scale * a, scale * b
    denominator, value = cleared_value(a, b)
    return a, b, denominator, value


def main():
    print("simple-pole family F=x^(2n)y^(2n)")
    for n in range(1, 11):
        _, _, denominator, value = simple_pole_monomial(n)
        per_degree = float(abs(value)) ** (1 / (4 * n))
        print(
            n,
            f"deg={4*n:2d}",
            f"Ddigits={len(str(denominator))}",
            f"cleared={float(value):.8g}",
            f"per-degree={per_degree:.6f}",
        )

    print("high-pole family F=x^(4n)y^(4n), t=2n")
    for n in range(1, 31):
        a, b, denominator, value = high_pole_monomial(n)
        per_n = float(abs(value)) ** (1 / n)
        print(
            n,
            f"deg={8*n:3d}",
            f"Ddigits={len(str(denominator))}",
            f"cleared={float(value):.8g}",
            f"per-n={per_n:.6f}",
            f"a={a}",
            f"b={b}",
        )


if __name__ == "__main__":
    main()
