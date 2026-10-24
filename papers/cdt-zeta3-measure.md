# Can holonomy bounds improve ζ(3)'s irrationality measure?  A measure-twice probe

**2026-10-24.**  Probe: `papers/cdt-zeta3-measure.py`.  The question comes from Dimitrov's LNT slides, which note that Apéry's H extends to the slit plane ℂ∖[(√2+1)⁴, ∞).  That domain's conformal radius is 4× its largest disc.  Can this beat Rhin–Viola's μ(ζ(3)) ≤ 5.513891?

## Instrument

CDT ICM (arXiv:2510.04156) Proposition 2.4: m ≤ ∬ / (L − τ − (1−γ)(2/μ − (1−γ)/μ²) log(1/ρ)), solved for the μ at which the right side equals m.  Apéry data:

- **Module:** {1, H, H′}, so m = 3.  Only the constant 1 is free of ζ(3), so γ = 1/3.
- **Denominator rate:** τ = 8/3, best-first.
- **Template:** univalent slit map φ(z) = 4βz/(1+z)², so ∬ = L = log 4β = 4.912.
- **Radius ρ:** set where A and B themselves blow up, at α = (√2−1)⁴.  That gives log(1/ρ) = 8.437.

**Control:** the classical formula 1 + (growth + den)/(decay − den) reproduces Apéry's 13.4178.

## Result

| | μ bound |
|---|---|
| Apéry classical (control) | 13.418 |
| **CDT Prop 2.4 as published, slit plane** | **18.17**, worse than Apéry, as CDT warn |
| Same with the coefficient 2 → 1 (hypothetical sharpening) | 8.53 |
| Rhin–Viola (target) | 5.514 |

Fuel L the slit plane would need, with the module and ρ held fixed:

| Coefficient | to match Apéry | to beat Rhin–Viola |
|---|---|---|
| 2 (published) | 5.226 | **6.875** |
| 1 (hypothetical) | 4.598 | **5.345** |

The slit plane has 4.912 in both rows.

## Reading

- **The penalty that dominates is log(1/ρ) = 8.44.**  It is the cost of A and B themselves blowing up at α, the same growth that costs Apéry's classical bound.  The slit plane's ×4 raises L by log 4 but leaves that penalty alone.
- **As published, beating Rhin–Viola needs about 2.0 more fuel (+40%).**  The sharpened coefficient lowers that to 0.43.  The sharpening is exactly CDT's stated open problem ("an ε-improvement over the usual irrationality measure in every single case").
- **Two nodes, both needed unless templates are generous.**
  1. A non-univalent template for the Apéry module with fuel ≥ 5.35, against a correspondingly larger ∬.  This is Dimitrov's "finite covering of X₁(6)+ of higher genus".
  2. The coefficient-1 sharpening of Prop 2.4, which is a proof-technique result in the Bost slopes framework.
- **Next cheap measurement:** evaluate ∬, L and ρ for explicit non-univalent templates (CDT App. A style h∘ψ, or lifts through covers of X₁(6)+), feed them to the instrument, and see whether any template moves μ at all at coefficient 2.  If none reaches about 5.2, the published-coefficient path cannot even match Apéry, and the lead rests entirely on node 2.

## Caveats

- **ρ is set by φ(z) = α on the positive real axis.**  The true ρ uses max|φ| on |z| = ρ, attained at z = −ρ.  The difference is a factor (1−ρ)²/(1+ρ)² ≈ 1 − 9·10⁻⁴, which is negligible.
- **The coefficient-1 row is a scale, not a theorem.**
- **Odds** the lead yields μ(ζ(3)) < 5.513: about 5%.
