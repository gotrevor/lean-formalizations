/-
# Growth constants of quadratic iterations are transcendental (Dubickas 2022, Theorem 1)

A. Dubickas, *Transcendency of some constants related to integer sequences of polynomial
iterations*, Ramanujan J. **57** (2022), 569–581, doi:10.1007/s11139-021-00428-5.
Local-only full text (gitignored): `papers/dubickas-2022-transcendency-polynomial-iterations.{pdf,txt}`.

For an integer sequence with `x_{n+1} = P(x_n)`, `x_n → ∞`, the limit `α = lim x_n^(1/dⁿ)`
exists (Wagner–Ziegler).  **Theorem 1**: for the five recurrences below, `α` is transcendental:

| constant | recurrence | `x₀` | OEIS sequence | OEIS constant (`√α`) |
|---|---|---|---|---|
| κ = 1.502837… | `x² + 1` | 1 | A003095 | A076949 |
| ζ = 1.678458… | `x² − 1` | 2 | A003096 | A077124 |
| γ = 1.597910… | `x² − x + 1` (Sylvester) | 2 | A000058 | A076393 (Vardi) |
| η | `x² + x + 1` | 1 | A002065 | |
| τ | `x² + 2x + 1` | 1 | A004019 | |

Theorem 1 is Theorem 2 for monic quadratics: `α` is transcendental unless
`a₁² − 2a₁ − 4a₂ ∈ {0, 8}` ((17), (18)); none of the five hits either value.

Inputs (frozen hypotheses, `Literature/Pisot.lean`): `Dubickas2022` (his Lemma 6, from
Corvaja–Zannier) and `Dubickas2022PisotGap` (his Lemma 8, from Smyth/Mignotte/Baker).

## Route (Dubickas §1, §4, §5 with `d = 2`, `a₀ = 1`)

1. **Formula (6)** (§1, elementary): with `y_n = x_n + a₁/2`, `y_{n+1} = y_n² + O(1)`;
   `α := lim x_n^(2^-n)` exists, `α > 1`, and `x_n = α^(2ⁿ) − a₁/2 + O(α^(−2ⁿ))`.
2. **Lemma 9**: if `α` is algebraic, `Dubickas2022` (with `q = 2`, `s_n = 2ⁿ`) makes some
   `β = α^(2^m)` Pisot; `Dubickas2022PisotGap` then forces `β` an integer or a quadratic Pisot unit.
3. **Lemma 7** (Chebyshev, elementary): `z_n = α₁^(2ⁿ) + α₂^(2ⁿ)` satisfies `z_{n+1} = z_n² − 2`.
4. **Lemma 10** (polynomial identity from agreement at infinitely many points) and **§5**: integer
   case ⇒ `y_{n+1} = y_n²` for all `n` ⇒ (17); Pisot-unit case ⇒ `y_{n+1} = y_n² − 2` ⇒ (18).

Only `d = 2` is needed for Theorem 1; general-degree Theorem 2 is a stretch, not a target.
-/
import LeanFormalizations.Literature.Pisot

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature

/-- **Dubickas (2022), Theorem 2 for monic quadratics** (conditions (17), (18)).  An integer
sequence with `x_{n+1} = x_n² + a₁ x_n + a₂` tending to `∞` has a growth constant
`α = lim x_n^(1/2ⁿ)`, and `α` is transcendental unless `a₁² − 2a₁ − 4a₂ ∈ {0, 8}`. -/
theorem transcendental_growth_of_monic_quadratic (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) (a₁ a₂ : ℤ) (x : ℕ → ℤ)
    (hx : ∀ n, x (n + 1) = x n ^ 2 + a₁ * x n + a₂) (hinf : Tendsto x atTop atTop)
    (h17 : a₁ ^ 2 - 2 * a₁ - 4 * a₂ ≠ 0) (h18 : a₁ ^ 2 - 2 * a₁ - 4 * a₂ ≠ 8) :
    ∃ α : ℝ, Tendsto (fun n ↦ (x n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) atTop (𝓝 α) ∧
      Transcendental ℚ α := by
  sorry

/-- A003095 shifted: `1, 2, 5, 26, 677, …` (`x_{n+1} = x_n² + 1`, `x₀ = 1`). -/
def kappaSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 => kappaSeq n ^ 2 + 1

/-- A003096: `2, 3, 8, 63, 3968, …` (`x_{n+1} = x_n² − 1`, `x₀ = 2`). -/
def zetaSeq : ℕ → ℤ
  | 0 => 2
  | n + 1 => zetaSeq n ^ 2 - 1

/-- A000058, Sylvester's sequence: `2, 3, 7, 43, 1807, …` (`x_{n+1} = x_n² − x_n + 1`). -/
def sylvester : ℕ → ℤ
  | 0 => 2
  | n + 1 => sylvester n ^ 2 - sylvester n + 1

/-- A002065 shifted: `1, 3, 13, 183, …` (`x_{n+1} = x_n² + x_n + 1`, `x₀ = 1`). -/
def etaSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 => etaSeq n ^ 2 + etaSeq n + 1

/-- A004019 shifted: `1, 4, 25, 676, …` (`x_{n+1} = x_n² + 2x_n + 1`, `x₀ = 1`). -/
def tauSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 => tauSeq n ^ 2 + 2 * tauSeq n + 1

/-- The growth constant `lim x_n^(1/2ⁿ)` has limit `α` and `α` is transcendental. -/
def HasTranscendentalGrowth (x : ℕ → ℤ) : Prop :=
  ∃ α : ℝ, Tendsto (fun n ↦ (x n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) atTop (𝓝 α) ∧ Transcendental ℚ α

/-- **Dubickas (2022), Theorem 1: κ, ζ, γ, η, τ are all transcendental.** -/
theorem theorem1 (hD : Dubickas2022) (hG : Dubickas2022PisotGap) :
    HasTranscendentalGrowth kappaSeq ∧ HasTranscendentalGrowth zetaSeq ∧
      HasTranscendentalGrowth sylvester ∧ HasTranscendentalGrowth etaSeq ∧
      HasTranscendentalGrowth tauSeq := by
  sorry

/-! ## The OEIS-normalised constants

OEIS indexes each constant as `c` with `a(n) ≈ c^(2^(n+1))`, i.e. `c = lim x_n^(1/2^(n+1)) = √α`
(A076949 for A003095, A077124 for A003096, A076393 = Vardi's constant for A000058).  A square
root of a transcendental number is transcendental. -/

/-- The half-rate growth constant `lim x_n^(1/2^(n+1))` exists and is transcendental. -/
def HasTranscendentalHalfGrowth (x : ℕ → ℤ) : Prop :=
  ∃ c : ℝ, Tendsto (fun n ↦ (x n : ℝ) ^ ((1 : ℝ) / 2 ^ (n + 1))) atTop (𝓝 c) ∧
    Transcendental ℚ c

/-- **OEIS A076949, A077124, A076393 (Vardi's constant) are transcendental.** -/
theorem oeis_constants (hD : Dubickas2022) (hG : Dubickas2022PisotGap) :
    HasTranscendentalHalfGrowth kappaSeq ∧ HasTranscendentalHalfGrowth zetaSeq ∧
      HasTranscendentalHalfGrowth sylvester := by
  sorry

end LeanFormalizations.Transcendence.Dubickas
