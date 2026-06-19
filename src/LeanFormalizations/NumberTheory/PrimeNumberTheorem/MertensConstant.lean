/-
# Toward the sharp Mertens constant `C₃ = −γ`

`Mertens.lean` proves `∏_{p≤N}(1−1/p)·log N → e^{C₃}` (`mertens_third_tendsto_exp`) with
`C₃ = mertensThirdConst`, and reduces the classical `e^{−γ}` headline to the single deep equation
`mertensThirdConst = −γ` (`mertens_third_classical`).  This file collects the first **provable**
scaffolding bricks toward that equation, via the real prime-zeta function and mathlib's complex ζ
Euler product.

**The classical route** (still multi-lap): for `s > 1`,
`log ζ(s) = ∑_p ∑_{k≥1} p^{−ks}/k = P(s) + ∑_{k≥2} P(ks)/k` where `P(s) = ∑_p p^{−s}` is the prime
zeta; as `s → 1⁺`, `ζ(s) − 1/(s−1) → γ` (`tendsto_riemannZeta_sub_one_div`) gives the `γ`, and an
Abel/Tauberian transfer connects `P(s)` to the partial sums `∑_{p≤x} 1/p = log log x + M + o(1)`
(`mertens_second_tendsto`), yielding `M = γ + ∑'_p (log(1−1/p)+1/p)`, i.e. `C₃ = −γ`.

This file currently establishes: the real prime zeta `primeZeta` is well-defined (summable for `s>1`)
and the real specialisation of mathlib's `riemannZeta_eulerProduct_exp_log`.  Both are axiom-clean.
-/
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Mertens
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace LeanFormalizations.Mertens

open Filter Topology

/-- **Real prime zeta** `P(s) = ∑'_{p prime} p^{−s}` (the Dirichlet series over primes). -/
noncomputable def primeZeta (s : ℝ) : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-s)

/-- The prime-zeta summand is summable for `s > 1` — a subseries of the convergent `p`-series
`∑_n n^{−s}` (`s > 1 ⇒ −s < −1`), restricted along the injection `Nat.Primes ↪ ℕ`. -/
lemma summable_primeZeta_term {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s)) := by
  have hN : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  exact hN.comp_injective Nat.Primes.coe_nat_injective

/-- The prime zeta is nonnegative. -/
lemma primeZeta_nonneg {s : ℝ} : 0 ≤ primeZeta s := by
  apply tsum_nonneg
  intro p
  positivity

/-- **Real specialisation of the ζ Euler product** (`riemannZeta_eulerProduct_exp_log`): for real
`s > 1`, `exp(∑'_p −log(1 − p^{−s})) = ζ(s)` in `ℂ`.  The starting point for taking real logarithms and
extracting the prime zeta. -/
lemma riemannZeta_eulerProduct_ofReal {s : ℝ} (hs : 1 < s) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))) = riemannZeta (s : ℂ) := by
  apply riemannZeta_eulerProduct_exp_log
  simpa using hs

/-- For a prime `p` and `s > 1`, the factor `p^{−s}` lies in `(0,1)` (indeed `≤ 1/2 < 1`). -/
lemma prime_rpow_lt_one {s : ℝ} (hs : 1 < s) (p : Nat.Primes) : (p : ℝ) ^ (-s) < 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  rw [Real.rpow_neg hppos.le]
  have h1 : (1 : ℝ) < (p : ℝ) ^ s := by
    have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
    exact Real.one_lt_rpow_iff_of_pos hppos |>.mpr (Or.inl ⟨hp1, by linarith⟩)
  rw [inv_lt_one_iff₀]
  right; exact h1

/-- Hence each Euler factor `1 − p^{−s}` is positive for `s > 1`. -/
lemma one_sub_prime_rpow_pos {s : ℝ} (hs : 1 < s) (p : Nat.Primes) : 0 < 1 - (p : ℝ) ^ (-s) :=
  by linarith [prime_rpow_lt_one hs p]

/-- **Term realness**: each complex Euler-log summand is the coercion of a real one — because
`1 − p^{−s}` is a positive real, so `Complex.log` of it is `Real.log` of it. -/
lemma neg_clog_eq_ofReal {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) := by
  have hppos : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hpos : 0 ≤ 1 - (p : ℝ) ^ (-s) := (one_sub_prime_rpow_pos hs p).le
  have hcast : (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hppos]; push_cast; ring_nf
  rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log hpos,
    ← Complex.ofReal_neg]

/-- The real Euler-log series `∑'_p −log(1−p^{−s})` is summable for `s > 1` — nonneg and bounded
termwise by `2·p^{−s}` (using `|log(1−x)+x| ≤ x²` and `x ≤ 1/2`). -/
lemma summable_real_eulerLog {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-s))) := by
  apply Summable.of_nonneg_of_le (f := fun p : Nat.Primes => 2 * (p : ℝ) ^ (-s))
  · intro p
    have hpos := one_sub_prime_rpow_pos hs p
    have hle1 : 1 - (p : ℝ) ^ (-s) ≤ 1 := by
      have : (0 : ℝ) ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
      linarith
    have := Real.log_nonpos hpos.le hle1
    linarith
  · intro p
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have hx0 : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by linarith) _
    have hxle : (p : ℝ) ^ (-s) ≤ 1 / 2 := by
      have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [Real.rpow_neg_one] at h1
      have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
      linarith
    have hb := log_one_sub_add_self_abs_le hx0 hxle
    rw [abs_le] at hb
    have hxle1 : (p : ℝ) ^ (-s) ≤ 1 := by linarith
    nlinarith [hb.1, hb.2, mul_nonneg hx0.le hx0.le]
  · exact (summable_primeZeta_term hs).mul_left 2

/-- Push the coercion through the tsum: the complex Euler-log sum is the coercion of the real one. -/
lemma clog_tsum_eq_ofReal {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))))
      = ((∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr (fun p => neg_clog_eq_ofReal hs p)

/-- **Real Euler product for `ζ`.**  For real `s > 1`, `ζ(s) = exp(∑'_p −log(1−p^{−s}))` as a positive
real (coerced into `ℂ`).  This makes `riemannZeta (s : ℂ)` manifestly real on `(1,∞)` and is the bridge
from mathlib's complex Euler product to a real-variable log-ζ identity. -/
lemma riemannZeta_eq_ofReal_exp {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ)
      = ((Real.exp (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s))) : ℝ) : ℂ) := by
  rw [← riemannZeta_eulerProduct_ofReal hs, clog_tsum_eq_ofReal hs, ← Complex.ofReal_exp]

/-- The Riemann ζ as a **real** function on `(1,∞)` (its real part; it is real there). -/
noncomputable def realZeta (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re

/-- On `(1,∞)`, `ζ` equals the coercion of its real value `realZeta`. -/
lemma riemannZeta_ofReal_eq {s : ℝ} (hs : 1 < s) : riemannZeta (s : ℂ) = (realZeta s : ℂ) := by
  rw [realZeta, riemannZeta_eq_ofReal_exp hs, Complex.ofReal_re]

/-- `realZeta s = exp(∑'_p −log(1−p^{−s}))`, hence positive on `(1,∞)`. -/
lemma realZeta_eq_exp {s : ℝ} (hs : 1 < s) :
    realZeta s = Real.exp (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s))) := by
  rw [realZeta, riemannZeta_eq_ofReal_exp hs, Complex.ofReal_re]

lemma realZeta_pos {s : ℝ} (hs : 1 < s) : 0 < realZeta s := by
  rw [realZeta_eq_exp hs]; exact Real.exp_pos _

/-- **Real log-ζ identity** (brick (i)): `log ζ(s) = ∑'_p −log(1−p^{−s})` for `s > 1`.  Taking `Real.log`
of the real Euler product.  Next: expand `−log(1−p^{−s}) = p^{−s} + ∑_{k≥2} p^{−ks}/k` to split this as
`primeZeta s + G(s)`. -/
lemma log_realZeta_eq {s : ℝ} (hs : 1 < s) :
    Real.log (realZeta s) = ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) := by
  rw [realZeta_eq_exp hs, Real.log_exp]

/-- **Per-prime Mercator expansion** (brick (ii-a)): `−log(1−p^{−s}) = ∑'_{n} (p^{−s})^{n+1}/(n+1)`
(mathlib `hasSum_pow_div_log_of_abs_lt_one`, applicable since `0 < p^{−s} < 1`).  The `n = 0` term is
`p^{−s}` (the prime-zeta contribution); the `n ≥ 1` tail is the correction `G`.  Next lap: Fubini this
over `Nat.Primes × ℕ` and combine with `log_realZeta_eq` to split `log ζ(s) = primeZeta s + G(s)`. -/
lemma neg_log_one_sub_prime_hasSum {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    HasSum (fun n : ℕ => ((p : ℝ) ^ (-s)) ^ (n + 1) / (n + 1)) (-Real.log (1 - (p : ℝ) ^ (-s))) := by
  apply Real.hasSum_pow_div_log_of_abs_lt_one
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    linarith
  rw [abs_of_pos (Real.rpow_pos_of_pos hppos _)]
  exact prime_rpow_lt_one hs p

/-- The `n = 0` term of the per-prime Mercator series is exactly `p^{−s}` — i.e. the prime-zeta
contribution to `−log(1−p^{−s})`.  (The split point for brick (ii-b): summing the `n = 0` slice over
primes gives `primeZeta s`, the `n ≥ 1` slices give the correction `G`.) -/
lemma mercator_zeroth_term {s : ℝ} (p : Nat.Primes) :
    ((p : ℝ) ^ (-s)) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) = (p : ℝ) ^ (-s) := by
  simp

/-- **The Mertens correction series** `G(s) = ∑'_p (−log(1−p^{−s}) − p^{−s})` — the per-prime sum of the
`n ≥ 1` Mercator tail `∑_{k≥2} p^{−ks}/k`.  Summable for `s > 1` (difference of two summable series), and
nonnegative.  At `s = 1` it is `∑'_p (−log(1−1/p) − 1/p) = −∑'_p (log(1−1/p) + 1/p)`, the quantity that
must equal `γ − M` for the classical `e^{−γ}`. -/
noncomputable def mertensCorr (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s))

/-- The correction summand is summable for `s > 1`: difference of `summable_real_eulerLog` and the
prime-zeta term. -/
lemma summable_mertensCorr_term {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)) :=
  (summable_real_eulerLog hs).sub (summable_primeZeta_term hs)

/-- **Brick (ii-b) — the log-ζ split**: for `s > 1`,
`log ζ(s) = P(s) + G(s)` with `P(s) = primeZeta s = ∑'_p p^{−s}` and `G(s) = mertensCorr s`.
This is the `n = 0` (prime-zeta) vs `n ≥ 1` (correction) split of the per-prime Mercator series, summed
over primes — obtained cleanly by `tsum_add` rather than a full double-series Fubini. -/
lemma log_realZeta_split {s : ℝ} (hs : 1 < s) :
    Real.log (realZeta s) = primeZeta s + mertensCorr s := by
  rw [log_realZeta_eq hs, primeZeta, mertensCorr,
    ← (summable_primeZeta_term hs).tsum_add (summable_mertensCorr_term hs)]
  exact tsum_congr (fun p => by ring)

/-- Each correction term `−log(1−p^{−s}) − p^{−s}` is nonnegative (it is the tail `∑_{k≥2} p^{−ks}/k ≥ 0`,
equivalently `−log(1−x) ≥ x` for `x ∈ [0,1)`). -/
lemma mertensCorr_term_nonneg {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    0 ≤ -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s) := by
  have hx1 : (p : ℝ) ^ (-s) < 1 := prime_rpow_lt_one hs p
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    linarith
  have hx0 : (0 : ℝ) ≤ (p : ℝ) ^ (-s) := (Real.rpow_pos_of_pos hppos _).le
  -- `log(1 - x) ≤ -x`  ⇔  `-log(1-x) - x ≥ 0`, from `log y ≤ y - 1` at `y = 1 - x`.
  have hy : Real.log (1 - (p : ℝ) ^ (-s)) ≤ (1 - (p : ℝ) ^ (-s)) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  linarith

/-- The correction series is nonnegative. -/
lemma mertensCorr_nonneg {s : ℝ} (hs : 1 < s) : 0 ≤ mertensCorr s :=
  tsum_nonneg (fun p => mertensCorr_term_nonneg hs p)

end LeanFormalizations.Mertens
