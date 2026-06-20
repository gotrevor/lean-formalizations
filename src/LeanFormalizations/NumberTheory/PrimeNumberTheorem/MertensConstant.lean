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

/-! ### Limit A — `P(s) + log(s−1) → −G(1)` as `s → 1⁺`

The ζ side of the constant.  Combining the split `log ζ(s) = P(s) + G(s)` with the mathlib asymptotic
`ζ(s) − 1/(s−1) → γ` (`tendsto_riemannZeta_sub_one_div_nhds_right`, real version) and the continuity of
`G = mertensCorr` at `1`.  This pins one of the two limits of `P(s)+log(s−1)`; Limit B (the Abel/Tauberian
transfer to `∑_{p≤x}1/p`) pins the other at `M − γ`, and uniqueness forces `C₃ = −γ`. -/

/-- **Real specialisation of `ζ(s) − 1/(s−1) → γ`.**  mathlib's
`tendsto_riemannZeta_sub_one_div_nhds_right` is `ℂ`-valued (along `𝓝[>] 1`); on `(1,∞)` the value is the
real `realZeta`, so taking real parts gives the real limit. -/
lemma tendsto_realZeta_sub_one_div :
    Tendsto (fun s : ℝ => realZeta s - 1 / (s - 1)) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
  have hc := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  have hre := (Complex.continuous_re.tendsto _).comp hc
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := hs
  rw [riemannZeta_ofReal_eq hs1]
  rw [Complex.sub_re, Complex.ofReal_re]
  congr 1
  rw [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
    ← Complex.ofReal_div, Complex.ofReal_re]

/-- `(s−1)·ζ(s) → 1` as `s → 1⁺` (the simple pole of ζ). -/
lemma tendsto_sub_one_mul_realZeta :
    Tendsto (fun s : ℝ => (s - 1) * realZeta s) (𝓝[>] 1) (𝓝 1) := by
  have hs1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0) := by
      simpa using (continuous_sub_right (1 : ℝ)).tendsto 1
    exact this.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun s : ℝ => (s - 1) * (realZeta s - 1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    have := hs1.mul tendsto_realZeta_sub_one_div
    simpa using this
  have := hprod.add (tendsto_const_nhds (x := (1 : ℝ)))
  simp only [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1' : (1 : ℝ) < s := hs
  have hne : s - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **A1**: `log ζ(s) + log(s−1) → 0` as `s → 1⁺` — because `(s−1)·ζ(s) → 1` and `log` is continuous at
`1` (`log((s−1)·ζ(s)) = log(s−1) + log ζ(s)`, both factors positive on `(1,∞)`). -/
lemma tendsto_logRealZeta_add_logSub :
    Tendsto (fun s : ℝ => Real.log (realZeta s) + Real.log (s - 1)) (𝓝[>] 1) (𝓝 0) := by
  have hcont : Tendsto (fun s : ℝ => Real.log ((s - 1) * realZeta s)) (𝓝[>] 1) (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      tendsto_sub_one_mul_realZeta
    simpa [Function.comp_def, Real.log_one] using h
  refine hcont.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1' : (1 : ℝ) < s := hs
  have hz : 0 < realZeta s := realZeta_pos hs1'
  have hsub : 0 < s - 1 := by linarith
  rw [Real.log_mul (by linarith) (ne_of_gt hz), add_comm]

/-- For `s ≥ 1` and a prime `p`, `p^{−s} ≤ 1/2` (so `1 − p^{−s} ≥ 1/2 > 0`). -/
lemma prime_rpow_le_half {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) : (p : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at h1
  have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
  linarith

/-- Each correction term is continuous on `[1,∞)` (`p^{−s}` is continuous, and `1 − p^{−s} ≥ 1/2 > 0`
there so `log` is too). -/
lemma continuousOn_mertensCorr_term (p : Nat.Primes) :
    ContinuousOn (fun s : ℝ => -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)) (Set.Ici 1) := by
  have hp_ne : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    positivity
  have hg : Continuous (fun s : ℝ => (p : ℝ) ^ (-s)) :=
    (Real.continuous_const_rpow hp_ne).comp continuous_neg
  refine ContinuousOn.sub ?_ hg.continuousOn
  refine ContinuousOn.neg (ContinuousOn.log (continuousOn_const.sub hg.continuousOn) ?_)
  intro s hs
  have hs1 : (1 : ℝ) ≤ s := hs
  have := prime_rpow_le_half hs1 p
  -- `1 − p^{−s} ≥ 1/2 ≠ 0`
  have : (0 : ℝ) < 1 - (p : ℝ) ^ (-s) := by linarith
  exact ne_of_gt this

/-- Termwise sup-norm bound for `s ≥ 1`: `|−log(1−p^{−s}) − p^{−s}| ≤ p^{−2}` (from `|log(1−x)+x| ≤ x²`
and `x = p^{−s} ≤ p^{−1}`), the summable dominator (`∑_p p^{−2} < ∞`). -/
lemma abs_mertensCorr_term_le {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    |(-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s))| ≤ (p : ℝ) ^ (-(2 : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hx0 : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos hppos _
  have hxle : (p : ℝ) ^ (-s) ≤ 1 / 2 := prime_rpow_le_half hs p
  have hb := log_one_sub_add_self_abs_le hx0 hxle
  -- rewrite `-log(1-x)-x = -(log(1-x)+x)`
  have heq : -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)
      = -(Real.log (1 - (p : ℝ) ^ (-s)) + (p : ℝ) ^ (-s)) := by ring
  rw [heq, abs_neg]
  refine hb.trans ?_
  -- `x² ≤ p^{−2}` :  `x = p^{−s} ≤ p^{−1}`, square monotone on `≥0`.
  have hxle1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hsq : ((p : ℝ) ^ (-1 : ℝ)) ^ 2 = (p : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-1 : ℝ)) 2, ← Real.rpow_mul hppos.le]
    norm_num
  calc ((p : ℝ) ^ (-s)) ^ 2 ≤ ((p : ℝ) ^ (-1 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hx0.le hxle1 2
    _ = (p : ℝ) ^ (-(2 : ℝ)) := hsq

/-- **A2 (continuity of `G`)**: `mertensCorr` is continuous on `[1,∞)` — a uniformly (by `p^{−2}`)
dominated series of functions continuous there.  In particular `mertensCorr s → mertensCorr 1` as
`s → 1⁺`. -/
lemma continuousOn_mertensCorr : ContinuousOn mertensCorr (Set.Ici 1) := by
  apply continuousOn_tsum continuousOn_mertensCorr_term
    (summable_primeZeta_term (show (1 : ℝ) < 2 by norm_num))
  intro p s hs
  rw [Real.norm_eq_abs]
  exact abs_mertensCorr_term_le hs p

lemma tendsto_mertensCorr_one : Tendsto mertensCorr (𝓝[>] 1) (𝓝 (mertensCorr 1)) := by
  have hC := (continuousOn_mertensCorr 1 (by simp)).tendsto
  exact hC.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)

/-- **Limit A**: `P(s) + log(s−1) → −G(1)` as `s → 1⁺`, where `G(1) = mertensCorr 1`.  Combine the split
`P(s) = log ζ(s) − G(s)` (`log_realZeta_split`) with A1 (`log ζ(s)+log(s−1)→0`) and A2 (`G(s)→G(1)`). -/
lemma tendsto_primeZeta_add_logSub :
    Tendsto (fun s : ℝ => primeZeta s + Real.log (s - 1)) (𝓝[>] 1) (𝓝 (-mertensCorr 1)) := by
  have h := tendsto_logRealZeta_add_logSub.sub tendsto_mertensCorr_one
  simp only [zero_sub] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := hs
  rw [log_realZeta_split hs1]; ring

/-! ### The bridge and the final reduction

`∑'_n primeCorrCoeff n = −G(1)` (the repo's ℕ-indexed correction series equals the negative of the
`Nat.Primes`-indexed `mertensCorr` at `1`), turning `mertensThirdConst = (∑'_n primeCorrCoeff n) − M`
into `mertensThirdConst = −G(1) − M`.  Combined with Limit A and the (deep) Limit B, uniqueness of
limits forces `mertensThirdConst = −γ`. -/

/-- **Bridge**: `∑'_n primeCorrCoeff n = −mertensCorr 1`.  The ℕ-indexed correction series (supported on
primes) reindexes to the `Nat.Primes`-indexed `mertensCorr`, with `p^{−1} = 1/p` and an overall sign. -/
lemma tsum_primeCorrCoeff_eq : (∑' n : ℕ, primeCorrCoeff n) = -mertensCorr 1 := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Nat.Primes.coe_nat_injective
  have hsupp : Function.support primeCorrCoeff ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hp : n.Prime := by
      by_contra h
      rw [primeCorrCoeff, if_neg h] at hn; exact hn rfl
    exact ⟨⟨n, hp⟩, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  have hneg : -mertensCorr 1
      = ∑' p : Nat.Primes, (Real.log (1 - (p : ℝ) ^ (-(1 : ℝ))) + (p : ℝ) ^ (-(1 : ℝ))) := by
    rw [mertensCorr, ← tsum_neg]
    exact tsum_congr (fun p => by ring)
  rw [hneg]
  refine tsum_congr (fun p => ?_)
  have hp : (p : ℕ).Prime := p.2
  rw [primeCorrCoeff, if_pos hp, Real.rpow_neg_one]

/-- **The final reduction (crux isolated).**  `mertensThirdConst = −γ` follows from the single deep
**Tauberian limit** `Limit B`: `P(s) + log(s−1) → M − γ` as `s → 1⁺`.  Everything else — Limit A (the ζ
Euler-product side), the bridge, and the algebra — is machine-checked here.  This concentrates the entire
remaining difficulty of the classical `e^{−γ}` Mertens constant into one precisely-stated real-analysis
fact (the Abel summation `P(s) = −log(s−1) + (M − γ) + o(1)`, where the `γ` enters via `Γ'(1) = −γ`). -/
theorem mertensThirdConst_eq_neg_gamma_of_tauberian
    (hTauber : Tendsto (fun s : ℝ => primeZeta s + Real.log (s - 1)) (𝓝[>] 1)
        (𝓝 (meisselMertensM - Real.eulerMascheroniConstant))) :
    mertensThirdConst = -Real.eulerMascheroniConstant := by
  have huniq : -mertensCorr 1 = meisselMertensM - Real.eulerMascheroniConstant :=
    tendsto_nhds_unique tendsto_primeZeta_add_logSub hTauber
  rw [mertensThirdConst, tsum_primeCorrCoeff_eq, huniq]
  ring

/-- **Classical Mertens 3rd, `e^{−γ}` form — modulo only the clean Tauberian limit.**
`∏_{p≤N}(1−1/p)·log N → e^{−γ}`, machine-checked given exactly `Limit B`
(`P(s)+log(s−1) → M − γ`).  Drops the opaque `mertensThirdConst = −γ` hypothesis of
`mertens_third_classical` in favour of a precise analytic statement about the prime zeta. -/
theorem mertens_third_classical_of_tauberian
    (hTauber : Tendsto (fun s : ℝ => primeZeta s + Real.log (s - 1)) (𝓝[>] 1)
        (𝓝 (meisselMertensM - Real.eulerMascheroniConstant))) :
    Tendsto (fun N : ℕ => primeProd N * Real.log N) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
  mertens_third_classical (mertensThirdConst_eq_neg_gamma_of_tauberian hTauber)

/-! ### Toward Limit B (the Tauberian crux) — `primeZeta` as a limit of prime partial sums

**Route for Limit B** (`P(s)+log(s−1) → M − γ`), with all mathlib footholds now identified:
take `c(k) = [k prime]/k`, `f(t) = t^{1−s}`; then `f(k)·c(k) = [k prime]·k^{−s}` and
`∑_{k≤n} c(k) = ∑_{p≤n} 1/p`.  mathlib's Abel summation
(`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) gives, since the boundary `f(n)·∑_{p≤n}1/p =
n^{1−s}·(log log n + M + o(1)) → 0` for `s > 1`,
`P(s) = (s−1) ∫_1^∞ (∑_{p≤t} 1/p)·t^{−s} dt`  (**brick B1**).
The `s → 1⁺` limit (**brick B2**) feeds in `∑_{p≤t} 1/p = log log t + M + o(1)`
(`mertens_second_tendsto`); the `M`-part gives `M·2^{1−s} → M`, the `o(1)`-part `→ 0`, and the
`log log t` part, after `u = (s−1) log t`, becomes `∫_0^∞ (log u − log(s−1)) e^{−u} du = −γ − log(s−1)`,
where `−γ = Γ'(1)` comes from `Real.hasDerivAt_Gamma_one`.  Net: `P(s) = −log(s−1) + (M − γ) + o(1)`.

**Brick B0** (below): `primeZeta s = lim_N ∑_{p≤N} p^{−s}`, connecting the `tsum` (over `Nat.Primes`) to
the Finset partial sums that the Abel machinery consumes.  Axiom-clean. -/

/-- Coefficient form of the prime-zeta summand: `p^{−s}` at primes, `0` elsewhere. -/
noncomputable def primeZetaCoeff (s : ℝ) (n : ℕ) : ℝ := if n.Prime then (n : ℝ) ^ (-s) else 0

/-- Termwise bound `|primeZetaCoeff s n| ≤ n^{−s}` (equality at primes, `0 ≤ n^{−s}` elsewhere). -/
lemma abs_primeZetaCoeff_le (s : ℝ) (n : ℕ) : |primeZetaCoeff s n| ≤ (n : ℝ) ^ (-s) := by
  unfold primeZetaCoeff
  split_ifs with hp
  · rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  · rw [abs_zero]; exact Real.rpow_nonneg (by positivity) _

/-- `primeZetaCoeff s` is summable for `s > 1` (bounded by the convergent `p`-series `∑ n^{−s}`). -/
lemma summable_primeZetaCoeff {s : ℝ} (hs : 1 < s) : Summable (primeZetaCoeff s) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s))
    (Real.summable_nat_rpow.mpr (by linarith))
  intro n; rw [Real.norm_eq_abs]; exact abs_primeZetaCoeff_le s n

/-- The ℕ-indexed prime-zeta coefficients sum (over all `n`) to the `Nat.Primes`-indexed `primeZeta`. -/
lemma tsum_primeZetaCoeff_eq {s : ℝ} : (∑' n : ℕ, primeZetaCoeff s n) = primeZeta s := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Nat.Primes.coe_nat_injective
  have hsupp : Function.support (primeZetaCoeff s) ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hp : n.Prime := by
      by_contra h; rw [primeZetaCoeff, if_neg h] at hn; exact hn rfl
    exact ⟨⟨n, hp⟩, rfl⟩
  rw [← hinj.tsum_eq hsupp, primeZeta]
  exact tsum_congr (fun p => by rw [primeZetaCoeff, if_pos p.2])

/-- **Brick B0**: `primeZeta s = lim_N ∑_{p≤N} p^{−s}` (partial sums of prime reciprocal `s`-powers
converge to the prime zeta) — the form consumed by Abel summation toward Limit B. -/
lemma primeZetaCoeff_tendsto {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, primeZetaCoeff s k) atTop (𝓝 (primeZeta s)) := by
  rw [← tsum_primeZetaCoeff_eq]
  exact (summable_primeZetaCoeff hs).hasSum.tendsto_sum_nat

/-- **Harmonic bound on prime reciprocals** `∑_{p≤n} 1/p ≤ 1 + log n` — a subsum of the harmonic series
`H_n ≤ 1 + log n` (`harmonic_le_one_add_log`).  This is the `O(log n)` envelope that makes the Abel
boundary term `n^{1−s}·∑_{p≤n}1/p → 0` vanish for `s > 1` (cf. `boundary_decay`). -/
lemma primeRecipSum_le_one_add_log (n : ℕ) : primeRecipSum n ≤ 1 + Real.log n := by
  have h1 : primeRecipSum n ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := by
    rw [primeRecipSum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_Icc]; exact ⟨hp.1.1, hp.1.2⟩
    · intro k _ _; positivity
  have h2 : (harmonic n : ℝ) = ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  calc primeRecipSum n ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := h1
    _ = (harmonic n : ℝ) := h2.symm
    _ ≤ 1 + Real.log n := harmonic_le_one_add_log n

/-- Derivative of the Abel weight `f(t) = t^{1−s}`: `f'(t) = (1−s)·t^{−s}` for `t > 0`. -/
lemma hasDerivAt_rpow_one_sub {s t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => u ^ (1 - s)) ((1 - s) * t ^ (-s)) t := by
  have h := Real.hasDerivAt_rpow_const (x := t) (p := 1 - s) (Or.inl (ne_of_gt ht))
  simpa only [show (1 : ℝ) - s - 1 = -s by ring] using h

/-- `f(t) = t^{1−s}` is differentiable at every `t > 0` (the `hf_diff` hypothesis of the Abel theorem
on `Ici 1`). -/
lemma differentiableAt_rpow_one_sub {s t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun u : ℝ => u ^ (1 - s)) t :=
  (hasDerivAt_rpow_one_sub ht).differentiableAt

/-- The derivative value: `deriv (·^{1−s}) t = (1−s)·t^{−s}` for `t > 0`. -/
lemma deriv_rpow_one_sub {s t : ℝ} (ht : 0 < t) :
    deriv (fun u : ℝ => u ^ (1 - s)) t = (1 - s) * t ^ (-s) :=
  (hasDerivAt_rpow_one_sub ht).deriv

open MeasureTheory in
/-- `deriv (·^{1−s})` is locally integrable on `Ici 1` (it agrees with the continuous `(1−s)·t^{−s}`
there) — the `hf_int` hypothesis of `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`. -/
lemma locallyIntegrableOn_deriv_rpow_one_sub {s : ℝ} :
    LocallyIntegrableOn (deriv (fun u : ℝ => u ^ (1 - s))) (Set.Ici 1) := by
  refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
  refine ContinuousOn.congr (f := fun t : ℝ => (1 - s) * t ^ (-s)) ?_ ?_
  · refine continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => ?_))
    refine Or.inl ?_
    simp only [Set.mem_Ici] at ht
    simp only [id_eq]
    linarith
  · intro t ht
    simp only [Set.mem_Ici] at ht
    exact deriv_rpow_one_sub (by linarith)

/-- Prime-reciprocal coefficient `c(k) = [k prime]/k` — the Abel-summation coefficient whose partial
sums are `∑_{p≤n} 1/p = primeRecipSum`. -/
noncomputable def primeRecipCoeff (k : ℕ) : ℝ := if k.Prime then (k : ℝ)⁻¹ else 0

/-- `c(0) = 0` (the `hc` hypothesis of `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`). -/
lemma primeRecipCoeff_zero : primeRecipCoeff 0 = 0 := by
  rw [primeRecipCoeff, if_neg Nat.not_prime_zero]

/-- The Abel partial sum of `primeRecipCoeff` over `Icc 0 n` is exactly `primeRecipSum n`. -/
lemma sum_Icc_primeRecipCoeff (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, primeRecipCoeff k = primeRecipSum n := by
  rw [primeRecipSum]
  simp only [primeRecipCoeff]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hset : (Finset.Icc 0 n).filter Nat.Prime = (Finset.Ioc 0 n).filter Nat.Prime := by
    ext p
    constructor
    · intro h
      rw [Finset.mem_filter, Finset.mem_Icc] at h
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨h.2.pos, h.1.2⟩, h.2⟩
    · intro h
      rw [Finset.mem_filter, Finset.mem_Ioc] at h
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, h.1.2⟩, h.2⟩
  rw [hset]

/-- The Abel product `f(k)·c(k) = k^{1−s}·[k prime]/k = [k prime]·k^{−s} = primeZetaCoeff s k`. -/
lemma rpow_one_sub_mul_primeRecipCoeff (s : ℝ) (k : ℕ) :
    (k : ℝ) ^ (1 - s) * primeRecipCoeff k = primeZetaCoeff s k := by
  rw [primeRecipCoeff, primeZetaCoeff]
  split_ifs with hp
  · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hp.pos
    rw [← Real.rpow_neg_one (k : ℝ), ← Real.rpow_add hk0]
    ring_nf
  · rw [mul_zero]

/-- **Abel boundary-decay** (general): for `s > 1` and any nonnegative `a(n) ≤ 1 + log n`, the boundary
`n^{1−s}·a(n) → 0` (polynomial decay beats log growth).  Verified-in-kernel port of an Aristotle proof
(`tendsto_pow_mul_exp_neg`, `tendsto_rpow_neg_atTop`, squeeze). -/
theorem boundary_decay (s : ℝ) (hs : 1 < s) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (haC : ∀ n, a n ≤ 1 + Real.log n) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s) * a n) atTop (nhds 0) := by
  have h_log : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s) * Real.log n) atTop (nhds 0) := by
    suffices h_log : Tendsto (fun u : ℝ => Real.exp ((1 - s) * u) * u) atTop (nhds 0) by
      have := h_log.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp +decide [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn), mul_comm]
    suffices h_y : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (nhds 0) by
      have := h_y.comp (Filter.tendsto_id.const_mul_atTop (sub_pos.mpr hs))
      convert this.div_const (s - 1) using 2 <;> norm_num <;> grind
    convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1) using 2; norm_num
  refine squeeze_zero (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (ha0 _))
    (fun n => mul_le_mul_of_nonneg_left (haC _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
  simpa [mul_add] using Filter.Tendsto.add
    (tendsto_rpow_neg_atTop (by linarith : 0 < s - 1) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop) h_log

/-- `primeRecipSum n ≥ 0` (a sum of positive prime reciprocals). -/
lemma primeRecipSum_nonneg (n : ℕ) : 0 ≤ primeRecipSum n := by
  rw [primeRecipSum]; exact Finset.sum_nonneg (fun p _ => by positivity)

/-- **Abel boundary limit for the prime zeta** (`h_lim` of `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`):
`(n^{1−s})·(∑_{k≤n} primeRecipCoeff k) → 0` for `s > 1`.  This is the `l = 0` boundary that, with the
remaining bigO/integrability hypotheses, yields `primeZeta s = (s−1)∫_1^∞ (∑_{p≤t}1/p)·t^{−s} dt` (brick B1). -/
lemma abel_boundary_tendsto {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s) * ∑ k ∈ Finset.Icc 0 n, primeRecipCoeff k)
      atTop (nhds 0) := by
  refine (boundary_decay s hs primeRecipSum primeRecipSum_nonneg primeRecipSum_le_one_add_log).congr' ?_
  filter_upwards with n
  rw [sum_Icc_primeRecipCoeff]

/-- **Abel bigO domination** (`hg_dom` of `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`): the integrand
`f'(t)·∑_{k≤⌊t⌋} c(k) = (1−s)t^{−s}·∑_{p≤⌊t⌋}1/p` is `O(t^{−s}(1+log t))` at `∞` (constant `|1−s|`, using
`∑_{p≤⌊t⌋}1/p ≤ 1 + log⌊t⌋ ≤ 1 + log t`).  The dominator's integrability is `hg_int` (delegated). -/
lemma abel_hg_dom {s : ℝ} (hs : 1 < s) :
    (fun t : ℝ => deriv (fun u : ℝ => u ^ (1 - s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeRecipCoeff k)
      =O[atTop] (fun t : ℝ => t ^ (-s) * (1 + Real.log t)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨|1 - s|, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hfloor1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hderiv : deriv (fun u : ℝ => u ^ (1 - s)) t = (1 - s) * t ^ (-s) := deriv_rpow_one_sub ht0
  have htneg : (0 : ℝ) < t ^ (-s) := Real.rpow_pos_of_pos ht0 _
  have hps0 : 0 ≤ primeRecipSum ⌊t⌋₊ := primeRecipSum_nonneg _
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hps_le : primeRecipSum ⌊t⌋₊ ≤ 1 + Real.log t := by
    refine (primeRecipSum_le_one_add_log _).trans ?_
    have : Real.log ⌊t⌋₊ ≤ Real.log t :=
      Real.log_le_log (by exact_mod_cast hfloor1) (Nat.floor_le ht0.le)
    linarith
  have hprod1 : (0 : ℝ) ≤ t ^ (-s) * primeRecipSum ⌊t⌋₊ := mul_nonneg htneg.le hps0
  have hprod2 : (0 : ℝ) ≤ t ^ (-s) * (1 + Real.log t) := mul_nonneg htneg.le (by linarith)
  rw [hderiv, sum_Icc_primeRecipCoeff, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul,
    abs_of_nonneg hprod1, abs_of_nonneg hprod2]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hps_le htneg.le) (abs_nonneg _)

open MeasureTheory in
/-- **Abel dominator integrability** (`hg_int` of `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`):
the dominator `g(t) = t^{−s}·(1+log t)` is integrable at `atTop` for `s > 1`.

Proof: with `ε = (s−1)/2 > 0` and `s' = s − ε = (s+1)/2 ∈ (1, s)`, the dominator is `O(t^{−s'})`
at `∞` — because `1 + log t = O(t^{ε})` (`isLittleO_log_rpow_atTop`, log beats any positive power) so
`t^{−s}·(1+log t) = O(t^{−s}·t^{ε}) = O(t^{−s+ε})` — and `t^{−s+ε} = t^{−s'}` is integrable at `atTop`
since `−s' < −1` (`integrableAtFilter_rpow_atTop_iff`).  The function is continuous on `Ioi 0` so
strongly measurable at `atTop`; `IsBigO.integrableAtFilter` then transfers integrability. -/
lemma integrableAtFilter_rpow_neg_mul_log {s : ℝ} (hs : 1 < s) :
    IntegrableAtFilter (fun t : ℝ => t ^ (-s) * (1 + Real.log t)) atTop := by
  set ε : ℝ := (s - 1) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  -- `1 + log t = O(t^ε)`: the constant is bounded by `t^ε` and `log = o(t^ε)`.
  have hlog : (fun t : ℝ => 1 + Real.log t) =O[atTop] (fun t : ℝ => t ^ ε) := by
    have h1 : (fun _ : ℝ => (1 : ℝ)) =O[atTop] (fun t : ℝ => t ^ ε) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_one,
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      exact Real.one_le_rpow ht hε.le
    exact h1.add (isLittleO_log_rpow_atTop hε).isBigO
  -- main domination `t^{−s}·(1+log t) = O(t^{−s+ε})`.
  have hmain : (fun t : ℝ => t ^ (-s) * (1 + Real.log t))
      =O[atTop] (fun t : ℝ => t ^ (-s + ε)) := by
    have hmul := (Asymptotics.isBigO_refl (fun t : ℝ => t ^ (-s)) atTop).mul hlog
    have heq : (fun t : ℝ => t ^ (-s) * t ^ ε) =ᶠ[atTop] (fun t : ℝ => t ^ (-s + ε)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [← Real.rpow_add ht]
    exact hmul.trans heq.isBigO
  -- strong measurability at `atTop` (continuous on `Ioi 0`).
  have hfm : StronglyMeasurableAtFilter (fun t : ℝ => t ^ (-s) * (1 + Real.log t)) atTop := by
    refine ⟨Set.Ioi 0, Ioi_mem_atTop 0, ?_⟩
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (Set.mem_Ioi.mp ht)))
    · exact continuousOn_const.add (Real.continuousOn_log.mono (fun t ht => (Set.mem_Ioi.mp ht).ne'))
  -- dominator integrable at `atTop` (`−s + ε < −1`).
  have hg : IntegrableAtFilter (fun t : ℝ => t ^ (-s + ε)) atTop :=
    integrableAtFilter_rpow_atTop_iff.mpr (by rw [hε_def]; linarith)
  exact hmain.integrableAtFilter hfm hg

open MeasureTheory in
/-- **Brick B1 — Abel-summation integral representation of the prime zeta.**  For `s > 1`,
`P(s) = (s−1)·∫_1^∞ (∑_{p≤⌊t⌋} 1/p)·t^{−s} dt`.

Obtained from mathlib's Abel summation `tendsto_sum_mul_atTop_nhds_one_sub_integral₀` with weight
`f(t)=t^{1−s}` and coefficients `c(k)=[k prime]/k`: the partial sums
`∑_{k≤n} f(k)·c(k) = ∑_{p≤n} p^{−s} → P(s)` (B0), while the boundary term `f(n)·∑_{p≤n}1/p → 0`
vanishes (`abel_boundary_tendsto`), leaving `−∫_1^∞ f'(t)·∑_{p≤⌊t⌋}1/p dt` with `f'(t)=(1−s)t^{−s}`.

Combined with `mertens_second_tendsto` (`∑_{p≤t}1/p = log log t + M + o(1)`), this is the launch
point for brick B2 (the `s→1⁺` limit, where `−γ = Γ'(1)` enters). -/
theorem primeZeta_eq_abel_integral {s : ℝ} (hs : 1 < s) :
    primeZeta s = (s - 1) * ∫ t in Set.Ioi (1 : ℝ), t ^ (-s) * primeRecipSum ⌊t⌋₊ := by
  -- `f(t) = t^{1−s}` is differentiable on `Ici 1`.
  have hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun u : ℝ => u ^ (1 - s)) t := by
    intro t ht
    rw [Set.mem_Ici] at ht
    exact differentiableAt_rpow_one_sub (by linarith)
  -- Apply Abel summation with all six (now-proven) hypotheses; the boundary limit `l = 0`.
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun u : ℝ => u ^ (1 - s))
    primeRecipCoeff primeRecipCoeff_zero hf_diff locallyIntegrableOn_deriv_rpow_one_sub
    (abel_boundary_tendsto hs) (abel_hg_dom hs) (integrableAtFilter_rpow_neg_mul_log hs)
  -- The Abel partial sums `∑_{k≤n} f(k)·c(k)` are exactly `∑_{p≤n} p^{−s}` (the prime-zeta coeffs).
  have habel2 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, primeZetaCoeff s k) atTop
      (𝓝 ((0 : ℝ) - ∫ t in Set.Ioi (1 : ℝ),
        deriv (fun u : ℝ => u ^ (1 - s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeRecipCoeff k)) := by
    refine habel.congr (fun n => ?_)
    exact Finset.sum_congr rfl (fun k _ => rpow_one_sub_mul_primeRecipCoeff s k)
  -- The same partial sums converge to `primeZeta s` (B0; reconcile `Icc 0 n` with `range (n+1)`).
  have hL : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, primeZetaCoeff s k) atTop
      (𝓝 (primeZeta s)) := by
    have h2 := (primeZetaCoeff_tendsto hs).comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun n => ?_)
    simp only [Function.comp_apply]
    rw [Nat.range_succ_eq_Icc_zero]
  -- On `Ioi 1` the integrand is `(1−s)·(t^{−s}·∑_{p≤⌊t⌋}1/p)`; pull the constant out.
  have key : (∫ t in Set.Ioi (1 : ℝ),
        deriv (fun u : ℝ => u ^ (1 - s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeRecipCoeff k)
      = (1 - s) * ∫ t in Set.Ioi (1 : ℝ), t ^ (-s) * primeRecipSum ⌊t⌋₊ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    rw [deriv_rpow_one_sub (by linarith), sum_Icc_primeRecipCoeff]
    ring
  -- Uniqueness of limits, then simplify the integral.
  calc primeZeta s
      = (0 : ℝ) - ∫ t in Set.Ioi (1 : ℝ),
          deriv (fun u : ℝ => u ^ (1 - s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeRecipCoeff k :=
        tendsto_nhds_unique hL habel2
    _ = (s - 1) * ∫ t in Set.Ioi (1 : ℝ), t ^ (-s) * primeRecipSum ⌊t⌋₊ := by rw [key]; ring

/-! ### Toward Limit B / brick B2 — the `s→1⁺` analysis where `−γ` enters

The integral representation `primeZeta s = (s−1)∫_1^∞ A(t)·t^{−s} dt` (`primeZeta_eq_abel_integral`,
`A(t)=∑_{p≤⌊t⌋}1/p`) is the launch point.  After the substitution `t = e^x` it reads
`primeZeta s = (s−1)∫_0^∞ A(eˣ)·e^{−(s−1)x} dx`, and with `A(eˣ) = log x + M + o(1)` (Mertens 2nd)
the three pieces are: `(s−1)∫_0^∞ M e^{−(s−1)x} = M`; the error `→ 0` (the Tauberian/Abelian step);
and `(s−1)∫_0^∞ log x · e^{−(s−1)x} dx → −γ − log(s−1)` after `u=(s−1)x`, the last because
`∫_0^∞ log u · e^{−u} du = Γ'(1) = −γ` (the lemma below).  Net: `primeZeta s + log(s−1) → M − γ`. -/

open MeasureTheory in
/-- **`Γ'(1) = −γ` in integral form**: `∫_0^∞ log u · e^{−u} du = −γ` (the Euler–Mascheroni constant).

This is where `−γ` enters the Mertens constant.  Proof: mathlib's `Complex.hasDerivAt_GammaIntegral`
gives `(GammaIntegral)'(1) = ∫_0^∞ u^{1−1}·(log u · e^{−u}) du = ↑(∫_0^∞ log u·e^{−u} du)`; on `Re > 0`
the Gamma integral agrees with `Complex.Gamma`, which on the reals is `↑(Real.Gamma ·)`, so this
complex derivative equals `↑(Real.Gamma'(1)) = ↑(−γ)` by `Real.hasDerivAt_Gamma_one`.  Uniqueness of
derivatives + injectivity of `ofReal` finish. -/
theorem integral_log_mul_exp_neg_Ioi_eq_neg_gamma :
    ∫ t in Set.Ioi (0 : ℝ), Real.log t * Real.exp (-t) = -Real.eulerMascheroniConstant := by
  -- Derivative of the complex Gamma integral at `s = 1` (a real point).
  have hpos : (0 : ℝ) < ((1 : ℝ) : ℂ).re := by simp
  have hGI := Complex.hasDerivAt_GammaIntegral hpos
  have hcomp := hGI.comp_ofReal
  -- Near `1`, `GammaIntegral ↑y = ↑(Real.Gamma y)`.
  have heq : (fun y : ℝ => Complex.GammaIntegral ↑y)
      =ᶠ[nhds (1 : ℝ)] fun y : ℝ => (↑(Real.Gamma y) : ℂ) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
    rw [Set.mem_Ioi] at hy
    rw [← Complex.Gamma_eq_integral (by rwa [Complex.ofReal_re]), Complex.Gamma_ofReal]
  -- The real Gamma derivative at `1` is `−γ`.
  have hR : HasDerivAt (fun y : ℝ => (↑(Real.Gamma y) : ℂ))
      (↑(-Real.eulerMascheroniConstant)) 1 := Real.hasDerivAt_Gamma_one.ofReal_comp
  -- Uniqueness of the derivative: the complex Gamma-integral value equals `↑(−γ)`.
  have huniq := (hcomp.congr_of_eventuallyEq heq.symm).unique hR
  -- Identify that value with `↑(∫_0^∞ log u·e^{−u} du)` and cancel the coercion.
  have hcast : (↑(∫ t in Set.Ioi (0 : ℝ), Real.log t * Real.exp (-t)) : ℂ)
      = ↑(-Real.eulerMascheroniConstant) := by
    rw [← huniq, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    rw [Complex.ofReal_one, sub_self, Complex.cpow_zero, one_mul]
    push_cast; ring
  exact_mod_cast hcast

open MeasureTheory in
/-- **Power-integral identity**: for `s > 1` and `c > 0`, `(s−1)·∫_c^∞ t^{−s} dt = c^{1−s}`.
(`∫_c^∞ t^{−s} = c^{1−s}/(s−1)` by `integral_Ioi_rpow_of_lt`.)  The `M`-part of brick B2 uses this at
`c = 2`: `M·(s−1)∫_2^∞ t^{−s} = M·2^{1−s} → M`. -/
lemma sub_one_mul_integral_rpow_neg {s : ℝ} (hs : 1 < s) {c : ℝ} (hc : 0 < c) :
    (s - 1) * ∫ t in Set.Ioi c, t ^ (-s) = c ^ (1 - s) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : (-s) < (-1 : ℝ)) hc, show (-s) + 1 = 1 - s by ring]
  have hne : (1 : ℝ) - s ≠ 0 := ne_of_lt (by linarith)
  field_simp
  ring

open MeasureTheory in
/-- **M-part core of brick B2**: `(s−1)·∫_2^∞ t^{−s} dt → 1` as `s → 1⁺` (since it equals `2^{1−s}`,
which `→ 2^0 = 1`).  Hence the `M`-term `M·(s−1)∫_2^∞ t^{−s} → M` — one of the three pieces of
`primeZeta s + log(s−1) → M − γ`. -/
lemma tendsto_sub_one_mul_integral_rpow :
    Tendsto (fun s : ℝ => (s - 1) * ∫ t in Set.Ioi (2 : ℝ), t ^ (-s)) (𝓝[>] 1) (𝓝 1) := by
  have hcont : Continuous (fun s : ℝ => (2 : ℝ) ^ (1 - s)) := by
    have h : (fun s : ℝ => (2 : ℝ) ^ (1 - s)) = fun s => Real.exp (Real.log 2 * (1 - s)) := by
      funext s; rw [Real.rpow_def_of_pos (by norm_num)]
    rw [h]; fun_prop
  have htend : Tendsto (fun s : ℝ => (2 : ℝ) ^ (1 - s)) (𝓝 1) (𝓝 1) := by
    simpa using hcont.tendsto (1 : ℝ)
  refine (htend.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (sub_one_mul_integral_rpow_neg (Set.mem_Ioi.mp hs) (by norm_num)).symm

open MeasureTheory in
/-- **Change of variables `u = (s−1)x` for the log-part of brick B2.**  For `s > 1`,
`(s−1)·∫_0^∞ log x · e^{−(s−1)x} dx = ∫_0^∞ (log u − log(s−1))·e^{−u} du`
(`integral_comp_mul_left_Ioi` after rewriting `log x = log((s−1)x) − log(s−1)`).

Evaluating the RHS — split via `integral_sub`, then `∫_0^∞ log u·e^{−u} = −γ`
(`integral_log_mul_exp_neg_Ioi_eq_neg_gamma`) and `∫_0^∞ e^{−u} = 1` — gives `−γ − log(s−1)`: the
term that carries `−γ` and cancels the `+log(s−1)` in Limit B.  (RHS evaluation = next brick; needs
`IntegrableOn (log·e^{−·}) (Ioi 0)`.) -/
lemma sub_one_mul_integral_log_exp_eq {s : ℝ} (hs : 1 < s) :
    (s - 1) * ∫ x in Set.Ioi (0 : ℝ), Real.log x * Real.exp (-((s - 1) * x))
      = ∫ u in Set.Ioi (0 : ℝ), (Real.log u - Real.log (s - 1)) * Real.exp (-u) := by
  have hsub : (0 : ℝ) < s - 1 := by linarith
  -- rewrite the integrand as `G((s−1)x)` with `G u = (log u − log(s−1))·e^{−u}`.
  have hcongr : (∫ x in Set.Ioi (0 : ℝ), Real.log x * Real.exp (-((s - 1) * x)))
      = ∫ x in Set.Ioi (0 : ℝ),
          (fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u)) ((s - 1) * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    show Real.log x * Real.exp (-((s - 1) * x))
        = (Real.log ((s - 1) * x) - Real.log (s - 1)) * Real.exp (-((s - 1) * x))
    rw [Real.log_mul (ne_of_gt hsub) (ne_of_gt hx)]
    ring
  rw [hcongr, integral_comp_mul_left_Ioi
        (fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u)) 0 hsub,
      mul_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsub), one_mul]

open MeasureTheory in
/-- **Integrability of the Gamma-derivative integrand** `log u · e^{−u}` on `(0,∞)`.  Split at `1`:
on `(0,1]` it is dominated by `|log u|` (interval-integrable, `e^{−u} ≤ 1`); on `(1,∞)` by
`u·e^{−u}` (the `Γ(2)` integrand, `log u ≤ u`). -/
lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one (α := ℝ)), integrableOn_union]
  constructor
  · -- on `(0,1]`: `‖log u · e^{−u}‖ ≤ ‖log u‖`.
    have hlog : IntegrableOn (fun u : ℝ => Real.log u) (Set.Ioc (0 : ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one)]
      exact intervalIntegral.intervalIntegrable_log'
    refine (hlog.norm).mono' ?_ ?_
    · refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable measurableSet_Ioc
      · exact Real.continuousOn_log.mono (fun u hu => ne_of_gt hu.1)
      · exact (Real.continuous_exp.comp continuous_neg).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_mul]
      have hexp : |Real.exp (-u)| ≤ 1 := by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by linarith [hu.1])
      calc |Real.log u| * |Real.exp (-u)| ≤ |Real.log u| * 1 :=
            mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = ‖Real.log u‖ := by rw [mul_one, Real.norm_eq_abs]
  · -- on `(1,∞)`: `log u · e^{−u} ≤ u · e^{−u}` = the `Γ(2)` integrand.
    have hg : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ ((2 : ℝ) - 1)) (Set.Ioi (1 : ℝ)) :=
      (Real.GammaIntegral_convergent (by norm_num)).mono_set (Set.Ioi_subset_Ioi zero_le_one)
    refine hg.mono' ?_ ?_
    · refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable measurableSet_Ioi
      · exact Real.continuousOn_log.mono (fun u hu => ne_of_gt (lt_trans one_pos hu))
      · exact (Real.continuous_exp.comp continuous_neg).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Set.mem_Ioi] at hu
      have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.log_nonneg hu.le) (Real.exp_pos _).le)]
      have hlu : Real.log u ≤ u := le_trans (Real.log_le_sub_one_of_pos hu0) (by linarith)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm (Real.exp (-u)) u]
      exact mul_le_mul_of_nonneg_right hlu (Real.exp_pos _).le

open MeasureTheory in
/-- **Evaluation of the substituted log-integral**: for `s > 1`,
`∫_0^∞ (log u − log(s−1))·e^{−u} du = −γ − log(s−1)`, by splitting (`integral_sub`) into
`∫_0^∞ log u·e^{−u} = −γ` (`integral_log_mul_exp_neg_Ioi_eq_neg_gamma`) and
`log(s−1)·∫_0^∞ e^{−u} = log(s−1)·1`. -/
lemma integral_log_sub_logSub_mul_exp {s : ℝ} (hs : 1 < s) :
    ∫ u in Set.Ioi (0 : ℝ), (Real.log u - Real.log (s - 1)) * Real.exp (-u)
      = -Real.eulerMascheroniConstant - Real.log (s - 1) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_log_mul_exp_neg
  have h2 : IntegrableOn (fun u : ℝ => Real.log (s - 1) * Real.exp (-u)) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have hcongr : (fun u : ℝ => (Real.log u - Real.log (s - 1)) * Real.exp (-u))
      = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
    funext u; ring
  rw [hcongr, integral_sub h1 h2, integral_log_mul_exp_neg_Ioi_eq_neg_gamma,
    integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

open MeasureTheory in
/-- **Log-part of brick B2, fully evaluated**: for `s > 1`,
`(s−1)·∫_0^∞ log x · e^{−(s−1)x} dx = −γ − log(s−1)`.  Combines the change of variables
`sub_one_mul_integral_log_exp_eq` with the evaluation `integral_log_sub_logSub_mul_exp`.

This is the piece carrying `−γ`; its `−log(s−1)` cancels the `+log(s−1)` in `primeZeta s + log(s−1)`,
and together with the `M`-part (`tendsto_sub_one_mul_integral_rpow`) and the Tauberian error (→0)
yields Limit B = `M − γ`. -/
lemma sub_one_mul_integral_log_exp {s : ℝ} (hs : 1 < s) :
    (s - 1) * ∫ x in Set.Ioi (0 : ℝ), Real.log x * Real.exp (-((s - 1) * x))
      = -Real.eulerMascheroniConstant - Real.log (s - 1) := by
  rw [sub_one_mul_integral_log_exp_eq hs, integral_log_sub_logSub_mul_exp hs]

open MeasureTheory in
/-- **Exponential form of brick B1** (substitution `t = eˣ`): for `s > 1`,
`primeZeta s = (s−1)·∫_0^∞ (∑_{p≤⌊eˣ⌋}1/p)·e^{−(s−1)x} dx`.

From `primeZeta_eq_abel_integral` by the change of variables `t = eˣ` (so `eˣ·(eˣ)^{−s} = e^{−(s−1)x}`),
formalized with `integral_image_eq_integral_abs_deriv_smul` (`exp` is injective with derivative `exp` and
`exp '' Ioi 0 = Ioi 1`).  This is the form where Mertens 2nd `∑_{p≤⌊eˣ⌋}1/p = log x + M + o(1)` splits the
integral into the log-part (`sub_one_mul_integral_log_exp` → `−γ − log(s−1)`), the M-part, and the
Tauberian error (→0). -/
lemma primeZeta_eq_abel_integral_exp {s : ℝ} (hs : 1 < s) :
    primeZeta s
      = (s - 1) * ∫ x in Set.Ioi (0 : ℝ),
          primeRecipSum ⌊Real.exp x⌋₊ * Real.exp (-((s - 1) * x)) := by
  rw [primeZeta_eq_abel_integral hs]
  congr 1
  have himg : Real.exp '' Set.Ioi 0 = Set.Ioi 1 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp x := Real.exp_lt_exp.mpr hx
    · intro hy
      have hy0 : (0 : ℝ) < y := by linarith
      have hlogpos : 0 < Real.log y := by
        rw [show (0 : ℝ) = Real.log 1 from Real.log_one.symm]; exact Real.log_lt_log one_pos hy
      exact ⟨Real.log y, hlogpos, Real.exp_log hy0⟩
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi (0 : ℝ))
    measurableSet_Ioi (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn) (fun t : ℝ => t ^ (-s) * primeRecipSum ⌊t⌋₊)
  rw [himg] at hcov
  rw [hcov]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [Set.mem_Ioi] at hx
  show |Real.exp x| • ((Real.exp x) ^ (-s) * primeRecipSum ⌊Real.exp x⌋₊)
      = primeRecipSum ⌊Real.exp x⌋₊ * Real.exp (-((s - 1) * x))
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
    ← mul_assoc, ← Real.exp_add, show x + x * -s = -((s - 1) * x) by ring]
  ring

open MeasureTheory in
/-- **M-part of brick B2 in the `eˣ` form**: `(s−1)·∫_0^∞ e^{−(s−1)x} dx = 1` for `s > 1`
(`∫_0^∞ e^{−(s−1)x} = 1/(s−1)`, `integral_exp_mul_Ioi`).  Hence the `M`-term
`(s−1)∫_0^∞ M·e^{−(s−1)x} = M` exactly. -/
lemma sub_one_mul_integral_exp_neg {s : ℝ} (hs : 1 < s) :
    (s - 1) * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-((s - 1) * x)) = 1 := by
  have hlt : -(s - 1) < 0 := by linarith
  have hcongr : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-((s - 1) * x)))
      = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(s - 1) * x) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [neg_mul])
  rw [hcongr, integral_exp_mul_Ioi hlt, mul_zero, Real.exp_zero]
  have hne : s - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- **Mertens 2nd along `x ↦ ⌊eˣ⌋`** (prerequisite for the Tauberian error of brick B2):
`primeRecipSum ⌊eˣ⌋ − log log ⌊eˣ⌋ → M` as `x → ∞`.  Just `mertens_second_tendsto` composed with
`⌊eˣ⌋ → ∞`.  Combined with `log log⌊eˣ⌋ − log x → 0`, this gives `r(x) := A(eˣ) − log x − M → 0`, the
input to the Abelian final-value step `(s−1)∫_0^∞ r(x)e^{−(s−1)x} → 0`. -/
lemma tendsto_primeRecipSum_floor_exp :
    Tendsto (fun x : ℝ =>
        primeRecipSum ⌊Real.exp x⌋₊ - Real.log (Real.log ⌊Real.exp x⌋₊)) atTop
      (nhds meisselMertensM) :=
  mertens_second_tendsto.comp (tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop)

open MeasureTheory in
/-- **Abelian final-value theorem** — the deep analytic crux of brick B2 (the Tauberian error step).

If `f → 0` at `atTop`, `f·e^{−δx}` is integrable on `(0,∞)` for every `δ>0`, and `|f|` is locally
integrable on every `(0,X]`, then
`δ·∫_0^∞ f(x)·e^{−δx} dx → 0` as `δ → 0⁺`.

Proof is the classical `ε`–`X` argument (no dominated convergence — mathlib is weak there): given
`ε`, pick `X` with `|f| ≤ ε/2` past `X`, and let `K = ∫_(0,X]|f|`.  Split `∫_0^∞ = ∫_(0,X] + ∫_(X,∞)`.
The **tail** is `≤ ∫_(X,∞)(ε/2)e^{−δx} = (ε/2)·e^{−δX}/δ ≤ (ε/2)/δ`, so `δ·|tail| ≤ ε/2`; the **head**
is `≤ ∫_(0,X]|f| = K` (since `e^{−δx}≤1` on `[0,∞)`), so `δ·|head| ≤ δK < ε/2` once `δ < ε/(2(K+1))`.
Hence `|δ·∫_0^∞| < ε`. -/
theorem tendsto_sub_one_mul_integral_abelian {f : ℝ → ℝ}
    (hf0 : Tendsto f atTop (𝓝 0))
    (hint : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun x => f x * Real.exp (-(δ * x))) (Set.Ioi 0))
    (hloc : ∀ X : ℝ, IntegrableOn (fun x => |f x|) (Set.Ioc 0 X)) :
    Tendsto (fun δ : ℝ => δ * ∫ x in Set.Ioi (0:ℝ), f x * Real.exp (-(δ * x)))
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X` past which `|f| ≤ ε/2`.
  obtain ⟨X₀, hX₀⟩ := Metric.tendsto_atTop.mp hf0 (ε / 2) (by positivity)
  set X : ℝ := max X₀ 1 with hXdef
  have hX0le : (0 : ℝ) ≤ X := le_trans zero_le_one (le_max_right _ _)
  have hXtail : ∀ y, X ≤ y → |f y| ≤ ε / 2 := by
    intro y hy
    have h := hX₀ y (le_trans (le_max_left _ _) hy)
    rw [dist_zero_right, Real.norm_eq_abs] at h
    exact h.le
  -- The head mass `K = ∫_(0,X] |f|`.
  set K : ℝ := ∫ y in Set.Ioc (0:ℝ) X, |f y| with hKdef
  have hKnonneg : 0 ≤ K := setIntegral_nonneg measurableSet_Ioc (fun y _ => abs_nonneg _)
  refine ⟨ε / (2 * (K + 1)), by positivity, ?_⟩
  intro δ hδmem hδdist
  rw [Set.mem_Ioi] at hδmem
  have hδ : 0 < δ := hδmem
  rw [dist_zero_right, Real.norm_eq_abs] at hδdist
  have hδlt : δ < ε / (2 * (K + 1)) := by rwa [abs_of_pos hδ] at hδdist
  -- Integrability on the two pieces, from `hint`.
  have hIoc : IntegrableOn (fun y => f y * Real.exp (-(δ * y))) (Set.Ioc 0 X) :=
    (hint δ hδ).mono_set Set.Ioc_subset_Ioi_self
  have hIoiX : IntegrableOn (fun y => f y * Real.exp (-(δ * y))) (Set.Ioi X) :=
    (hint δ hδ).mono_set (Set.Ioi_subset_Ioi hX0le)
  -- Split `∫_(0,∞) = ∫_(0,X] + ∫_(X,∞)`.
  have hsplit : (∫ y in Set.Ioi (0:ℝ), f y * Real.exp (-(δ * y)))
      = (∫ y in Set.Ioc (0:ℝ) X, f y * Real.exp (-(δ * y)))
        + ∫ y in Set.Ioi X, f y * Real.exp (-(δ * y)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hX0le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoiX]
  -- Head bound: `|∫_(0,X]| ≤ K`.
  have hhead : |∫ y in Set.Ioc (0:ℝ) X, f y * Real.exp (-(δ * y))| ≤ K := by
    have h1 : |∫ y in Set.Ioc (0:ℝ) X, f y * Real.exp (-(δ * y))|
        ≤ ∫ y in Set.Ioc (0:ℝ) X, ‖f y * Real.exp (-(δ * y))‖ := by
      rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    refine h1.trans ?_
    rw [hKdef]
    refine setIntegral_mono_on hIoc.norm (hloc X) measurableSet_Ioc (fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle1 : Real.exp (-(δ * y)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hy.1, hδ])
    calc |f y| * Real.exp (-(δ * y)) ≤ |f y| * 1 :=
          mul_le_mul_of_nonneg_left hle1 (abs_nonneg _)
      _ = |f y| := mul_one _
  -- Tail bound: `|∫_(X,∞)| ≤ (ε/2)/δ`.
  have hexpint : IntegrableOn (fun y => Real.exp (-(δ * y))) (Set.Ioi X) := by
    have h := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) X
    simpa only [neg_mul] using h
  have htail : |∫ y in Set.Ioi X, f y * Real.exp (-(δ * y))| ≤ (ε / 2) / δ := by
    have h1 : |∫ y in Set.Ioi X, f y * Real.exp (-(δ * y))|
        ≤ ∫ y in Set.Ioi X, ‖f y * Real.exp (-(δ * y))‖ := by
      rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    refine h1.trans ?_
    have h2 : (∫ y in Set.Ioi X, ‖f y * Real.exp (-(δ * y))‖)
        ≤ ∫ y in Set.Ioi X, (ε / 2) * Real.exp (-(δ * y)) := by
      refine setIntegral_mono_on hIoiX.norm (hexpint.const_mul (ε / 2)) measurableSet_Ioi
        (fun y hy => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hXtail y (le_of_lt hy)) (Real.exp_pos _).le
    refine h2.trans ?_
    rw [integral_const_mul]
    -- `∫_(X,∞) e^{−δy} = e^{−δX}/δ ≤ 1/δ`.
    have hval : (∫ y in Set.Ioi X, Real.exp (-(δ * y))) = Real.exp (-(δ * X)) / δ := by
      have h := integral_exp_mul_Ioi (a := -δ) (by linarith) X
      simp only [neg_mul] at h
      rw [h, neg_div_neg_eq]
    rw [hval]
    have hexple : Real.exp (-(δ * X)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hX0le, hδ])
    calc ε / 2 * (Real.exp (-(δ * X)) / δ)
        ≤ ε / 2 * (1 / δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          rw [div_le_div_iff_of_pos_right hδ]; exact hexple
      _ = ε / 2 / δ := mul_one_div _ _
  -- Combine.
  rw [dist_zero_right, Real.norm_eq_abs, hsplit]
  have hcombine : |δ * ((∫ y in Set.Ioc (0:ℝ) X, f y * Real.exp (-(δ * y)))
      + ∫ y in Set.Ioi X, f y * Real.exp (-(δ * y)))| ≤ δ * K + ε / 2 := by
    calc |δ * ((∫ y in Set.Ioc (0:ℝ) X, f y * Real.exp (-(δ * y)))
            + ∫ y in Set.Ioi X, f y * Real.exp (-(δ * y)))|
        = δ * |(∫ y in Set.Ioc (0:ℝ) X, f y * Real.exp (-(δ * y)))
            + ∫ y in Set.Ioi X, f y * Real.exp (-(δ * y))| := by
          rw [abs_mul, abs_of_pos hδ]
      _ ≤ δ * (|∫ y in Set.Ioc (0:ℝ) X, f y * Real.exp (-(δ * y))|
            + |∫ y in Set.Ioi X, f y * Real.exp (-(δ * y))|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hδ.le
      _ ≤ δ * (K + (ε / 2) / δ) := mul_le_mul_of_nonneg_left (add_le_add hhead htail) hδ.le
      _ = δ * K + ε / 2 := by field_simp
  refine lt_of_le_of_lt hcombine ?_
  -- `δK + ε/2 < ε`, since `δK < ε/2`.
  have hpos : 0 < 2 * (K + 1) := by positivity
  have hclear : δ * (2 * (K + 1)) < ε := by rw [← lt_div_iff₀ hpos]; exact hδlt
  nlinarith [hclear, hKnonneg, hδ]

/-! ### Integrability of the three `eˣ`-form pieces on `(0,∞)` (for the assembly of Limit B). -/

open MeasureTheory in
/-- `x·e^{−δx}` is integrable on `(0,∞)` for `δ>0` (the `Γ(2)` integrand rescaled), from
`integrableOn_rpow_mul_exp_neg_mul_rpow` at `s = p = 1`. -/
lemma integrableOn_id_mul_exp_neg_mul {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x => x * Real.exp (-(δ * x))) (Set.Ioi (0:ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := δ)
    (by norm_num) le_rfl hδ
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

open MeasureTheory in
/-- The linear envelope `(1+x)·e^{−δx}` is integrable on `(0,∞)` for `δ>0`. -/
lemma integrableOn_one_add_id_mul_exp_neg_mul {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x => (1 + x) * Real.exp (-(δ * x))) (Set.Ioi (0:ℝ)) := by
  have h1 : IntegrableOn (fun x => Real.exp (-(δ * x))) (Set.Ioi (0:ℝ)) := by
    have h := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) 0
    simpa only [neg_mul] using h
  have h2 := integrableOn_id_mul_exp_neg_mul hδ
  refine (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi

open MeasureTheory in
/-- **Integrability of the `primeRecipSum` piece**: `primeRecipSum⌊eˣ⌋·e^{−δx}` is integrable on
`(0,∞)` for `δ>0`, dominated by the envelope `(1+x)·e^{−δx}` since `primeRecipSum⌊eˣ⌋ ≤ 1 + log⌊eˣ⌋
≤ 1 + x` on `(0,∞)`. -/
lemma integrableOn_primeRecipSum_exp {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x => primeRecipSum ⌊Real.exp x⌋₊ * Real.exp (-(δ * x))) (Set.Ioi (0:ℝ)) := by
  refine (integrableOn_one_add_id_mul_exp_neg_mul hδ).mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · exact (Measurable.of_discrete (f := primeRecipSum)).comp Real.measurable_exp.nat_floor
    · exact (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Set.mem_Ioi] at hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (primeRecipSum_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hfloorpos : (0:ℝ) < (⌊Real.exp x⌋₊ : ℝ) := by
      have h1 : 1 ≤ ⌊Real.exp x⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp hx.le)
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    have hlog_le : Real.log ⌊Real.exp x⌋₊ ≤ x := by
      calc Real.log ⌊Real.exp x⌋₊
          ≤ Real.log (Real.exp x) := Real.log_le_log hfloorpos (Nat.floor_le (Real.exp_pos x).le)
        _ = x := Real.log_exp x
    have := primeRecipSum_le_one_add_log ⌊Real.exp x⌋₊
    linarith

open MeasureTheory in
/-- **Integrability of the `log` piece**: `log x·e^{−δx}` is integrable on `(0,∞)` for `δ>0`, by the
scaling `x ↦ δx` (`integrableOn_Ioi_comp_mul_left_iff`) from `(log u − log δ)·e^{−u}` (integrable as
`log·e^{−u}` minus a constant multiple of `e^{−u}`). -/
lemma integrableOn_log_mul_exp_neg_mul {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x => Real.log x * Real.exp (-(δ * x))) (Set.Ioi (0:ℝ)) := by
  have hG : IntegrableOn (fun u => (Real.log u - Real.log δ) * Real.exp (-u)) (Set.Ioi (0:ℝ)) := by
    have h2 : IntegrableOn (fun u => Real.log δ * Real.exp (-u)) (Set.Ioi (0:ℝ)) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    refine (integrableOn_log_mul_exp_neg.sub h2).congr_fun
      (fun u _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have key := (integrableOn_Ioi_comp_mul_left_iff
    (fun u => (Real.log u - Real.log δ) * Real.exp (-u)) 0 hδ).mpr (by rwa [mul_zero])
  refine key.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hx
  show (Real.log (δ * x) - Real.log δ) * Real.exp (-(δ * x)) = Real.log x * Real.exp (-(δ * x))
  rw [Real.log_mul (ne_of_gt hδ) (ne_of_gt hx)]; ring

/-! ### The Tauberian-error remainder `r(x) = primeRecipSum⌊eˣ⌋ − log x − M → 0`. -/

/-- `log⌊eˣ⌋ − x → 0` as `x → ∞`.  Squeeze: `log(1−e^{−x}) ≤ log⌊eˣ⌋ − x ≤ 0`, the lower bound from
`eˣ−1 < ⌊eˣ⌋` (`Nat.lt_floor_add_one`) and `log((eˣ−1)/eˣ) = log(eˣ−1) − x`, both ends `→ 0`. -/
lemma tendsto_log_floor_exp_sub :
    Tendsto (fun x => Real.log ⌊Real.exp x⌋₊ - x) atTop (𝓝 0) := by
  have hlower : Tendsto (fun x => Real.log (1 - Real.exp (-x))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x => 1 - Real.exp (-x)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub Real.tendsto_exp_neg_atTop_nhds_zero
    have := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp h0
    simpa [Real.log_one, Function.comp_def] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hex1 : (0:ℝ) < Real.exp x - 1 := by
      have : (1:ℝ) < Real.exp x := Real.one_lt_exp_iff.mpr hx
      linarith
    have hfloorgt : Real.exp x - 1 < (⌊Real.exp x⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one (Real.exp x)
      push_cast at h
      linarith
    have heq : Real.log (1 - Real.exp (-x)) = Real.log (Real.exp x - 1) - x := by
      have hd : (1 - Real.exp (-x)) = (Real.exp x - 1) / Real.exp x := by
        rw [Real.exp_neg]; field_simp
      rw [hd, Real.log_div hex1.ne' (Real.exp_pos x).ne', Real.log_exp]
    rw [heq]
    have hmono : Real.log (Real.exp x - 1) ≤ Real.log ⌊Real.exp x⌋₊ :=
      Real.log_le_log hex1 hfloorgt.le
    linarith
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hfloorpos : (0:ℝ) < (⌊Real.exp x⌋₊ : ℝ) := by
      have h1 : 1 ≤ ⌊Real.exp x⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp hx.le)
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    have : Real.log ⌊Real.exp x⌋₊ ≤ x := by
      calc Real.log ⌊Real.exp x⌋₊
          ≤ Real.log (Real.exp x) := Real.log_le_log hfloorpos (Nat.floor_le (Real.exp_pos x).le)
        _ = x := Real.log_exp x
    linarith

/-- `log log⌊eˣ⌋ − log x → 0` as `x → ∞`.  Since `log⌊eˣ⌋/x = 1 + (log⌊eˣ⌋−x)/x → 1` (numerator `→ 0`,
denominator `→ ∞`), `log(log⌊eˣ⌋/x) → log 1 = 0`, and `log(log⌊eˣ⌋/x) = log log⌊eˣ⌋ − log x`. -/
lemma tendsto_log_log_floor_exp_sub_log :
    Tendsto (fun x => Real.log (Real.log ⌊Real.exp x⌋₊) - Real.log x) atTop (𝓝 0) := by
  have hratio : Tendsto (fun x => Real.log ⌊Real.exp x⌋₊ / x) atTop (𝓝 1) := by
    have hnum : Tendsto (fun x => (Real.log ⌊Real.exp x⌋₊ - x) / x) atTop (𝓝 0) :=
      tendsto_log_floor_exp_sub.div_atTop tendsto_id
    have hone : Tendsto (fun x => 1 + (Real.log ⌊Real.exp x⌋₊ - x) / x) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hnum
    refine hone.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp; ring
  have hlog := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hratio
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.log 2), eventually_gt_atTop 0] with x hx2 hx0
  have he2 : (2:ℝ) < Real.exp x := by
    have h := Real.exp_lt_exp.mpr hx2
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
  have hfloor2 : (2:ℝ) ≤ (⌊Real.exp x⌋₊ : ℝ) := by
    have : (2:ℕ) ≤ ⌊Real.exp x⌋₊ := Nat.le_floor (by exact_mod_cast he2.le)
    exact_mod_cast this
  have hlogpos : 0 < Real.log ⌊Real.exp x⌋₊ := Real.log_pos (by linarith)
  simp only [Function.comp_apply]
  rw [Real.log_div hlogpos.ne' hx0.ne']

/-- **The Tauberian-error remainder `r(x) := primeRecipSum⌊eˣ⌋ − log x − M → 0`** as `x → ∞`.
Writes `r(x) = (primeRecipSum⌊eˣ⌋ − log log⌊eˣ⌋ − M) + (log log⌊eˣ⌋ − log x)`, both summands `→ 0`
(`tendsto_primeRecipSum_floor_exp` and `tendsto_log_log_floor_exp_sub_log`).  This is the input `f`
to the Abelian final-value crux `tendsto_sub_one_mul_integral_abelian`. -/
lemma tendsto_floorExpRemainder :
    Tendsto (fun x => primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM) atTop (𝓝 0) := by
  have h1 := tendsto_primeRecipSum_floor_exp.sub_const meisselMertensM
  rw [sub_self] at h1
  have hsum := h1.add tendsto_log_log_floor_exp_sub_log
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with x
  ring

/-! ### Limit B, assembled — `primeZeta s + log(s−1) → M − γ`. -/

open MeasureTheory in
/-- **Limit B** (the Tauberian limit), now fully proven: `primeZeta s + log(s−1) → M − γ` as `s→1⁺`.

Assembly of the `eˣ`-form spine: `primeZeta s = (s−1)∫_0^∞ primeRecipSum⌊eˣ⌋·e^{−(s−1)x}`
(`primeZeta_eq_abel_integral_exp`); split the integrand `primeRecipSum⌊eˣ⌋ = log x + M + r(x)` into the
three integrable pieces, giving `primeZeta s = (−γ−log(s−1)) + M + (s−1)∫_0^∞ r·e^{−(s−1)x}`.  The error
`(s−1)∫_0^∞ r·e^{−(s−1)x} → 0` is the Abelian final-value crux `tendsto_sub_one_mul_integral_abelian`
applied to `r → 0` (`tendsto_floorExpRemainder`).  Net: `primeZeta s + log(s−1) → M − γ`. -/
theorem tendsto_primeZeta_add_logSub_limitB :
    Tendsto (fun s : ℝ => primeZeta s + Real.log (s - 1)) (𝓝[>] 1)
      (𝓝 (meisselMertensM - Real.eulerMascheroniConstant)) := by
  -- Hypotheses for the Abelian final-value crux, with `f = r`.
  have hintf : ∀ δ : ℝ, 0 < δ → IntegrableOn
      (fun x => (primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM)
        * Real.exp (-(δ * x))) (Set.Ioi 0) := by
    intro δ hδ
    have hIps := integrableOn_primeRecipSum_exp hδ
    have hIlog := integrableOn_log_mul_exp_neg_mul hδ
    have hIM : IntegrableOn (fun x => meisselMertensM * Real.exp (-(δ * x))) (Set.Ioi 0) := by
      have h := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) 0
      have h' : IntegrableOn (fun x => Real.exp (-(δ * x))) (Set.Ioi 0) := by
        simpa only [neg_mul] using h
      exact h'.const_mul _
    exact ((hIps.sub hIlog).sub hIM).congr_fun
      (fun x _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hlocf : ∀ X : ℝ, IntegrableOn
      (fun x => |primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM|) (Set.Ioc 0 X) := by
    intro X
    have hps : IntegrableOn (fun x => primeRecipSum ⌊Real.exp x⌋₊) (Set.Ioc (0:ℝ) X) := by
      refine (integrableOn_const (C := 1 + X) (hs := measure_Ioc_lt_top.ne)).mono' ?_ ?_
      · exact ((Measurable.of_discrete (f := primeRecipSum)).comp
          Real.measurable_exp.nat_floor).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (primeRecipSum_nonneg _)]
        have hx0 : 0 < x := hx.1
        have hfloorpos : (0:ℝ) < (⌊Real.exp x⌋₊ : ℝ) := by
          have h1 : 1 ≤ ⌊Real.exp x⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp hx0.le)
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
        have hlog_le : Real.log ⌊Real.exp x⌋₊ ≤ x :=
          (Real.log_le_log hfloorpos (Nat.floor_le (Real.exp_pos x).le)).trans_eq (Real.log_exp x)
        have := primeRecipSum_le_one_add_log ⌊Real.exp x⌋₊
        linarith [hx.2]
    have hlogI : IntegrableOn (fun x => Real.log x) (Set.Ioc (0:ℝ) X) := by
      rcases le_total (0:ℝ) X with hX | hX
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mp
          intervalIntegral.intervalIntegrable_log'
      · rw [Set.Ioc_eq_empty (not_lt.mpr hX)]; exact integrableOn_empty
    have hMI : IntegrableOn (fun _ : ℝ => meisselMertensM) (Set.Ioc (0:ℝ) X) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    exact ((hps.sub hlogI).sub hMI).abs
  -- The error term `(s−1)∫_0^∞ r·e^{−(s−1)x} → 0`.
  have hshift : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun s : ℝ => s - 1) := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi, sub_pos]; exact hs
  have herr := (tendsto_sub_one_mul_integral_abelian tendsto_floorExpRemainder hintf hlocf).comp hshift
  have hmain := (tendsto_const_nhds
    (x := meisselMertensM - Real.eulerMascheroniConstant)).add herr
  rw [add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1:ℝ) < s := hs
  have hδ : (0:ℝ) < s - 1 := by linarith
  simp only [Function.comp_apply]
  -- the three integrable pieces (for the integral split)
  have hIps := integrableOn_primeRecipSum_exp hδ
  have hIlog := integrableOn_log_mul_exp_neg_mul hδ
  have hIM : IntegrableOn (fun x => meisselMertensM * Real.exp (-((s-1) * x))) (Set.Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -(s-1)) (by linarith) 0
    have h' : IntegrableOn (fun x => Real.exp (-((s-1) * x))) (Set.Ioi 0) := by
      simpa only [neg_mul] using h
    exact h'.const_mul _
  have hIr : IntegrableOn (fun x =>
      (primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM)
        * Real.exp (-((s-1) * x))) (Set.Ioi 0) :=
    ((hIps.sub hIlog).sub hIM).congr_fun
      (fun x _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hsplit : (∫ x in Set.Ioi (0:ℝ), primeRecipSum ⌊Real.exp x⌋₊ * Real.exp (-((s-1) * x)))
      = (∫ x in Set.Ioi (0:ℝ), Real.log x * Real.exp (-((s-1) * x)))
        + (∫ x in Set.Ioi (0:ℝ), meisselMertensM * Real.exp (-((s-1) * x)))
        + (∫ x in Set.Ioi (0:ℝ), (primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM)
            * Real.exp (-((s-1) * x))) := by
    have h1 : (∫ x in Set.Ioi (0:ℝ), primeRecipSum ⌊Real.exp x⌋₊ * Real.exp (-((s-1) * x)))
        = ∫ x in Set.Ioi (0:ℝ), (Real.log x * Real.exp (-((s-1) * x))
            + meisselMertensM * Real.exp (-((s-1) * x)))
          + (primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM)
              * Real.exp (-((s-1) * x)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
    have h2 : (∫ x in Set.Ioi (0:ℝ), (Real.log x * Real.exp (-((s-1) * x))
            + meisselMertensM * Real.exp (-((s-1) * x)))
          + (primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM)
              * Real.exp (-((s-1) * x)))
        = (∫ x in Set.Ioi (0:ℝ), Real.log x * Real.exp (-((s-1) * x))
            + meisselMertensM * Real.exp (-((s-1) * x)))
          + ∫ x in Set.Ioi (0:ℝ), (primeRecipSum ⌊Real.exp x⌋₊ - Real.log x - meisselMertensM)
              * Real.exp (-((s-1) * x)) :=
      integral_add (hIlog.add hIM) hIr
    have h3 : (∫ x in Set.Ioi (0:ℝ), Real.log x * Real.exp (-((s-1) * x))
            + meisselMertensM * Real.exp (-((s-1) * x)))
        = (∫ x in Set.Ioi (0:ℝ), Real.log x * Real.exp (-((s-1) * x)))
          + ∫ x in Set.Ioi (0:ℝ), meisselMertensM * Real.exp (-((s-1) * x)) :=
      integral_add hIlog hIM
    rw [h1, h2, h3]
  have vlog : (s - 1) * (∫ x in Set.Ioi (0:ℝ), Real.log x * Real.exp (-((s-1) * x)))
      = -Real.eulerMascheroniConstant - Real.log (s - 1) := sub_one_mul_integral_log_exp hs1
  have vM : (s - 1) * (∫ x in Set.Ioi (0:ℝ), meisselMertensM * Real.exp (-((s-1) * x)))
      = meisselMertensM := by
    rw [integral_const_mul, ← mul_assoc, mul_comm (s - 1) meisselMertensM, mul_assoc,
      sub_one_mul_integral_exp_neg hs1, mul_one]
  rw [primeZeta_eq_abel_integral_exp hs1, hsplit, mul_add, mul_add, vlog, vM]
  ring

/-! ### The classical `e^{−γ}` Mertens constant, UNCONDITIONAL. -/

/-- **`mertensThirdConst = −γ`**, unconditionally — `Limit B` is now a theorem
(`tendsto_primeZeta_add_logSub_limitB`), so the Tauberian hypothesis of
`mertensThirdConst_eq_neg_gamma_of_tauberian` is discharged. -/
theorem mertensThirdConst_eq_neg_gamma :
    mertensThirdConst = -Real.eulerMascheroniConstant :=
  mertensThirdConst_eq_neg_gamma_of_tauberian tendsto_primeZeta_add_logSub_limitB

/-- **Classical Mertens 3rd theorem, `e^{−γ}` form — UNCONDITIONAL.**
`∏_{p≤N}(1−1/p)·log N → e^{−γ}` as `N → ∞`, with `γ = Real.eulerMascheroniConstant`. -/
theorem mertens_third_classical_eGamma :
    Tendsto (fun N : ℕ => primeProd N * Real.log N) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
  mertens_third_classical_of_tauberian tendsto_primeZeta_add_logSub_limitB

end LeanFormalizations.Mertens
