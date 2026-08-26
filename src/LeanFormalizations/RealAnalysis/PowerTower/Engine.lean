/-
# Infinite power tower (Euler 1783) — proof engine (upper half)

The real proofs behind the two load-bearing statements of `Statement.lean`. Per the
repo's audit-surface doctrine the engine lives in this sibling and `Statement.lean`
delegates to `tower_converges_engine` / `tower_diverges_engine`.

Everything here is **elementary** — no calculus, no derivatives, no critical
points. The single analytic input is `Real.add_one_le_exp` (`x + 1 ≤ eˣ`), from
which the whole "the maximum of `t^(1/t)` is `e^(1/e)`" phenomenon falls out as the
inequality `log L ≤ L / e`. The convergence side is monotone-bounded convergence to
a fixed point; the divergence side is "monotone + no fixed point above the
threshold ⟹ unbounded ⟹ atTop".

Source: L. Euler, *De formulis exponentialibus replicatis* (1783); modern survey
L. Lóczi, "The strange properties of the infinite power tower", arXiv:1908.05559.
-/
import LeanFormalizations.RealAnalysis.PowerTower.Defs

open Real Filter Topology

namespace LeanFormalizations.RealAnalysis.PowerTower

/-! ### Shared elementary helpers -/

/-- `log L ≤ L / e` for `L > 0`. This is the entire "max of `t^(1/t)` is at
`t = e`" fact, derived with no calculus straight from `x + 1 ≤ eˣ`. -/
theorem log_le_div_e {L : ℝ} (hL : 0 < L) : Real.log L ≤ L / Real.exp 1 := by
  have h := Real.add_one_le_exp (Real.log L - 1)
  rw [Real.exp_sub, Real.exp_log hL] at h
  linarith

/-- A positive fixed point forces the base below the endpoint: if `x^L = L` with
`x, L > 0`, then `x ≤ e^(1/e)`. (Take logs: `L·log x = log L ≤ L/e`, divide by
`L > 0` to get `log x ≤ 1/e`, then apply `exp`.) -/
theorem base_le_eInvE {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (h : x ^ L = L) :
    x ≤ eInvE := by
  have hlog : L * Real.log x = Real.log L := by
    rw [← Real.log_rpow hx, h]
  have hlogx : Real.log x ≤ 1 / Real.exp 1 := by
    have hd := log_le_div_e hL
    rw [← hlog, div_eq_mul_one_div] at hd
    exact le_of_mul_le_mul_left hd hL
  calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ ≤ Real.exp (1 / Real.exp 1) := Real.exp_le_exp.mpr hlogx
    _ = eInvE := rfl

/-- For `1 ≤ x`, consecutive tower terms are increasing: `ⁿx ≤ ⁿ⁺¹x`. -/
theorem tower_le_succ {x : ℝ} (hx : 1 ≤ x) : ∀ n, tower x n ≤ tower x (n + 1) := by
  intro n
  induction n with
  | zero => rw [tower_zero, tower_one]; exact hx
  | succ k ih =>
      rw [tower_succ, tower_succ]
      exact Real.rpow_le_rpow_of_exponent_le hx ih

/-- For `1 ≤ x` the tower `n ↦ ⁿx` is monotone (the increasing regime). -/
theorem tower_mono {x : ℝ} (hx : 1 ≤ x) : Monotone (tower x) :=
  monotone_nat_of_le_succ (tower_le_succ hx)

/-- `1 < e^(1/e)`: the endpoint exceeds `1` since `1/e > 0`. -/
theorem one_lt_eInvE : 1 < eInvE := by
  rw [eInvE]; exact Real.one_lt_exp_iff.mpr (by positivity)

/-- On `[1, e^(1/e)]` every tower term is bounded by `e`. Induction: the base case
is `1 ≤ e`, and the step uses monotonicity of `t ↦ x^t` together with
`x ≤ e^(1/e)` and the endpoint identity `(e^(1/e))^e = e`. -/
theorem tower_le_exp_one {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ eInvE) :
    ∀ n, tower x n ≤ Real.exp 1 := by
  intro n
  induction n with
  | zero => rw [tower_zero]; exact Real.one_le_exp (by norm_num)
  | succ k ih =>
      rw [tower_succ]
      calc x ^ tower x k
          ≤ x ^ Real.exp 1 := Real.rpow_le_rpow_of_exponent_le hx1 ih
        _ ≤ eInvE ^ Real.exp 1 := Real.rpow_le_rpow (by linarith) hx2 (Real.exp_pos 1).le
        _ = Real.exp 1 := endpoint_fixed_point

/-- A monotone, bounded tower converges to a fixed point of `t ↦ x^t` that is `≥ 1`.
This is the shared core of both engines (convergence uses it directly; divergence
uses its contrapositive). -/
theorem exists_fixedpoint_of_bddAbove {x : ℝ} (hx1 : 1 ≤ x)
    (hbdd : BddAbove (Set.range (tower x))) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L ∧ 1 ≤ L := by
  have hmono := tower_mono hx1
  set L := ⨆ n, tower x n with hLdef
  have hL : Tendsto (tower x) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  refine ⟨L, hL, ?_, ?_⟩
  · -- x ^ L = L, by uniqueness of limits applied to the shifted sequence
    have hshift : Tendsto (fun n => tower x (n + 1)) atTop (𝓝 L) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hrpow : Tendsto (fun n => x ^ tower x n) atTop (𝓝 (x ^ L)) :=
      Tendsto.rpow tendsto_const_nhds hL (Or.inl (ne_of_gt hx0))
    have heq : (fun n => tower x (n + 1)) = (fun n => x ^ tower x n) := by
      funext n; rw [tower_succ]
    rw [heq] at hshift
    exact (tendsto_nhds_unique hshift hrpow).symm
  · -- 1 ≤ L, since tower x 0 = 1 ≤ ⨆
    have := le_ciSup hbdd 0
    simpa using this

/-! ### The two engines -/

/-- **Convergence engine** (`1 ≤ x ≤ e^(1/e)`). The tower is monotone and bounded
by `e`, hence converges to a fixed point `L ∈ [1, e]` of `t ↦ x^t`. -/
theorem tower_converges_engine {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ eInvE) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L ∧ 1 ≤ L ∧ L ≤ Real.exp 1 := by
  have hbd := tower_le_exp_one hx1 hx2
  have hbdd : BddAbove (Set.range (tower x)) :=
    ⟨Real.exp 1, by rintro _ ⟨n, rfl⟩; exact hbd n⟩
  obtain ⟨L, hL, hfix, hL1⟩ := exists_fixedpoint_of_bddAbove hx1 hbdd
  exact ⟨L, hL, hfix, hL1, le_of_tendsto' hL hbd⟩

/-- **Divergence engine** (`x > e^(1/e)`). Here `x > 1`, so the tower is monotone.
If it were bounded it would have a fixed point `L ≥ 1`, forcing `x ≤ e^(1/e)`
(`base_le_eInvE`) — contradiction. So it is unbounded, and monotone + unbounded ⟹
`atTop`. -/
theorem tower_diverges_engine {x : ℝ} (hx : eInvE < x) :
    Tendsto (tower x) atTop atTop := by
  have hx1 : 1 ≤ x := le_of_lt (lt_trans one_lt_eInvE hx)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hmono := tower_mono hx1
  have hub : ∀ b, ∃ n, b ≤ tower x n := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb⟩ := hcon
    have hbdd : BddAbove (Set.range (tower x)) :=
      ⟨b, by rintro _ ⟨n, rfl⟩; exact (hb n).le⟩
    obtain ⟨L, _hL, hfix, hL1⟩ := exists_fixedpoint_of_bddAbove hx1 hbdd
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    have := base_le_eInvE hx0 hLpos hfix
    linarith
  exact tendsto_atTop_atTop_of_monotone hmono hub

end LeanFormalizations.RealAnalysis.PowerTower
