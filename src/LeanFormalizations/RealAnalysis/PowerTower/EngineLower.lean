/-
# Infinite power tower (Euler 1783) — proof engine (LOWER half)

The oscillating regime `e^(-e) ≤ x < 1`. Here `f t = x^t` is **decreasing**, so the
tower `a n = ⁿx` is no longer monotone; instead the even subsequence
`E n = a (2n)` decreases and the odd subsequence `O n = a (2n+1)` increases, each
to a limit (`γ`, `β`). The pair `(β, γ)` is a 2-cycle of `f` (`f β = γ`, `f γ = β`).
Convergence of the whole tower is exactly `β = γ`.

`β = γ` for `x ≥ e^(-e)` is the genuine content of the lower bound — the
bifurcation at `x = e^(-e)`. **The crux is isolated as `two_cycle_collapse`** (see
its docstring for the precise analytic statement and why the naive tangent-line
argument is insufficient). Everything else here is machine-checked scaffolding:
continuity / monotonicity of `f`, monotone-bounded convergence of the two
subsequences, the limit relations, and the even/odd ⟹ whole reassembly.

Source: L. Euler, *De formulis exponentialibus replicatis* (1783); modern survey
L. Lóczi, "The strange properties of the infinite power tower", arXiv:1908.05559, §3.
-/
import LeanFormalizations.RealAnalysis.PowerTower.Defs

open Real Filter Topology

namespace LeanFormalizations.RealAnalysis.PowerTower

/-! ### THE CRUX (isolated axiom) -/

/-- **No nontrivial 2-cycle for `t ↦ x^t` when `x ≥ e^(-e)`** (with `0 < x < 1`).

If `β, γ > 0` form a 2-cycle of `f t = x^t` (`x^β = γ`, `x^γ = β`) and
`e^(-e) ≤ x`, then `β = γ`. This is the analytic heart of the lower bound for the
power tower's interval of convergence (the bifurcation at `x = e^(-e)`).

DISCLOSED AXIOM (debt, not a destination). The genuine difficulty: setting
`c = log x ∈ [-e, 0)`, the relations give `β log β = γ log γ`, and one must show the
map `g = f ∘ f` is non-expansive. The clean reason is that its derivative is bounded
by `|c|/e ≤ 1` — the same "maximum of `t·e^{-t}`" phenomenon (`add_one_le_exp`) that
drives the upper half. NOTE: the elementary "subtract the two tangent-line
inequalities at the fixed point" argument sketched in some references is INVALID
(one cannot subtract inequalities; numerically the tangent-at-`y` bound only pins
`log y` to an interval straddling `-1`, not below it). A rigorous proof needs the
slope-product / mean-value bound. Being attacked via Aristotle + the literature
(Lóczi §3); to be discharged into a machine-checked proof. -/
axiom two_cycle_collapse {x β γ : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hxe : eNegE ≤ x)
    (hβ : 0 < β) (hγ : 0 < γ) (h1 : x ^ β = γ) (h2 : x ^ γ = β) : β = γ

/-! ### Elementary scaffolding -/

variable {x : ℝ}

/-- Every tower term is positive. -/
theorem tower_pos (hx0 : 0 < x) (n : ℕ) : 0 < tower x n := by
  induction n with
  | zero => rw [tower_zero]; exact one_pos
  | succ k _ => rw [tower_succ]; exact Real.rpow_pos_of_pos hx0 _

/-- For `0 < x < 1`, every tower term after the first is `< 1` (the exponent
`tower x n` is positive and the base is in `(0,1)`). -/
theorem tower_succ_lt_one (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    tower x (n + 1) < 1 := by
  rw [tower_succ]
  exact Real.rpow_lt_one hx0.le hx1 (tower_pos hx0 n)

/-- `t ↦ x^t` is antitone (decreasing) for `0 < x ≤ 1`. -/
theorem f_antitone (hx0 : 0 < x) (hx1 : x ≤ 1) : Antitone (fun t : ℝ => x ^ t) :=
  fun _ _ hab => Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hab

/-- `g t = x^(x^t) = f (f t)` is monotone (increasing): a decreasing map composed
with itself. This makes both subsequences `a (2n)`, `a (2n+1)` monotone. -/
theorem g_mono (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Monotone (fun t : ℝ => x ^ (x ^ t)) :=
  fun _ _ hab => f_antitone hx0 hx1 (f_antitone hx0 hx1 hab)

/-- The two-step recurrence `a (n+2) = g (a n)`. -/
theorem tower_add_two (n : ℕ) : tower x (n + 2) = x ^ (x ^ tower x n) := by
  rw [tower_succ, tower_succ]

/-! ### Even/odd subsequence convergence -/

/-- If both the even and odd subsequences of `a` converge to the same `L`, then
`a` converges to `L`. (No mathlib lemma found; proved directly via the metric
characterization, splitting an index by parity.) -/
theorem tendsto_of_even_odd {a : ℕ → ℝ} {L : ℝ}
    (he : Tendsto (fun n => a (2 * n)) atTop (𝓝 L))
    (ho : Tendsto (fun n => a (2 * n + 1)) atTop (𝓝 L)) :
    Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at he ho ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := he ε hε
  obtain ⟨N2, hN2⟩ := ho ε hε
  refine ⟨2 * max N1 N2, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = k + k = 2 * k, with k ≥ N1
    have hkn : n = 2 * k := by omega
    have hk1 : k ≥ N1 := by omega
    have := hN1 k hk1
    rwa [hkn]
  · -- n = 2 * k + 1, with k ≥ N2
    have hk2 : k ≥ N2 := by omega
    have := hN2 k hk2
    rwa [hk]

/-! ### The lower-half engine -/

/-- **Convergence engine, lower half** (`e^(-e) ≤ x < 1`). The even subsequence
decreases to `γ`, the odd subsequence increases to `β`; `(β,γ)` is a 2-cycle of
`t ↦ x^t`. The crux `two_cycle_collapse` forces `β = γ`, so the whole tower
converges to the common value `L`, a fixed point of `t ↦ x^t`. -/
theorem tower_converges_lower (hxe : eNegE ≤ x) (hx1 : x < 1) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hcont : Continuous (fun t : ℝ => x ^ t) := Real.continuous_const_rpow (ne_of_gt hx0)
  -- two-step recurrences for the even / odd subsequences
  have hErec : ∀ n, tower x (2 * (n + 1)) = (fun t => x ^ (x ^ t)) (tower x (2 * n)) := by
    intro n
    have h : 2 * (n + 1) = (2 * n) + 2 := by ring
    rw [h, tower_add_two]
  have hOrec : ∀ n, tower x (2 * (n + 1) + 1) = (fun t => x ^ (x ^ t)) (tower x (2 * n + 1)) := by
    intro n
    have h : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [h, tower_add_two]
  -- EVEN subsequence is antitone
  have hgm := g_mono hx0 hx1.le
  have hE_anti : Antitone (fun n => tower x (2 * n)) := by
    apply antitone_nat_of_succ_le
    intro n
    induction n with
    | zero =>
        -- tower x 2 ≤ tower x 0 = 1
        have e1 : 2 * (0 + 1) = 2 := by norm_num
        have e0 : 2 * 0 = 0 := by norm_num
        show tower x (2 * (0 + 1)) ≤ tower x (2 * 0)
        rw [e1, e0, tower_zero]
        exact (tower_succ_lt_one hx0 hx1 1).le
    | succ k ih =>
        show tower x (2 * (k + 1 + 1)) ≤ tower x (2 * (k + 1))
        calc tower x (2 * (k + 1 + 1))
            = (fun t => x ^ (x ^ t)) (tower x (2 * (k + 1))) := hErec (k + 1)
          _ ≤ (fun t => x ^ (x ^ t)) (tower x (2 * k)) := hgm ih
          _ = tower x (2 * (k + 1)) := (hErec k).symm
  -- ODD subsequence is monotone
  have hO_mono : Monotone (fun n => tower x (2 * n + 1)) := by
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero =>
        -- tower x 1 ≤ tower x 3
        have e1 : 2 * 0 + 1 = 1 := by norm_num
        have e3 : 2 * (0 + 1) + 1 = 3 := by norm_num
        show tower x (2 * 0 + 1) ≤ tower x (2 * (0 + 1) + 1)
        rw [e1, e3, tower_one]
        have h2 : tower x 2 ≤ 1 := (tower_succ_lt_one hx0 hx1 1).le
        have h3 : tower x 3 = x ^ tower x 2 := tower_succ x 2
        rw [h3]
        calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ ≤ x ^ tower x 2 := Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le h2
    | succ k ih =>
        show tower x (2 * (k + 1) + 1) ≤ tower x (2 * (k + 1 + 1) + 1)
        calc tower x (2 * (k + 1) + 1)
            = (fun t => x ^ (x ^ t)) (tower x (2 * k + 1)) := hOrec k
          _ ≤ (fun t => x ^ (x ^ t)) (tower x (2 * (k + 1) + 1)) := hgm ih
          _ = tower x (2 * (k + 1 + 1) + 1) := (hOrec (k + 1)).symm
  -- bounds
  have hE_bdd : BddBelow (Set.range (fun n => tower x (2 * n))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (tower_pos hx0 _).le⟩
  have hO_bdd : BddAbove (Set.range (fun n => tower x (2 * n + 1))) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (tower_succ_lt_one hx0 hx1 _).le⟩
  -- limits γ (even, infimum) and β (odd, supremum)
  set γ := ⨅ n, tower x (2 * n) with hγdef
  set β := ⨆ n, tower x (2 * n + 1) with hβdef
  have hγ_lim : Tendsto (fun n => tower x (2 * n)) atTop (𝓝 γ) :=
    tendsto_atTop_ciInf hE_anti hE_bdd
  have hβ_lim : Tendsto (fun n => tower x (2 * n + 1)) atTop (𝓝 β) :=
    tendsto_atTop_ciSup hO_mono hO_bdd
  -- limit relation  β = x ^ γ   (from  a (2n+1) = x ^ a (2n))
  have hOeq : (fun n => tower x (2 * n + 1)) = (fun n => x ^ tower x (2 * n)) := by
    funext n; rw [tower_succ]
  have hβγ : β = x ^ γ := by
    have hlim2 : Tendsto (fun n => x ^ tower x (2 * n)) atTop (𝓝 (x ^ γ)) :=
      (hcont.tendsto γ).comp hγ_lim
    have hβ' := hβ_lim
    rw [hOeq] at hβ'
    exact tendsto_nhds_unique hβ' hlim2
  -- limit relation  γ = x ^ β   (from  a (2n+2) = x ^ a (2n+1), shift)
  have hEshift : Tendsto (fun n => tower x (2 * (n + 1))) atTop (𝓝 γ) :=
    hγ_lim.comp (tendsto_add_atTop_nat 1)
  have hEeq : (fun n => tower x (2 * (n + 1))) = (fun n => x ^ tower x (2 * n + 1)) := by
    funext n
    have h : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h, tower_succ]
  have hγβ : γ = x ^ β := by
    have hlim2 : Tendsto (fun n => x ^ tower x (2 * n + 1)) atTop (𝓝 (x ^ β)) :=
      (hcont.tendsto β).comp hβ_lim
    have hE' := hEshift
    rw [hEeq] at hE'
    exact tendsto_nhds_unique hE' hlim2
  -- positivity of the two limits, from the relations
  have hβpos : 0 < β := by rw [hβγ]; exact Real.rpow_pos_of_pos hx0 _
  have hγpos : 0 < γ := by rw [hγβ]; exact Real.rpow_pos_of_pos hx0 _
  -- THE CRUX: the 2-cycle collapses
  have hβeqγ : β = γ :=
    two_cycle_collapse hx0 hx1 hxe hβpos hγpos hγβ.symm hβγ.symm
  -- conclude: the whole tower converges to L := β = γ
  refine ⟨β, ?_, ?_⟩
  · apply tendsto_of_even_odd
    · -- even subsequence → β (= γ)
      rw [hβeqγ]; exact hγ_lim
    · exact hβ_lim
  · -- x ^ β = β : indeed x ^ β = γ = β
    rw [← hγβ, hβeqγ]

end LeanFormalizations.RealAnalysis.PowerTower
