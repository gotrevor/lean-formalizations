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
argument is insufficient); it is itself fully machine-checked, with no axiom. The rest
here is machine-checked scaffolding:
continuity / monotonicity of `f`, monotone-bounded convergence of the two
subsequences, the limit relations, and the even/odd ⟹ whole reassembly.

Source: L. Euler, *De formulis exponentialibus replicatis* (1783); modern survey
L. Lóczi, "The strange properties of the infinite power tower", arXiv:1908.05559, §3.
-/
import LeanFormalizations.RealAnalysis.PowerTower.Defs

open Real Filter Topology

namespace LeanFormalizations.RealAnalysis.PowerTower

/-! ### THE CRUX — no nontrivial 2-cycle for `t ↦ x^t` on `[e^(-e), 1)`

Fully machine-checked (NO axiom). The heart is that the second iterate
`g = f ∘ f` (`f t = x^t`) is non-expansive: its derivative
`g'(t) = (log x)² · x^(x^t) · x^t = c²·e^{c(e^{ct}+t)}` (`c = log x < 0`) is bounded
by `|c|/e ≤ 1` for `x ≥ e^(-e)`. This rides on the SAME `add_one_le_exp`
"maximum of `t·e^{-t}`" phenomenon as the upper half (`exp_mul_add_ge` below). For
`x > e^(-e)` the bound is `< 1` uniformly, so `g` is a contraction (Banach ⟹ unique
fixed point ⟹ `β = γ`); at the boundary `x = e^(-e)` the bound is `1` with strict
inequality off the single critical point `t = 1/e`, and an antitone-on-interval
argument still forces `β = γ`.

(NB: the "subtract the two tangent-line inequalities at the fixed point" sketch in
some references is INVALID — one cannot subtract inequalities, and the tangent-at-`y`
bound only pins `log y` to an interval *straddling* `-1`. The slope/derivative bound
here is the correct mechanism.) -/

/-- The elementary heart: for `c < 0`, `exp(c t) + t ≥ (1 + log(-c))/(-c)`, the
minimum of `t ↦ e^{ct}+t` (attained at `t = log(-c)/(-c)`). Pure `add_one_le_exp`;
the `t`-terms cancel because `c + (-c) = 0`. -/
theorem exp_mul_add_ge {c : ℝ} (hc : c < 0) (t : ℝ) :
    (1 + Real.log (-c)) / (-c) ≤ Real.exp (c * t) + t := by
  have hcpos : 0 < -c := by linarith
  have htan := Real.add_one_le_exp (c * t + Real.log (-c))
  rw [Real.exp_add, Real.exp_log hcpos] at htan
  rw [div_le_iff₀ hcpos]
  nlinarith [htan]

/-- Strict version of `exp_mul_add_ge`, off the unique critical point. -/
theorem exp_mul_add_gt {c : ℝ} (hc : c < 0) {t : ℝ}
    (ht : c * t + Real.log (-c) ≠ 0) :
    (1 + Real.log (-c)) / (-c) < Real.exp (c * t) + t := by
  have hcpos : 0 < -c := by linarith
  have htan := Real.add_one_lt_exp ht
  rw [Real.exp_add, Real.exp_log hcpos] at htan
  rw [div_lt_iff₀ hcpos]; nlinarith [htan]

/-- The derivative magnitude bound `|g'(t)| ≤ (-log x)/e` for `0 < x < 1`. The whole
"bifurcation at `e^(-e)`" reduces to this, via `exp_mul_add_ge`. -/
theorem deriv_bound (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (t : ℝ) :
    |(x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x)| ≤ (-Real.log x) * Real.exp (-1) := by
  set c := Real.log x with hc
  have hcneg : c < 0 := by rw [hc]; exact Real.log_neg hx hx1
  have hcne : c ≠ 0 := ne_of_lt hcneg
  have hcpos : 0 < -c := by linarith
  have hxt : x ^ t = Real.exp (c * t) := by rw [hc, Real.rpow_def_of_pos hx]
  have hxxt : x ^ (x ^ t) = Real.exp (c * Real.exp (c * t)) := by
    rw [hc, Real.rpow_def_of_pos hx, hxt]
  have hval : (x ^ (x ^ t) * c) * (x ^ t * c)
      = c ^ 2 * Real.exp (c * (Real.exp (c * t) + t)) := by
    rw [hxxt, hxt, mul_add, Real.exp_add]; ring
  rw [hval]
  have hpos : 0 < c ^ 2 * Real.exp (c * (Real.exp (c * t) + t)) := by positivity
  rw [abs_of_pos hpos]
  have hm := exp_mul_add_ge hcneg t
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hm hcneg.le)
  have hcc : c / (-c) = -1 := by rw [div_neg, div_self hcne]
  have hkey : c * ((1 + Real.log (-c)) / (-c)) = -(1 + Real.log (-c)) := by
    calc c * ((1 + Real.log (-c)) / (-c)) = c / (-c) * (1 + Real.log (-c)) := by ring
      _ = -1 * (1 + Real.log (-c)) := by rw [hcc]
      _ = -(1 + Real.log (-c)) := by ring
  rw [hkey] at hexp
  have hrhs : Real.exp (-(1 + Real.log (-c))) = Real.exp (-1) / (-c) := by
    rw [show -(1 + Real.log (-c)) = (-1) - Real.log (-c) by ring, Real.exp_sub, Real.exp_log hcpos]
  rw [hrhs] at hexp
  calc c ^ 2 * Real.exp (c * (Real.exp (c * t) + t))
      ≤ c ^ 2 * (Real.exp (-1) / (-c)) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (-c) * Real.exp (-1) := by field_simp

/-- `g = f ∘ f` has derivative `(x^(x^t)·log x)·(x^t·log x)` at `t`. -/
theorem hasDeriv_g (x : ℝ) (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun t => x ^ (x ^ t)) ((x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x)) t :=
  (Real.hasStrictDerivAt_const_rpow hx (x ^ t)).hasDerivAt.comp t
    (Real.hasStrictDerivAt_const_rpow hx t).hasDerivAt

/-- **Crux, interior `x > e^(-e)`.** Here `g` is a strict contraction (`|g'| ≤
(-log x)/e < 1`), so its two fixed points `β, γ` coincide (Banach). -/
theorem two_cycle_collapse_of_lt {x β γ : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hxe : eNegE < x) (h1 : x ^ β = γ) (h2 : x ^ γ = β) : β = γ := by
  set g : ℝ → ℝ := fun t => x ^ (x ^ t) with hg
  set K : NNReal := Real.toNNReal ((-Real.log x) * Real.exp (-1)) with hK
  have hKnonneg : 0 ≤ (-Real.log x) * Real.exp (-1) := by
    have h := Real.log_neg hx0 hx1
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hdiff : Differentiable ℝ g := fun t => (hasDeriv_g x hx0 t).differentiableAt
  have hbound : ∀ t, ‖deriv g t‖₊ ≤ K := by
    intro t
    have hderiv : deriv g t = (x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x) :=
      (hasDeriv_g x hx0 t).deriv
    rw [← NNReal.coe_le_coe, coe_nnnorm, hderiv, Real.norm_eq_abs, hK,
        Real.coe_toNNReal _ hKnonneg]
    exact deriv_bound x hx0 hx1 t
  have hLip : LipschitzWith K g := lipschitzWith_of_nnnorm_deriv_le hdiff hbound
  have hK1 : K < 1 := by
    rw [hK, ← Real.toNNReal_one]
    refine (Real.toNNReal_lt_toNNReal_iff (by norm_num)).mpr ?_
    have hlog : Real.log eNegE < Real.log x :=
      Real.log_lt_log (by rw [eNegE]; exact Real.exp_pos _) hxe
    rw [eNegE, Real.log_exp] at hlog
    rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos 1), one_mul]
    linarith
  have hcontr : ContractingWith K g := ⟨hK1, hLip⟩
  have hfixβ : Function.IsFixedPt g β := by show x ^ (x ^ β) = β; rw [h1, h2]
  have hfixγ : Function.IsFixedPt g γ := by show x ^ (x ^ γ) = γ; rw [h2, h1]
  rcases hcontr.eq_or_edist_eq_top_of_fixedPoints hfixβ hfixγ with h | h
  · exact h
  · exact absurd h (edist_ne_top β γ)

/-- Strict derivative bound at the boundary `x = e^(-e)`: `g'(t) < 1` for `t ≠ 1/e`
(the unique critical point at the boundary). -/
theorem deriv_lt_one_boundary {t : ℝ} (ht : t ≠ Real.exp (-1)) :
    (eNegE ^ (eNegE ^ t) * Real.log eNegE) * (eNegE ^ t * Real.log eNegE) < 1 := by
  set x := eNegE with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hxc : Real.log x = -Real.exp 1 := by rw [hxdef, eNegE, Real.log_exp]
  set c := Real.log x with hc
  have hcneg : c < 0 := by rw [hxc]; linarith [Real.exp_pos 1]
  have hcpos : 0 < -c := by linarith
  have hxt : x ^ t = Real.exp (c * t) := by rw [hc, Real.rpow_def_of_pos hx0]
  have hxxt : x ^ (x ^ t) = Real.exp (c * Real.exp (c * t)) := by
    rw [hc, Real.rpow_def_of_pos hx0, hxt]
  have hval : (x ^ (x ^ t) * c) * (x ^ t * c)
      = c ^ 2 * Real.exp (c * (Real.exp (c * t) + t)) := by
    rw [hxxt, hxt, mul_add, Real.exp_add]; ring
  rw [hval]
  have htstar : Real.log (-c) / (-c) = Real.exp (-1) := by
    rw [hxc, neg_neg, Real.log_exp, Real.exp_neg]; ring
  have hcne0 : c ≠ 0 := ne_of_lt hcneg
  have hne : c * t + Real.log (-c) ≠ 0 := by
    intro h0
    apply ht
    have ht_eq : t = Real.log (-c) / (-c) := by
      rw [eq_div_iff (by linarith : (-c) ≠ 0)]
      linear_combination -h0
    rw [ht_eq, htstar]
  have hgt := exp_mul_add_gt hcneg hne
  have hexp := Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hgt hcneg)
  have hcc : c / (-c) = -1 := by rw [div_neg, div_self hcne0]
  have hkey : c * ((1 + Real.log (-c)) / (-c)) = -(1 + Real.log (-c)) := by
    calc c * ((1 + Real.log (-c)) / (-c)) = c / (-c) * (1 + Real.log (-c)) := by ring
      _ = -1 * (1 + Real.log (-c)) := by rw [hcc]
      _ = -(1 + Real.log (-c)) := by ring
  rw [hkey] at hexp
  have hrhs : Real.exp (-(1 + Real.log (-c))) = Real.exp (-1) / (-c) := by
    rw [show -(1 + Real.log (-c)) = (-1) - Real.log (-c) by ring, Real.exp_sub, Real.exp_log hcpos]
  rw [hrhs] at hexp
  have hfin : c ^ 2 * Real.exp (c * (Real.exp (c * t) + t)) < (-c) * Real.exp (-1) := by
    calc c ^ 2 * Real.exp (c * (Real.exp (c * t) + t))
        < c ^ 2 * (Real.exp (-1) / (-c)) := by
          apply mul_lt_mul_of_pos_left hexp; positivity
      _ = (-c) * Real.exp (-1) := by field_simp
  have hone : (-c) * Real.exp (-1) = 1 := by
    rw [hxc, neg_neg, ← Real.exp_add]; norm_num
  linarith [hfin, hone]

/-- **Crux, boundary `x = e^(-e)`.** Here `g` is non-expansive with `g' < 1` off the
single point `1/e`; if `β ≠ γ` were a 2-cycle then `h = g - id` is `0` on the whole
interval `(β,γ)`, forcing `g' = 1` there — impossible since `g' < 1` away from `1/e`. -/
theorem two_cycle_collapse_boundary {β γ : ℝ}
    (h1 : eNegE ^ β = γ) (h2 : eNegE ^ γ = β) : β = γ := by
  set x := eNegE with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    have hxe : x = Real.exp (-Real.exp 1) := hxdef
    rw [hxe, Real.exp_lt_one_iff]; linarith [Real.exp_pos 1]
  set g : ℝ → ℝ := fun t => x ^ (x ^ t) with hg
  set h : ℝ → ℝ := fun t => g t - t with hh
  have hHh : ∀ t, HasDerivAt h
      ((x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x) - 1) t :=
    fun t => (hasDeriv_g x hx0 t).sub (hasDerivAt_id t)
  have hg_le : ∀ t : ℝ, (x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x) ≤ 1 := by
    intro t
    have hb := deriv_bound x hx0 hx1 t
    have hone : (-Real.log x) * Real.exp (-1) = 1 := by
      rw [hxdef]; simp only [eNegE, Real.log_exp, neg_neg, ← Real.exp_add]; norm_num
    rw [hone] at hb
    exact (abs_le.mp hb).2
  have hh_anti : Antitone h := by
    apply antitone_of_deriv_nonpos (fun t => (hHh t).differentiableAt)
    intro t
    rw [(hHh t).deriv]; linarith [hg_le t]
  have hfixβ : h β = 0 := by simp only [hh, hg]; rw [h1, h2]; ring
  have hfixγ : h γ = 0 := by simp only [hh, hg]; rw [h2, h1]; ring
  have key : ∀ a b : ℝ, a < b → h a = 0 → h b = 0 → False := by
    intro a b hab ha hb
    have hconst : ∀ s ∈ Set.Ioo a b, h s = 0 := by
      intro s hs
      have h1' := hh_anti (le_of_lt hs.2)
      have h2' := hh_anti (le_of_lt hs.1)
      rw [hb] at h1'; rw [ha] at h2'; linarith
    obtain ⟨t₀, ht₀mem, ht₀ne⟩ : ∃ t₀ ∈ Set.Ioo a b, t₀ ≠ Real.exp (-1) := by
      obtain ⟨t₀, ht₀⟩ :=
        ((Set.Ioo_infinite hab).diff (Set.finite_singleton (Real.exp (-1)))).nonempty
      exact ⟨t₀, ht₀.1, ht₀.2⟩
    have hev : h =ᶠ[𝓝 t₀] (fun _ => 0) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht₀mem.1 ht₀mem.2) (fun s hs => hconst s hs)
    have hderiv0 : deriv h t₀ = 0 := by rw [hev.deriv_eq]; simp
    rw [(hHh t₀).deriv] at hderiv0
    have hg_lt := deriv_lt_one_boundary (t := t₀) ht₀ne
    rw [← hxdef] at hg_lt
    linarith
  rcases lt_trichotomy β γ with hlt | heq | hgt
  · exact (key β γ hlt hfixβ hfixγ).elim
  · exact heq
  · exact (key γ β hgt hfixγ hfixβ).elim

/-- **The crux, full closed interval `[e^(-e), 1)`** (machine-checked, NO axiom).
No nontrivial 2-cycle of `t ↦ x^t`: if `β, γ > 0`, `x^β = γ`, `x^γ = β` and
`e^(-e) ≤ x < 1`, then `β = γ`. Splits into the interior contraction
(`two_cycle_collapse_of_lt`) and the boundary (`two_cycle_collapse_boundary`). -/
theorem two_cycle_collapse {x β γ : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hxe : eNegE ≤ x)
    (_hβ : 0 < β) (_hγ : 0 < γ) (h1 : x ^ β = γ) (h2 : x ^ γ = β) : β = γ := by
  rcases eq_or_lt_of_le hxe with heq | hlt
  · -- x = eNegE (boundary)
    subst heq
    exact two_cycle_collapse_boundary h1 h2
  · -- eNegE < x (interior)
    exact two_cycle_collapse_of_lt hx0 hx1 hlt h1 h2

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

/-- **Shared subsequence data for the oscillating regime** (`e^(-e) ≤ x < 1`). The
even subsequence `a (2n)` decreases to `γ`, the odd subsequence `a (2n+1)` increases
to `β`; `(β,γ)` is a 2-cycle of `t ↦ x^t` (`x^γ = β`, `x^β = γ`). Both the
convergence proof (`tower_converges_lower`, which adds `two_cycle_collapse` to force
`β = γ`) and the divergence proof (`tower_diverges_lower`, which shows `β < γ`) build
on this construction, so it is factored out here. Needs only `0 < x < 1` — the
lower endpoint `e^(-e)` enters only via the *crux* (`two_cycle_collapse`), not the
subsequence construction. -/
theorem tower_subseq_limits (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ β γ : ℝ,
      Tendsto (fun n => tower x (2 * n)) atTop (𝓝 γ) ∧
      Tendsto (fun n => tower x (2 * n + 1)) atTop (𝓝 β) ∧
      γ = x ^ β ∧ β = x ^ γ ∧ 0 < β ∧ 0 < γ := by
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
  exact ⟨β, γ, hγ_lim, hβ_lim, hγβ, hβγ, hβpos, hγpos⟩

/-- **Convergence engine, lower half** (`e^(-e) ≤ x < 1`). The crux
`two_cycle_collapse` forces the 2-cycle endpoints `β = γ`, so the whole tower
converges to the common value `L`, a fixed point of `t ↦ x^t`. -/
theorem tower_converges_lower (hxe : eNegE ≤ x) (hx1 : x < 1) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  obtain ⟨β, γ, hγ_lim, hβ_lim, hγβ, hβγ, hβpos, hγpos⟩ := tower_subseq_limits hx0 hx1
  have hβeqγ : β = γ :=
    two_cycle_collapse hx0 hx1 hxe hβpos hγpos hγβ.symm hβγ.symm
  refine ⟨β, ?_, ?_⟩
  · apply tendsto_of_even_odd
    · rw [hβeqγ]; exact hγ_lim
    · exact hβ_lim
  · rw [← hγβ, hβeqγ]

/-! ### Divergence below the lower endpoint — the genuine attracting 2-cycle

For `0 < x < e^(-e)` the unique fixed point `y` of `f t = x^t` (which lies in
`(0,1)`) is **repelling**: `g'(y) = (log y)^2 > 1` because `x < e^(-e)` forces
`log y < -1`. So `g = f∘f` has *three* fixed points near `y` — a repelling `y`
flanked by two attracting ones `β₀ < y < γ₀` (a genuine 2-cycle of `f`). The
even/odd subsequences of the tower are trapped on opposite sides
(`a(2n) ≥ γ₀ > y > β₀ ≥ a(2n+1)`), so their limits are *distinct* and the tower
cannot converge. This is the sharp converse of `two_cycle_collapse`. -/

/-- For `0 < x < 1`, the map `t ↦ x^t` has a fixed point in `(0,1)`: by the IVT on
`x^t - t`, which is `1 > 0` at `t = 0` and `x - 1 < 0` at `t = 1`. -/
theorem fixedpoint_exists (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ y : ℝ, 0 < y ∧ y < 1 ∧ x ^ y = y := by
  have hcont : ContinuousOn (fun t : ℝ => x ^ t - t) (Set.Icc 0 1) :=
    ((Real.continuous_const_rpow (ne_of_gt hx0)).sub continuous_id).continuousOn
  have h0 : (fun t : ℝ => x ^ t - t) 1 < 0 := by
    simp only [Real.rpow_one]; linarith
  have h1 : (0:ℝ) < (fun t : ℝ => x ^ t - t) 0 := by
    simp only [Real.rpow_zero]; norm_num
  obtain ⟨y, hy_mem, hy_eq⟩ :=
    intermediate_value_Ioo' (by norm_num : (0:ℝ) ≤ 1) hcont ⟨h0, h1⟩
  refine ⟨y, hy_mem.1, hy_mem.2, ?_⟩
  have : x ^ y - y = 0 := hy_eq
  linarith

/-- **The repelling seed.** For `0 < x < e^(-e)`, the fixed point `y` of `t ↦ x^t`
satisfies `log y < -1`. Equivalent to `y < 1/e`, the genuine content of the
bifurcation at `e^(-e)`: from `y·log x = log y` and `log x < -e`, if instead
`log y ≥ -1` then `y ≥ 1/e` so `-y·e ≤ -1`, forcing `log y < -1`, a contradiction. -/
theorem log_fixedpoint_lt_neg_one (hx0 : 0 < x) (hlt : x < eNegE)
    {y : ℝ} (hy0 : 0 < y) (hfix : x ^ y = y) : Real.log y < -1 := by
  have hlogx : Real.log x < -Real.exp 1 := by
    have h := Real.log_lt_log hx0 hlt
    rwa [eNegE, Real.log_exp] at h
  have hlogy : Real.log y = y * Real.log x := by
    conv_lhs => rw [← hfix]
    rw [Real.log_rpow hx0]
  have hA : Real.log y < -(y * Real.exp 1) := by
    have h := mul_lt_mul_of_pos_left hlogx hy0
    rw [hlogy]; nlinarith [h]
  by_contra hcon
  push Not at hcon
  have hyge : Real.exp (-1) ≤ y := by
    have h := Real.exp_le_exp.mpr hcon
    rwa [Real.exp_log hy0] at h
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have hprod : (1:ℝ) ≤ y * Real.exp 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hyge (Real.exp_pos 1).le, he]
  linarith [hA, hprod, hcon]

/-- **The genuine attracting 2-cycle.** For `0 < x < e^(-e)` there are
`β₀ < γ₀` with `x^(x^β₀) = β₀`, `x^(x^γ₀) = γ₀` (fixed points of `g = f∘f`),
`x < β₀` and `γ₀ < 1`. These bracket the repelling fixed point `y` and trap the
two subsequences. Built by IVT on `h = g - id` around `y`, using that `g' > 1` on a
neighborhood of `y` (continuity of `g'` + `g'(y) = (log y)^2 > 1`). -/
theorem strict_two_cycle_exists (hx0 : 0 < x) (hlt : x < eNegE) :
    ∃ β₀ γ₀ : ℝ, x < β₀ ∧ β₀ < γ₀ ∧ γ₀ < 1 ∧
      x ^ (x ^ β₀) = β₀ ∧ x ^ (x ^ γ₀) = γ₀ := by
  have hx1 : x < 1 := by
    have h1 : eNegE < 1 := by rw [eNegE, Real.exp_lt_one_iff]; linarith [Real.exp_pos 1]
    linarith
  -- the fixed point y and its repelling derivative
  obtain ⟨y, hy0, hy1, hfix⟩ := fixedpoint_exists hx0 hx1
  have hlogy : Real.log y < -1 := log_fixedpoint_lt_neg_one hx0 hlt hy0 hfix
  have hxy : x < y := by
    have h := Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hy1
    rwa [Real.rpow_one, hfix] at h
  -- key identities at y
  have hxxy : x ^ (x ^ y) = y := by rw [hfix, hfix]
  have hylogx : y * Real.log x = Real.log y := by
    rw [← Real.log_rpow hx0 y, hfix]
  -- continuity of f, g, g'
  have hfcont : Continuous (fun t : ℝ => x ^ t) := Real.continuous_const_rpow (ne_of_gt hx0)
  have hgcont : Continuous (fun t : ℝ => x ^ (x ^ t)) := hfcont.comp hfcont
  have hG'cont : Continuous
      (fun t : ℝ => (x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x)) :=
    (hgcont.mul continuous_const).mul (hfcont.mul continuous_const)
  -- g'(y) > 1
  have hG'y : (1:ℝ) < (x ^ (x ^ y) * Real.log x) * (x ^ y * Real.log x) := by
    rw [hxxy, hfix, hylogx]
    nlinarith [hlogy, mul_self_nonneg (Real.log y + 1)]
  -- a neighbourhood (radius ε) where g' > 1
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_lt continuous_const hG'cont) y hG'y
  -- shrink ε so the interval [y-δ', y+δ'] stays inside (x,1) ∩ ball y ε
  obtain ⟨δ', hδ'pos, hδ'ε, hδ'1y, hδ'yx⟩ :
      ∃ δ' : ℝ, 0 < δ' ∧ δ' < ε ∧ δ' < 1 - y ∧ δ' < y - x := by
    refine ⟨min ε (min (1 - y) (y - x)) / 2, ?_, ?_, ?_, ?_⟩
    · have : 0 < min ε (min (1 - y) (y - x)) :=
        lt_min hε (lt_min (by linarith) (by linarith))
      linarith
    · have : min ε (min (1 - y) (y - x)) ≤ ε := min_le_left _ _
      linarith
    · have : min ε (min (1 - y) (y - x)) ≤ 1 - y :=
        (min_le_right _ _).trans (min_le_left _ _)
      linarith
    · have : min ε (min (1 - y) (y - x)) ≤ y - x :=
        (min_le_right _ _).trans (min_le_right _ _)
      linarith
  -- h = g - id is strictly increasing on [y-δ', y+δ'] (positive derivative there)
  have hmono : StrictMonoOn (fun t => x ^ (x ^ t) - t)
      (Set.Icc (y - δ') (y + δ')) := by
    have hcont_h : ContinuousOn (fun t : ℝ => x ^ (x ^ t) - t)
        (Set.Icc (y - δ') (y + δ')) := (hgcont.sub continuous_id).continuousOn
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont_h ?_
    intro t ht
    rw [interior_Icc] at ht
    have hball_t : t ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have hG'gt : 1 < (x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x) := hball hball_t
    have hHD : HasDerivAt (fun s : ℝ => x ^ (x ^ s) - s)
        ((x ^ (x ^ t) * Real.log x) * (x ^ t * Real.log x) - 1) t :=
      (hasDeriv_g x hx0 t).sub (hasDerivAt_id t)
    rw [hHD.deriv]; linarith [hG'gt]
  -- endpoints and h(y) = 0
  set a := y - δ' with ha
  set b := y + δ' with hb
  have hay : a < y := by rw [ha]; linarith
  have hyb : y < b := by rw [hb]; linarith
  have hab : a < b := lt_trans hay hyb
  have hhy : (fun t => x ^ (x ^ t) - t) y = 0 := by
    show x ^ (x ^ y) - y = 0; rw [hxxy]; ring
  have hmem_y : y ∈ Set.Icc a b := ⟨hay.le, hyb.le⟩
  have hmem_a : a ∈ Set.Icc a b := ⟨le_refl _, hab.le⟩
  have hmem_b : b ∈ Set.Icc a b := ⟨hab.le, le_refl _⟩
  have hhb : (0:ℝ) < (fun t => x ^ (x ^ t) - t) b := by
    have := hmono hmem_y hmem_b hyb; rw [hhy] at this; linarith
  have hha : (fun t => x ^ (x ^ t) - t) a < 0 := by
    have := hmono hmem_a hmem_y hay; rw [hhy] at this; linarith
  -- boundary values: g(1) = x^x < 1 and g(x) = x^(x^x) > x
  have hh1 : (fun t => x ^ (x ^ t) - t) 1 < 0 := by
    simp only [Real.rpow_one]
    have : x ^ x < 1 := Real.rpow_lt_one hx0.le hx1 hx0
    linarith
  have hhx : (0:ℝ) < (fun t => x ^ (x ^ t) - t) x := by
    show (0:ℝ) < x ^ (x ^ x) - x
    have hxx : x ^ x < 1 := Real.rpow_lt_one hx0.le hx1 hx0
    have h := Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hxx
    rw [Real.rpow_one] at h; linarith
  have hcontOn : ∀ s t : ℝ, ContinuousOn (fun t => x ^ (x ^ t) - t) (Set.Icc s t) :=
    fun s t => (hgcont.sub continuous_id).continuousOn
  -- γ₀ ∈ (b, 1) : a zero of h, hence a fixed point of g above y
  have hb1 : b ≤ 1 := by rw [hb]; linarith
  obtain ⟨γ₀, hγ₀mem, hγ₀eq⟩ :=
    intermediate_value_Ioo' hb1 (hcontOn b 1) ⟨hh1, hhb⟩
  -- β₀ ∈ (x, a) : a zero of h, hence a fixed point of g below y
  have hxa : x ≤ a := by rw [ha]; linarith
  obtain ⟨β₀, hβ₀mem, hβ₀eq⟩ :=
    intermediate_value_Ioo' hxa (hcontOn x a) ⟨hha, hhx⟩
  refine ⟨β₀, γ₀, hβ₀mem.1, ?_, ?_, ?_, ?_⟩
  · -- β₀ < a < y < b < γ₀
    exact lt_trans hβ₀mem.2 (lt_trans hay (lt_trans hyb hγ₀mem.1))
  · exact hγ₀mem.2
  · have : x ^ (x ^ β₀) - β₀ = 0 := hβ₀eq
    linarith
  · have : x ^ (x ^ γ₀) - γ₀ = 0 := hγ₀eq
    linarith

/-- **Lower divergence (MANDATORY).** For `0 < x < e^(-e)` the infinite power tower
does **not** converge: the even subsequence is trapped above `γ₀` and the odd
subsequence below `β₀ < γ₀` (the genuine attracting 2-cycle, `strict_two_cycle_exists`),
so the two subsequence limits are distinct and no single limit exists. The sharp
converse of `two_cycle_collapse`. -/
theorem tower_diverges_lower (hx0 : 0 < x) (hlt : x < eNegE) :
    ¬ ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) := by
  have hx1 : x < 1 := by
    have h1 : eNegE < 1 := by rw [eNegE, Real.exp_lt_one_iff]; linarith [Real.exp_pos 1]
    linarith
  obtain ⟨β, γ, hγ_lim, hβ_lim, _hγβ, _hβγ, _hβpos, _hγpos⟩ := tower_subseq_limits hx0 hx1
  obtain ⟨β₀, γ₀, hxβ₀, hβ₀γ₀, hγ₀1, hβ₀fix, hγ₀fix⟩ := strict_two_cycle_exists hx0 hlt
  have hErec : ∀ n, tower x (2 * (n + 1)) = (fun t => x ^ (x ^ t)) (tower x (2 * n)) := by
    intro n; have h : 2 * (n + 1) = (2 * n) + 2 := by ring
    rw [h, tower_add_two]
  have hOrec : ∀ n, tower x (2 * (n + 1) + 1) = (fun t => x ^ (x ^ t)) (tower x (2 * n + 1)) := by
    intro n; have h : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [h, tower_add_two]
  have hgm := g_mono hx0 hx1.le
  -- even subsequence trapped above γ₀
  have hE_ge : ∀ n, γ₀ ≤ tower x (2 * n) := by
    intro n
    induction n with
    | zero => simp only [Nat.mul_zero, tower_zero]; linarith [hγ₀1]
    | succ k ih =>
        rw [hErec k]
        calc γ₀ = x ^ (x ^ γ₀) := hγ₀fix.symm
          _ ≤ x ^ (x ^ tower x (2 * k)) := hgm ih
  -- odd subsequence trapped below β₀
  have hO_le : ∀ n, tower x (2 * n + 1) ≤ β₀ := by
    intro n
    induction n with
    | zero => simp only [Nat.mul_zero, Nat.zero_add, tower_one]; linarith [hxβ₀]
    | succ k ih =>
        rw [hOrec k]
        calc x ^ (x ^ tower x (2 * k + 1)) ≤ x ^ (x ^ β₀) := hgm ih
          _ = β₀ := hβ₀fix
  have hγ_ge : γ₀ ≤ γ := ge_of_tendsto' hγ_lim hE_ge
  have hβ_le : β ≤ β₀ := le_of_tendsto' hβ_lim hO_le
  have hβγ_strict : β < γ := by linarith [hβ_le, hγ_ge, hβ₀γ₀]
  -- distinct subsequence limits ⟹ no overall limit
  rintro ⟨L, hL⟩
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have h2n1 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have hEL : Tendsto (fun n => tower x (2 * n)) atTop (𝓝 L) := hL.comp h2n
  have hOL : Tendsto (fun n => tower x (2 * n + 1)) atTop (𝓝 L) := hL.comp h2n1
  have hγL : γ = L := tendsto_nhds_unique hγ_lim hEL
  have hβL : β = L := tendsto_nhds_unique hβ_lim hOL
  linarith [hβγ_strict, hγL, hβL]

end LeanFormalizations.RealAnalysis.PowerTower
