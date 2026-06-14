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
