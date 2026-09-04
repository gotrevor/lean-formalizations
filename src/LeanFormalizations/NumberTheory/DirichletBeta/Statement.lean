/-
# Phase 4 — the audit surface: one of `β(2), β(4), …, β(20)` is irrational

The load-bearing statements of the Dirichlet-beta thread.  Everything else in this directory is
engine.

* `exists_irrational_of_forms` — **W'**, the wiring: a sequence of ℤ-linear forms in
  `1, x_j (j ∈ t)` that never vanishes and tends to `0` forces one `x_j` to be irrational.  This
  is the whole of the classical criterion, once, for `p` numbers (the `p = 1` case is
  `Catalan/Frame.lean`'s `irrational_of_forms`).
* `exists_even_beta_irrational` — **the headline**: at least one of `β(2), β(4), …, β(20)` is
  irrational.  Rivoal–Zudilin 2003 / Zudilin 2019 §2, elementary route, `s = 21`.
* `catalan_or_higher_beta_irrational` — the same statement with `β(2) = G` named, which is the
  form Trevor's thread cares about.

**⚠️ Nothing here claims that Catalan's constant is irrational.  It remains open.**  The headline
says a *disjunction* holds; every one of its ten disjuncts is individually open.

The ledger, in one line:

    d_n^21 · r_n  is a nonzero integer combination of 1, β(2), …, β(20)   (N2, N3)
    |d_n^21 · r_n| ≤ (e^{1.01 n})^21 · e^{-21.3 n} = e^{-0.09 n} → 0     (N4, N5)
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Beta
import LeanFormalizations.NumberTheory.DirichletBeta.Rational
import LeanFormalizations.NumberTheory.DirichletBeta.LinearForm
import LeanFormalizations.NumberTheory.DirichletBeta.Integral
import LeanFormalizations.NumberTheory.DirichletBeta.Bound
import LeanFormalizations.NumberTheory.DirichletBeta.Lcm

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- If `q.den ∣ m` then `q * m` is an integer. -/
private lemma exists_int_mul {q : ℚ} {m : ℤ} (h : (q.den : ℤ) ∣ m) : ∃ z : ℤ, q * m = z := by
  obtain ⟨k, hk⟩ := h
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have key : q * (q.den : ℚ) = (q.num : ℚ) := by
    nth_rewrite 1 [← Rat.num_div_den q]
    field_simp
  refine ⟨q.num * k, ?_⟩
  have hm : (m : ℚ) = (q.den : ℚ) * (k : ℚ) := by rw [hk]; push_cast; ring
  rw [hm, ← mul_assoc, key]
  push_cast
  ring

/-- **W' (wiring).**  Let `x : ι → ℝ` and let `A n + Σ_{j ∈ t} C n j · x j` be a sequence of
ℤ-linear forms which is never zero and tends to `0`.  Then some `x j`, `j ∈ t`, is irrational.

If every `x j` were rational with common denominator `Q`, the form times `Q` would be a nonzero
integer, hence of absolute value `≥ 1`, so the form itself would be `≥ 1/Q` — contradicting
convergence to `0`. -/
theorem exists_irrational_of_forms {ι : Type*} [DecidableEq ι] (t : Finset ι) (x : ι → ℝ)
    (A : ℕ → ℤ) (C : ℕ → ι → ℤ)
    (hne : ∀ n, (A n : ℝ) + ∑ j ∈ t, (C n j : ℝ) * x j ≠ 0)
    (hto : Tendsto (fun n => |(A n : ℝ) + ∑ j ∈ t, (C n j : ℝ) * x j|) atTop (𝓝 0)) :
    ∃ j ∈ t, Irrational (x j) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ j ∈ t, ∃ y : ℚ, (y : ℝ) = x j := fun j hj => not_not.1 (hcon j hj)
  choose! r hr using hmem
  set Q : ℤ := ∏ j ∈ t, ((r j).den : ℤ) with hQdef
  have hQpos : 0 < Q := Finset.prod_pos fun j _ => Int.natCast_pos.2 (r j).pos
  -- the rational shadow of the form
  set L : ℕ → ℚ := fun n => (A n : ℚ) + ∑ j ∈ t, (C n j : ℚ) * r j with hLdef
  have hcast : ∀ n, ((L n : ℚ) : ℝ) = (A n : ℝ) + ∑ j ∈ t, (C n j : ℝ) * x j := by
    intro n
    simp only [hLdef, Rat.cast_add, Rat.cast_intCast, Rat.cast_sum, Rat.cast_mul]
    refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
    rw [hr j hj]
  have hLne : ∀ n, L n ≠ 0 := by
    intro n h
    exact hne n (by rw [← hcast n, h]; simp)
  -- `Q * L n` is an integer
  have hQL : ∀ n, ∃ z : ℤ, L n * Q = z := by
    intro n
    have hj : ∀ j ∈ t, ∃ z : ℤ, r j * (Q : ℚ) = z := fun j hj =>
      exists_int_mul (Finset.dvd_prod_of_mem _ hj)
    choose! z hz using hj
    refine ⟨A n * Q + ∑ j ∈ t, C n j * z j, ?_⟩
    have : ∀ j ∈ t, (C n j : ℚ) * r j * (Q : ℚ) = ((C n j * z j : ℤ) : ℚ) := by
      intro j hj; push_cast [← hz j hj]; ring
    simp only [hLdef, add_mul, Finset.sum_mul]
    push_cast
    rw [Finset.sum_congr rfl this]
    push_cast
    ring
  -- hence the form is bounded below in absolute value
  have hlb : ∀ n, (1 : ℝ) / Q ≤ |(A n : ℝ) + ∑ j ∈ t, (C n j : ℝ) * x j| := by
    intro n
    obtain ⟨z, hz⟩ := hQL n
    have hz0 : z ≠ 0 := by
      intro h
      exact hLne n (by
        have : L n * (Q : ℚ) = 0 := by rw [hz, h]; simp
        rcases mul_eq_zero.1 this with h' | h'
        · exact h'
        · exact absurd h' (by exact_mod_cast hQpos.ne'))
    have h1 : (1 : ℚ) ≤ |L n * Q| := by rw [hz]; exact_mod_cast Int.one_le_abs hz0
    have hQ' : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQpos
    have h2 : (1 : ℚ) / Q ≤ |L n| := by
      rw [div_le_iff₀ hQ']
      calc (1 : ℚ) ≤ |L n * Q| := h1
        _ = |L n| * Q := by rw [abs_mul, abs_of_pos hQ']
    have h3 := (Rat.cast_le (K := ℝ)).2 h2
    push_cast at h3
    rw [← hcast n]
    exact h3
  -- ... contradicting convergence to `0`
  have hpos : (0 : ℝ) < 1 / Q := by
    have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    positivity
  obtain ⟨n, hn⟩ := (hto.eventually (gt_mem_nhds hpos)).exists
  exact absurd (hlb n) (not_le.2 hn)

/-- **The headline.**  At least one of `β(2), β(4), …, β(20)` is irrational.

Rivoal–Zudilin 2003 (Math. Ann. **326**, 705–721) / Zudilin 2019 (arXiv:1804.09922) §2, by the
elementary route of Zudilin's SIGMA 2018 paper (no saddle point, no Nesterenko criterion), with
`s = 21` and the in-repo prime number theorem supplying `d_n^{1/n} → e`. -/
theorem exists_even_beta_irrational :
    ∃ i ∈ Icc 1 10, Irrational (dirichletBeta (2 * i)) := by
  obtain ⟨N₄, hN₄⟩ := abs_rForm_le_exp
  obtain ⟨N₅, hN₅⟩ := dn_le_exp
  set N := max N₄ N₅ with hNdef
  -- the forms, at the even indices `n = 2(N+m)`
  have hchoice : ∀ m : ℕ, ∃ A : ℕ → ℤ,
      ((dn (2 * (N + m)) : ℝ)) ^ 21 * rForm 21 (2 * (N + m))
        = (A 0 : ℝ) + ∑ i ∈ Icc 1 10, (A i : ℝ) * dirichletBeta (2 * i) := by
    intro m
    have h := exists_int_combination (s := 21) (n := 2 * (N + m)) (by norm_num)
      ⟨10, by norm_num⟩ ⟨N + m, by ring⟩
    simpa using h
  choose A hA using hchoice
  refine exists_irrational_of_forms (Icc 1 10) (fun i => dirichletBeta (2 * i))
    (fun m => A m 0) (fun m i => A m i) (fun m => ?_) ?_
  · -- nonvanishing: `d_n^21 ≠ 0` and `r_n ≠ 0`
    rw [← hA m]
    have hdpos : (0 : ℝ) < (dn (2 * (N + m)) : ℝ) := by
      exact_mod_cast Nat.lcmUpto_pos (2 * (N + m))
    exact mul_ne_zero (by positivity)
      (rForm_ne_zero (by norm_num) ⟨10, by norm_num⟩ ⟨N + m, by ring⟩)
  · -- the ledger: `|d_n^21 · r_n| ≤ e^{21·1.01·n} · e^{-21.3 n} = e^{-0.09 n} → 0`
    have key : ∀ m : ℕ,
        |(A m 0 : ℝ) + ∑ i ∈ Icc 1 10, (A m i : ℝ) * dirichletBeta (2 * i)|
          ≤ Real.exp (-0.18 * m) := by
      intro m
      rw [← hA m]
      have hle : N ≤ 2 * (N + m) := by omega
      have h4 : |rForm 21 (2 * (N + m))| ≤ Real.exp (-21.3 * (2 * (N + m) : ℕ)) :=
        hN₄ _ (le_trans (le_trans (le_max_left _ _) (le_of_eq hNdef.symm)) hle) ⟨N + m, by ring⟩
      have h5 : ((dn (2 * (N + m)) : ℕ) : ℝ) ≤ Real.exp (1.01 * (2 * (N + m) : ℕ)) :=
        hN₅ _ (le_trans (le_trans (le_max_right _ _) (le_of_eq hNdef.symm)) hle)
      have hdpos : (0 : ℝ) < ((dn (2 * (N + m)) : ℕ) : ℝ) := by
        exact_mod_cast Nat.lcmUpto_pos (2 * (N + m))
      have hstep : |((dn (2 * (N + m)) : ℝ)) ^ 21 * rForm 21 (2 * (N + m))|
          ≤ Real.exp (1.01 * (2 * (N + m) : ℕ)) ^ 21 * Real.exp (-21.3 * (2 * (N + m) : ℕ)) := by
        rw [abs_mul, abs_of_pos (by positivity)]
        gcongr
      refine hstep.trans ?_
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hNm : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      push_cast
      nlinarith [hNm, (Nat.cast_nonneg m : (0:ℝ) ≤ (m : ℝ))]
    refine squeeze_zero (fun m => abs_nonneg _) key ?_
    have hfun : (fun m : ℕ => Real.exp (-0.18 * m)) = fun m : ℕ => Real.exp (-0.18) ^ m := by
      funext m
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hfun]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _) ?_
    rw [Real.exp_lt_one_iff]
    norm_num

/-- The same disjunction with Catalan's constant named: `β(2) = G`.  **This does not say `G` is
irrational** — only that if `G` is rational then one of `β(4), …, β(20)` is not. -/
theorem catalan_or_higher_beta_irrational :
    Irrational LeanFormalizations.Catalan.catalanConst ∨
      ∃ i ∈ Icc 2 10, Irrational (dirichletBeta (2 * i)) := by
  obtain ⟨i, hi, hirr⟩ := exists_even_beta_irrational
  rcases eq_or_lt_of_le (mem_Icc.1 hi).1 with h | h
  · refine Or.inl ?_
    have h2 : 2 * i = 2 := by omega
    rw [h2, beta_two_eq_catalanConst] at hirr
    exact hirr
  · exact Or.inr ⟨i, mem_Icc.2 ⟨h, (mem_Icc.1 hi).2⟩, hirr⟩

end LeanFormalizations.DirichletBeta
