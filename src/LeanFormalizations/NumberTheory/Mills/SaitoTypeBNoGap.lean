/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBParts
import LeanFormalizations.NumberTheory.Mills.DominantPair

/-!
# Phase 62: where Baker enters Saito's Type B, and how much of it E+ can drop

`saitoTypeBLeastEv_holds` uses `Dubickas2022PisotGap` (Dubickas 2022 Lemma 8 = Saito Lemma 5.14,
whose complex-pair case is Baker's theorem) twice: in `eventually_low` (Saito's case (I), sparse
decay at rate `c − 1 ≥ 19/10`) and in the main degree bound (case (II), decay at every large `k` at
rate `151/400`).  The frozen `saitoTypeBLeast_holds` has no `hG`.

## Case (II) for E+: no Baker needed (`conjPowSum_lower_of_recurrence`)
For `C k = 3^(k+j) + s` the exponents `n_k = C k / g` satisfy `n_(k+1) = 3 n_k − d` exactly, with
`d = 2s/g ≠ 0`.  Along such an orbit the conjugate power sum cannot cancel: by Smyth's lemma the
dominant conjugates are one real `γ` (then `|S(n)| ≈ R^n`) or a pair `γ, γ̄`; in the latter case,
with `a_k = (γ/R)^(n_k)`, cancellation `Re a_k → 0` means `a_k² → −1`, while `a_(k+1)² =
a_k⁶ v²` with `v = (γ/R)^(−d)`, forcing `v² = 1`, i.e. `γ^(2d) = γ̄^(2d)`, which contradicts the
distinctness of the conjugates of `β^(2d)`.  So `|S(n_k)| ≥ c R^(n_k)` infinitely often.

## Case (I): the residual Baker-type input (`SparseNoCancel`)
Case (I) gives `‖β^n‖ ≤ K β^(−19n/10)` only along an arbitrary sparse set of `n`, with no relation
between consecutive terms.  The norm of `β^n − Tr(β^n)` gives only `|S(n)| ≥ β^(−(ℓ−1)n)`, which
excludes degree 2 but not degree `≥ 3` (it is borderline at `ℓ = 3`: rate 2 against 19/10).
`SparseNoCancel` is exactly what case (I) needs; it follows from `Dubickas2022PisotGap`
(`sparseNoCancel_of_gap`).  It is the reopen condition of the `Maze.lean` row
"Saito Type B (E+) from BHP + Dubickas 2022 Lemma 6 alone".
-/

namespace LeanFormalizations.Mills.SaitoTypeB

open LeanFormalizations.Literature LeanFormalizations.Mills Filter

/-- **Reopen node** (what Saito's case (I) needs, degree `≥ 3`): the conjugate power sum of a
Pisot number of degree `≥ 3` is eventually larger than `K β^(−19n/10)`.  True by Baker's theorem
(`sparseNoCancel_of_gap`); no elementary proof known to us. -/
def SparseNoCancel : Prop :=
  ∀ β : ℝ, IsPisot β → 3 ≤ (minpoly ℚ β).natDegree → ∀ K > (0 : ℝ),
    ∀ᶠ n : ℕ in atTop, K * β ^ (-((19 / 10 : ℝ) * n)) < ‖conjPowSum β n‖

/-- `Dubickas2022PisotGap` (Baker) implies the reopen node. -/
theorem sparseNoCancel_of_gap (hG : Dubickas2022PisotGap) : SparseNoCancel := by
  intro β hβ hdeg K hK
  by_contra hcon
  rw [not_eventually] at hcon
  have hfreq : ∃ᶠ n : ℕ in atTop, ‖conjPowSum β n‖ ≤ K * (β ^ (-((19 / 10 : ℝ) * n)) : ℝ) :=
    hcon.mono fun n h => not_lt.1 h
  have hb := pisot_degree_bound hG hβ (by omega) (by norm_num) hK hfreq
  have h' := card_otherConj_add_one hβ.2.1.tower_top
  have : (2 : ℝ) ≤ Multiset.card (otherConj β) := by exact_mod_cast (by omega :
    2 ≤ Multiset.card (otherConj β))
  linarith

/-- **No cancellation along `n ↦ 3n − d`** (Baker-free).  If the exponents satisfy
`n_(k+1) = 3 n_k − d` with `d ≠ 0` and `n_k → ∞`, the conjugate power sum of a Pisot number of
degree `≥ 2` is at least `c R^(n_k)` infinitely often, `R` the largest other-conjugate modulus.

Confidence ~90%.  English proof in the module docstring (Smyth's lemma via a Galois automorphism
sending `|γ|²` to a conjugate of modulus `> 1`; then the `a_k² → −1` / `a_(k+1)² → −v²`
argument). -/
theorem conjPowSum_lower_of_recurrence {β : ℝ} (hβ : IsPisot β)
    (hdeg : 2 ≤ (minpoly ℚ β).natDegree) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {d : ℤ}
    (hd : d ≠ 0) (hrec : ∀ k, (n (k + 1) : ℤ) = 3 * n k - d) :
    ∃ c > (0 : ℝ), ∃ᶠ k in atTop, c * conjMax β ^ n k ≤ ‖conjPowSum β (n k)‖ := by
  have hiter : ∀ t k, (2 : ℤ) * n (k + t) = 3 ^ t * (2 * n k) - d * (3 ^ t - 1) := by
    intro t
    induction t with
    | zero => intro k; simp
    | succ t ih =>
      intro k
      rw [← add_assoc, hrec]; linear_combination 3 * ih k
  obtain ⟨c, hc, hfr⟩ := DominantPair.lower_along_records hβ hdeg hn (Rec := fun _ => True)
    (T := 1) (K' := 0) (fun m _ => ⟨m + 1, by omega, le_rfl, trivial⟩) (g := 2) hd
    (fun k r _ _ _ hkr => by
      have := hiter (r - k) k
      rwa [show k + (r - k) = r by omega] at this)
  exact ⟨c, hc, hfr.mono fun k hk => hk.2⟩

end LeanFormalizations.Mills.SaitoTypeB
