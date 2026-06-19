/-
# Corollary: `goodsteinLength` dominates every finite level of the fast-growing hierarchy

The unconditional diagonal bound `fastGrowing_ofNat_le_goodsteinLength` packaged as the textbook
qualitative statement of Cichoń's lower bound at finite levels: for every finite `n`, the Goodstein
length function `goodsteinLength` *eventually* dominates `f_n` (up to the additive `+2` of the Hardy
shift). Equivalently, `goodsteinLength` is not dominated by any `f_n` with `n < ω` — the finite-level
half of the Kirby–Paris growth gap.
-/
import LeanFormalizations.Logic.Goodstein.DominationBaseCases

namespace LeanFormalizations.Logic.Goodstein

open ONote

/-- **`goodsteinLength` eventually dominates `f_n`, for every finite level `n`.** For each `n` there is
a threshold `N` (namely `max 16 (2^{n+1})`) beyond which `fastGrowing (ofNat n) m ≤ goodsteinLength m +
2`. This is Cichoń's lower bound at the finite levels, in its qualitative "eventual domination" form:
`goodsteinLength` outgrows the entire hierarchy `f_0, f_1, f_2, …`. -/
theorem goodsteinLength_dominates_fastGrowing_ofNat (n : ℕ) :
    ∃ N, ∀ m, N ≤ m → fastGrowing (ONote.ofNat n) m ≤ goodsteinLength m + 2 := by
  refine ⟨max 16 (2 ^ (n + 1)), fun m hm => ?_⟩
  have h16 : 16 ≤ m := le_trans (le_max_left _ _) hm
  have hpow : 2 ^ (n + 1) ≤ m := le_trans (le_max_right _ _) hm
  have hlog : n + 1 ≤ Nat.log 2 m := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 hpow
  exact fastGrowing_ofNat_le_goodsteinLength h16 hlog

end LeanFormalizations.Logic.Goodstein
