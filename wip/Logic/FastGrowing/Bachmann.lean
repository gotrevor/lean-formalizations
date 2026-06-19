/-
# The Bachmann inequality for `ONote.fundamentalSequence` (FGH index-monotonicity prerequisite)

This is the single number-theoretic fact behind pointwise monotonicity of the fast-growing
hierarchy (`fastGrowing_fundSeq_step` in `Basic.lean`): for a limit notation `o` with fundamental
sequence `f`, when the successor term `f (n+1)` is itself a limit with fundamental sequence `g`, the
previous term `f n` is dominated by `g` at level `n+1`:  `f n ≤ g (n+1)`.

`lake env lean wip/Logic/FastGrowing/Bachmann.lean` kernel-checks this (`#print axioms` = [propext, Classical.choice, Quot.sound]).

## Status (2026-06-19 lap)
- **`oadd_le_oadd_tail` — PROVEN.** `b ≤ c ⟹ oadd e m b ≤ oadd e m c` (tail monotonicity, repr level).
- **`fundSeq_bachmann` — FULLY PROVEN (2026-06-19), axiom-clean.** All cases incl. the zero-tail (`b = 0`).
  The proof is structural recursion on `o = oadd e m b`:
  * `o = 0` / `b` a successor : `fundamentalSequence o` is not `inr`, so `ho` is absurd. ✓
  * **`b` a limit (`fundamentalSequence b = inr fb`) — the recursive heart, PROVEN.** Here
    `f i = oadd e m (fb i)`; `f (n+1) = oadd e m (fb (n+1))`. If `fb (n+1)` is a limit with fund seq
    `gb`, then `g i = oadd e m (gb i)` and the goal `oadd e m (fb n) ≤ oadd e m (gb (n+1))` reduces by
    `oadd_le_oadd_tail` to `fb n ≤ gb (n+1)` — which is `fundSeq_bachmann` for the structural subterm
    `b`. The `fb (n+1)` successor / zero branches contradict `hg` / `fb`-strict-monotonicity. ✓
  * **`b = 0` (`fundamentalSequence b = inl none`) — PROVEN.** Then `o = ωᵉ·m`
    and `fundamentalSequence o` branches on `fundamentalSequence e` and `m.natPred`
    (`Mathlib/SetTheory/Ordinal/Notation` lines 929–935), giving four limit sub-cases:
      - (B) `e = e'+1`, `m = 1`: `f i = ωᵉ'·(i+1)`. `f n = ωᵉ'·(n+1)`, and `g (n+1)` shares that
        `oadd e' (n+1)` prefix with a `≥ 0` tail ⇒ closes by `oadd_le_oadd_tail`.
      - (C) `e = e'+1`, `m = k+2`: `f i = ωᵉ·(k+1) + ωᵉ'·(i+1)`; same prefix-domination closing.
      - (D) `e` a limit (`fundamentalSequence e = inr fe`), `m = 1`: `f i = ω^(fe i)`. `f (n+1) =
        ω^(fe (n+1))`; this case is **recursive on `e`** (the exponent), mirroring the `b`-limit case:
        `fundSeq_bachmann e _ (fundamentalSequence e = inr fe) _` gives `fe n ≤ (·) (n+1)`.
      - (E) `e` a limit, `m = k+2`: `f i = ωᵉ·(k+1) + ω^(fe i)`; combination of (C)-prefix + (D)-recursion.
    Each sub-case's `g (n+1)` is read off by the same `rw [fundamentalSequence, …]` unfolding used
    above; the closings are `oadd_le_oadd_tail` + `le_self_add`/ω-power monotonicity, or recursion on
    `e`. Verified example: `o = ω²` (case D-ish), `f n = ω·(n+1) ≤ ω·(n+1)+(n+2) = g (n+1)`.
-/
import Mathlib.SetTheory.Ordinal.Notation

namespace LeanFormalizations.Logic.FastGrowing.Bachmann

open ONote Ordinal

/-- **Tail monotonicity (PROVEN).** Increasing the tail of an `oadd` increases it. -/
theorem oadd_le_oadd_tail {e : ONote} {m : ℕ+} {b c : ONote} (h : b ≤ c) :
    oadd e m b ≤ oadd e m c := by
  rw [le_def] at h ⊢
  show ω ^ e.repr * m + b.repr ≤ ω ^ e.repr * m + c.repr
  gcongr

/-- Exponent/leading monotonicity at the repr level, with a possibly larger multiplicity and tail. -/
theorem oadd_le_oadd_exp_mul {a a' : ONote} {m m' : ℕ+} {b b' : ONote}
    (hexp : a.repr ≤ a'.repr) (hmul : (m : ℕ) ≤ (m' : ℕ)) (htail : b.repr ≤ b'.repr) :
    oadd a m b ≤ oadd a' m' b' := by
  rw [le_def]
  show ω ^ a.repr * m + b.repr ≤ ω ^ a'.repr * m' + b'.repr
  gcongr <;> first | exact omega0_pos | exact one_lt_omega0.le

theorem zero_le' (x : ONote) : (0 : ONote) ≤ x := by rw [le_def]; simp

/-- **The Bachmann inequality.** For a limit notation `o` (`NF`) with fundamental sequence `f`, if the
successor term `f (n+1)` is itself a limit with fundamental sequence `g`, then `f n ≤ g (n+1)`.

FULLY PROVEN; the zero-tail (`b = 0`) case is the four-limit-sub-case (B–E) bash discharged below. -/
theorem fundSeq_bachmann (o : ONote) (hNF : NF o) {f g : ℕ → ONote} {n : ℕ}
    (ho : fundamentalSequence o = Sum.inr f)
    (hg : fundamentalSequence (f (n + 1)) = Sum.inr g) : f n ≤ g (n + 1) := by
  rcases o with _ | ⟨e, m, b⟩
  · simp [fundamentalSequence] at ho
  · rcases hb : fundamentalSequence b with (_ | b') | fb
    · have hb0 : b = 0 := by
        have hp := fundamentalSequence_has_prop b; rw [hb] at hp; exact hp
      subst hb0
      rw [fundamentalSequence] at ho
      simp only [fundamentalSequence] at ho
      have hred : (n+1).succPNat.natPred = n + 1 := rfl
      have hred1 : (1 : ℕ+).natPred = 0 := rfl
      rcases he : fundamentalSequence e with (_ | e') | fe <;>
        rcases hm : (m : ℕ+).natPred with _ | m' <;>
        rw [he, hm] at ho <;>
        simp only [reduceCtorEq, Sum.inr.injEq] at ho
      · -- B: e succ (e'), m = 1
        subst ho; simp only at hg ⊢
        rcases hfe : fundamentalSequence e' with (_ | e'') | fe' <;>
          simp only [fundamentalSequence, hfe, hred] at hg ⊢
        · simp at hg
        · rw [Sum.inr.injEq] at hg; subst hg; exact oadd_le_oadd_tail (zero_le' _)
        · rw [Sum.inr.injEq] at hg; subst hg; exact oadd_le_oadd_tail (zero_le' _)
      · -- C: e succ (e'), m = m'+1
        subst ho; simp only at hg ⊢
        rcases hfe : fundamentalSequence e' with (_ | e'') | fe' <;>
          simp only [fundamentalSequence, hfe, hred] at hg ⊢
        · simp at hg
        · rw [Sum.inr.injEq] at hg; subst hg
          exact oadd_le_oadd_tail (oadd_le_oadd_tail (zero_le' _))
        · rw [Sum.inr.injEq] at hg; subst hg
          exact oadd_le_oadd_tail (oadd_le_oadd_tail (zero_le' _))
      · -- D: e limit (fe), m = 1
        subst ho; simp only at hg ⊢
        have hmono : StrictMono fe := by
          have hp := fundamentalSequence_has_prop e; rw [he] at hp
          exact strictMono_nat_of_lt_succ fun i => (hp.2.1 i).1
        rcases hfe2 : fundamentalSequence (fe (n + 1)) with (_ | a') | gb <;>
          simp only [fundamentalSequence, hfe2, hred1] at hg ⊢
        · simp at hg
        · -- fe(n+1) successor a': fe n ≤ a' via strict mono + succ
          rw [Sum.inr.injEq] at hg; subst hg
          have hp2 := fundamentalSequence_has_prop (fe (n+1)); rw [hfe2] at hp2
          have hle : (fe n).repr ≤ a'.repr := by
            have := hmono (Nat.lt_succ_self n)
            rw [lt_def, hp2.1] at this
            exact Order.le_of_lt_succ this
          exact oadd_le_oadd_exp_mul hle (by simp) (by simp)
        · -- fe(n+1) limit gb: Bachmann recursion fe n ≤ gb(n+1)
          rw [Sum.inr.injEq] at hg; subst hg
          have hbm : fe n ≤ gb (n + 1) := fundSeq_bachmann e hNF.fst he hfe2
          rw [le_def] at hbm
          exact oadd_le_oadd_exp_mul hbm (le_refl _) (le_refl _)
      · -- E: e limit (fe), m = m'+1
        subst ho; simp only at hg ⊢
        have hmono : StrictMono fe := by
          have hp := fundamentalSequence_has_prop e; rw [he] at hp
          exact strictMono_nat_of_lt_succ fun i => (hp.2.1 i).1
        rcases hfe2 : fundamentalSequence (fe (n + 1)) with (_ | a') | gb <;>
          simp only [fundamentalSequence, hfe2, hred1] at hg ⊢
        · simp at hg
        · rw [Sum.inr.injEq] at hg; subst hg
          have hp2 := fundamentalSequence_has_prop (fe (n+1)); rw [hfe2] at hp2
          have hle : (fe n).repr ≤ a'.repr := by
            have := hmono (Nat.lt_succ_self n)
            rw [lt_def, hp2.1] at this
            exact Order.le_of_lt_succ this
          exact oadd_le_oadd_tail (oadd_le_oadd_exp_mul hle (by simp) (by simp))
        · rw [Sum.inr.injEq] at hg; subst hg
          have hbm : fe n ≤ gb (n + 1) := fundSeq_bachmann e hNF.fst he hfe2
          rw [le_def] at hbm
          exact oadd_le_oadd_tail (oadd_le_oadd_exp_mul hbm (le_refl _) (le_refl _))
    · have : fundamentalSequence (oadd e m b) = Sum.inl (some (oadd e m b')) := by
        rw [fundamentalSequence, hb]
      rw [this] at ho; exact absurd ho (by simp)
    · have hof : fundamentalSequence (oadd e m b) = Sum.inr (fun i => oadd e m (fb i)) := by
        rw [fundamentalSequence, hb]
      rw [hof, Sum.inr.injEq] at ho
      subst ho
      simp only at hg ⊢
      rcases hfb : fundamentalSequence (fb (n + 1)) with (_ | c) | gb
      · have hp := fundamentalSequence_has_prop b; rw [hb] at hp
        have hmono : StrictMono fb := strictMono_nat_of_lt_succ fun i => (hp.2.1 i).1
        have hlt : fb 0 < fb (n + 1) := hmono (Nat.succ_pos n)
        have hx0 : fb (n + 1) = 0 := by
          have hpp := fundamentalSequence_has_prop (fb (n + 1)); rw [hfb] at hpp; exact hpp
        rw [hx0] at hlt; exact absurd (lt_def.mp hlt) (by simp)
      · have : fundamentalSequence (oadd e m (fb (n + 1))) = Sum.inl (some (oadd e m c)) := by
          rw [fundamentalSequence, hfb]
        rw [this] at hg; exact absurd hg (by simp)
      · have hgof : fundamentalSequence (oadd e m (fb (n + 1)))
            = Sum.inr (fun i => oadd e m (gb i)) := by
          rw [fundamentalSequence, hfb]
        rw [hgof, Sum.inr.injEq] at hg
        subst hg; simp only
        exact oadd_le_oadd_tail (fundSeq_bachmann b hNF.snd hb hfb)

end LeanFormalizations.Logic.FastGrowing.Bachmann
