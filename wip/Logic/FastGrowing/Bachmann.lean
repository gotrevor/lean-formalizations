/-
# The Bachmann inequality for `ONote.fundamentalSequence` (FGH index-monotonicity prerequisite)

This is the single number-theoretic fact behind pointwise monotonicity of the fast-growing
hierarchy (`fastGrowing_fundSeq_step` in `Basic.lean`): for a limit notation `o` with fundamental
sequence `f`, when the successor term `f (n+1)` is itself a limit with fundamental sequence `g`, the
previous term `f n` is dominated by `g` at level `n+1`:  `f n ≤ g (n+1)`.

`lake env lean wip/Logic/FastGrowing/Bachmann.lean` kernel-checks this.

## Status (2026-06-19 lap)
- **`oadd_le_oadd_tail` — PROVEN.** `b ≤ c ⟹ oadd e m b ≤ oadd e m c` (tail monotonicity, repr level).
- **`fundSeq_bachmann` — the recursive backbone is PROVEN; sole hole = the zero-tail (`b = 0`) case.**
  The proof is structural recursion on `o = oadd e m b`:
  * `o = 0` / `b` a successor : `fundamentalSequence o` is not `inr`, so `ho` is absurd. ✓
  * **`b` a limit (`fundamentalSequence b = inr fb`) — the recursive heart, PROVEN.** Here
    `f i = oadd e m (fb i)`; `f (n+1) = oadd e m (fb (n+1))`. If `fb (n+1)` is a limit with fund seq
    `gb`, then `g i = oadd e m (gb i)` and the goal `oadd e m (fb n) ≤ oadd e m (gb (n+1))` reduces by
    `oadd_le_oadd_tail` to `fb n ≤ gb (n+1)` — which is `fundSeq_bachmann` for the structural subterm
    `b`. The `fb (n+1)` successor / zero branches contradict `hg` / `fb`-strict-monotonicity. ✓
  * **`b = 0` (`fundamentalSequence b = inl none`) — the SOLE remaining `sorry`.** Then `o = ωᵉ·m`
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

/-- **The Bachmann inequality.** For a limit notation `o` (`NF`) with fundamental sequence `f`, if the
successor term `f (n+1)` is itself a limit with fundamental sequence `g`, then `f n ≤ g (n+1)`.

Recursive backbone PROVEN (see file header); sole remaining `sorry` = the zero-tail (`b = 0`) case. -/
theorem fundSeq_bachmann (o : ONote) (hNF : NF o) {f g : ℕ → ONote} {n : ℕ}
    (ho : fundamentalSequence o = Sum.inr f)
    (hg : fundamentalSequence (f (n + 1)) = Sum.inr g) : f n ≤ g (n + 1) := by
  rcases o with _ | ⟨e, m, b⟩
  · simp [fundamentalSequence] at ho
  · rcases hb : fundamentalSequence b with (_ | b') | fb
    · -- b = 0 : o = ωᵉ·m ; four limit sub-cases (B–E) on `fundamentalSequence e`, `m.natPred`
      sorry
    · -- b a successor ⇒ o a successor ⇒ `ho` absurd
      have : fundamentalSequence (oadd e m b) = Sum.inl (some (oadd e m b')) := by
        rw [fundamentalSequence, hb]
      rw [this] at ho; exact absurd ho (by simp)
    · -- b a limit : f i = oadd e m (fb i) — the recursive heart
      have hof : fundamentalSequence (oadd e m b) = Sum.inr (fun i => oadd e m (fb i)) := by
        rw [fundamentalSequence, hb]
      rw [hof, Sum.inr.injEq] at ho
      subst ho
      simp only at hg ⊢
      rcases hfb : fundamentalSequence (fb (n + 1)) with (_ | c) | gb
      · -- fb (n+1) = 0 : impossible (fb strictly increasing from fb 0 ≥ 0)
        have hp := fundamentalSequence_has_prop b
        rw [hb] at hp
        have hmono : StrictMono fb := strictMono_nat_of_lt_succ fun i => (hp.2.1 i).1
        have hlt : fb 0 < fb (n + 1) := hmono (Nat.succ_pos n)
        have hx0 : fb (n + 1) = 0 := by
          have hpp := fundamentalSequence_has_prop (fb (n + 1)); rw [hfb] at hpp; exact hpp
        rw [hx0] at hlt
        exact absurd (lt_def.mp hlt) (by simp)
      · -- fb (n+1) a successor ⇒ oadd e m (fb (n+1)) a successor ⇒ `hg` absurd
        have : fundamentalSequence (oadd e m (fb (n + 1))) = Sum.inl (some (oadd e m c)) := by
          rw [fundamentalSequence, hfb]
        rw [this] at hg; exact absurd hg (by simp)
      · -- fb (n+1) a limit : g i = oadd e m (gb i) ; reduce to Bachmann for the subterm `b`
        have hgof : fundamentalSequence (oadd e m (fb (n + 1)))
            = Sum.inr (fun i => oadd e m (gb i)) := by
          rw [fundamentalSequence, hfb]
        rw [hgof, Sum.inr.injEq] at hg
        subst hg
        simp only
        exact oadd_le_oadd_tail (fundSeq_bachmann b hNF.snd hb hfb)

end LeanFormalizations.Logic.FastGrowing.Bachmann
