/-
# Bachmann inequality for ONote.fundamentalSequence — ONLY the `b = 0` branch is open

GOAL: replace the single remaining `sorry` (the `b = 0` case, marked below) with a real proof.
Everything else in `fundSeq_bachmann` is already proven; do not change the proven branches.

CONTEXT. `ONote.fundamentalSequence : ONote → (Option ONote) ⊕ (ℕ → ONote)` is defined in
`Mathlib/SetTheory/Ordinal/Notation.lean`:
  fundamentalSequence zero = inl none
  fundamentalSequence (oadd a m b) =
    match fundamentalSequence b with
    | inr f          => inr (fun i => oadd a m (f i))
    | inl (some b')  => inl (some (oadd a m b'))
    | inl none       =>            -- THIS is the `b = 0` case to discharge
      match fundamentalSequence a, m.natPred with
      | inl none,     0     => inl (some zero)
      | inl none,     k + 1 => inl (some (oadd zero k.succPNat zero))
      | inl (some a'), 0    => inr (fun i => oadd a' i.succPNat zero)
      | inl (some a'), k + 1=> inr (fun i => oadd a k.succPNat (oadd a' i.succPNat zero))
      | inr fe,        0    => inr (fun i => oadd (fe i) 1 zero)
      | inr fe,        k + 1=> inr (fun i => oadd a k.succPNat (oadd (fe i) 1 zero))
`fundamentalSequence_has_prop o` gives the `FundamentalSequenceProp`; in the `inr f` (limit) case:
`IsSuccLimit o.repr ∧ (∀ i, f i < f (i+1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a<o.repr → ∃ i, a<(f i).repr`.

The Bachmann inequality: for a limit `o` with fundamental sequence `f`, when `f (n+1)` is itself a
limit with fundamental sequence `g`, then `f n ≤ g (n+1)`.

ROADMAP for the `b = 0` branch (`o = oadd e m 0 = ωᵉ·m`). After `rw [fundamentalSequence, hb] at ho`
the four limit sub-cases of `(fundamentalSequence e, m.natPred)` each pin `f`; the two `inl none`
exponent cases make `o` a successor (so `ho : inl _ = inr f` is absurd). In each limit sub-case,
`f n` and `g (n+1)` share an `oadd <exp> <mult>` prefix with `f n` carrying tail `0`, so the goal
closes by `oadd_le_oadd_tail (zero_le _)` (B/C) or by recursion of `fundSeq_bachmann` on the exponent
`e` (D/E). The successor sub-cases for `f (n+1)` make `hg` absurd. VERIFIED example: `o = ω²`,
`f n = ω·(n+1) ≤ ω·(n+1)+(n+2) = g (n+1)`.
-/
import Mathlib

namespace BachmannProblem

open ONote Ordinal

/-- Tail monotonicity (PROVEN — keep as is, reusable for the closings). -/
theorem oadd_le_oadd_tail {e : ONote} {m : ℕ+} {b c : ONote} (h : b ≤ c) :
    oadd e m b ≤ oadd e m c := by
  rw [le_def] at h ⊢
  show ω ^ e.repr * m + b.repr ≤ ω ^ e.repr * m + c.repr
  gcongr

/-- **The Bachmann inequality.** Recursive backbone proven; the SOLE remaining `sorry` is the
`b = 0` (zero-tail) case, marked below. -/
theorem fundSeq_bachmann (o : ONote) (hNF : NF o) {f g : ℕ → ONote} {n : ℕ}
    (ho : fundamentalSequence o = Sum.inr f)
    (hg : fundamentalSequence (f (n + 1)) = Sum.inr g) : f n ≤ g (n + 1) := by
  rcases o with _ | ⟨e, m, b⟩
  · simp [fundamentalSequence] at ho
  · rcases hb : fundamentalSequence b with (_ | b') | fb
    · -- ===== b = 0 : o = ωᵉ·m ; FOUR limit sub-cases (B–E). THIS IS THE ONLY OPEN GOAL. =====
      sorry
    · -- b a successor ⇒ o a successor ⇒ `ho` absurd
      have : fundamentalSequence (oadd e m b) = Sum.inl (some (oadd e m b')) := by
        rw [fundamentalSequence, hb]
      rw [this] at ho; exact absurd ho (by simp)
    · -- b a limit : f i = oadd e m (fb i) — the recursive heart (PROVEN)
      have hof : fundamentalSequence (oadd e m b) = Sum.inr (fun i => oadd e m (fb i)) := by
        rw [fundamentalSequence, hb]
      rw [hof, Sum.inr.injEq] at ho
      subst ho
      simp only at hg ⊢
      rcases hfb : fundamentalSequence (fb (n + 1)) with (_ | c) | gb
      · have hp := fundamentalSequence_has_prop b
        rw [hb] at hp
        have hmono : StrictMono fb := strictMono_nat_of_lt_succ fun i => (hp.2.1 i).1
        have hlt : fb 0 < fb (n + 1) := hmono (Nat.succ_pos n)
        have hx0 : fb (n + 1) = 0 := by
          have hpp := fundamentalSequence_has_prop (fb (n + 1)); rw [hfb] at hpp; exact hpp
        rw [hx0] at hlt
        exact absurd (lt_def.mp hlt) (by simp)
      · have : fundamentalSequence (oadd e m (fb (n + 1))) = Sum.inl (some (oadd e m c)) := by
          rw [fundamentalSequence, hfb]
        rw [this] at hg; exact absurd hg (by simp)
      · have hgof : fundamentalSequence (oadd e m (fb (n + 1)))
            = Sum.inr (fun i => oadd e m (gb i)) := by
          rw [fundamentalSequence, hfb]
        rw [hgof, Sum.inr.injEq] at hg
        subst hg
        simp only
        exact oadd_le_oadd_tail (fundSeq_bachmann b hNF.snd hb hfb)

end BachmannProblem
