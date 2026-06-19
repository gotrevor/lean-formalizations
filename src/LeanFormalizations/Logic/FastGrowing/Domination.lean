/-
# A4 — `fastGrowingε₀` dominates every fixed level (the headline domination crux)

The unboundedness that *is* the Goodstein/Kirby–Paris independence content:

> For every notation `o < ε₀`, eventually `fastGrowing o n < fastGrowingε₀ n`.

`fastGrowingε₀` is `mathlib`'s one-step extension of the fast-growing hierarchy to `ε₀`,
built on the *diagonal tower* fundamental sequence `0, 1, ω, ω^ω, ω^ω^ω, …` converging to
`ε₀`:

* `fastGrowingε₀ i = fastGrowing (tower i) i`, where `tower i = (fun a => ω^a)^[i] 0`.

This file pins the tower structure and **proves A4 in full, axiom-clean**. With
A1 (`le_fastGrowing`), A2 (`fastGrowing_monotone`) and A3 (`fastGrowing_bachmann_reach`)
proved in `Basic.lean`, the remaining content of A4 was an **index domination** fact: each
fixed `o` is eventually outgrown because the tower indices climb past it.

## Architecture (all proved, no `sorry`)
1. **Tower structure**: `tower (i+1) = ω^{tower i}`, `fastGrowingε₀` unfolds to
   `fastGrowing (tower i) i`; cofinality `tower_cofinal`.
2. **The CNF norm** `norm` + the **key cofinality bound**
   `lt_fundamentalSequence_of_norm_le` (THE new theorem): for a limit `β` and `α < β` with
   `norm α ≤ x`, already `α < g_β(x)`. Proved by structural induction over all six
   `fundamentalSequence` branches.
3. **General reachability** `reaches_of_lt`: `α < β ∧ norm α ≤ x ⟹ Reaches x β α`, by WF
   recursion on `β` reusing (2) at limits.
4. **Strictness** via the notation successor `osucc`: reach `osucc o` and take one strict
   successor index step (`fastGrowing_lt_succ_index`, needs `2 ≤ n`).

Headline: `fastGrowing_lt_fastGrowingε₀` — every fixed `f_o` is eventually strictly
dominated by `f_{ε₀}`. This is the unboundedness that *is* the Kirby–Paris growth gap.
-/
import Mathlib.SetTheory.Ordinal.Notation
import LeanFormalizations.Logic.FastGrowing.Basic

namespace LeanFormalizations.Logic.FastGrowing

open ONote Ordinal

/-- **No `ω`-fixed points below `ε₀`, elementarily.** For every normal-form notation,
`repr o < ω ^ repr o`. Proved by *structural induction* on `o` — the inductive hypothesis
at the leading exponent `e` gives `repr e < ω ^ repr e ≤ repr o`, hence `repr e < repr o`,
so `repr o < ω ^ (repr e + 1) ≤ ω ^ repr o` (`NFBelow.repr_lt` + monotonicity). No `ε₀`
fixed-point machinery needed. The key strictness fact underlying the tower's growth. -/
theorem repr_lt_opow_repr : ∀ (o : ONote), o.NF → o.repr < ω ^ o.repr
  | 0, _ => by simp
  | oadd e n a, h => by
      have hIH : e.repr < ω ^ e.repr := repr_lt_opow_repr e h.fst
      have hle : ω ^ e.repr ≤ (oadd e n a).repr := omega0_le_oadd e n a
      have helt : e.repr < (oadd e n a).repr := lt_of_lt_of_le hIH hle
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (oadd e n a).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt helt)
      exact lt_of_lt_of_le h1 h2

/-! ### The CNF norm and structural comparison helpers (toward general Bachmann reachability)

The general index-domination needs a **budget condition**: the diagonal argument `x` must be
large enough that the fundamental-sequence descent of `β` actually passes through `α`. The
right "size of `α`" is its **CNF norm**: the largest finite number (coefficient or finite
tail) appearing anywhere in `α`'s Cantor normal form. -/

/-- **CNF norm** of a notation: the maximum finite coefficient appearing anywhere in its
Cantor normal form (recursively through exponents and tails). `norm 0 = 0`,
`norm (ω^e·n + a) = max (norm e) (max n (norm a))`. This is the budget threshold: if
`norm α ≤ x` then the standard fundamental-sequence descent of any `β > α` reaches `α` with
budget `x` (`reaches_of_lt`). -/
def norm : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (max (n : ℕ) (norm a))

@[simp] theorem norm_zero : norm 0 = 0 := rfl

@[simp] theorem norm_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    norm (oadd e n a) = max (norm e) (max (n : ℕ) (norm a)) := rfl

/-- **Trichotomy decomposition of `<` on `oadd`.** For normal-form notations, `α < β`
splits into the three lexicographic cases on (exponent, coefficient, tail). -/
theorem lt_oadd_cases {ea : ONote} {na : ℕ+} {ba e : ONote} {m : ℕ+} {b : ONote}
    (hα : NF (oadd ea na ba)) (hβ : NF (oadd e m b)) (h : oadd ea na ba < oadd e m b) :
    ea < e ∨ (ea = e ∧ (na : ℕ) < (m : ℕ)) ∨ (ea = e ∧ na = m ∧ ba < b) := by
  rcases lt_trichotomy ea.repr e.repr with he | he | he
  · exact Or.inl (lt_def.2 he)
  · have heq : ea = e := (@repr_inj ea e hα.fst hβ.fst).1 he
    subst heq
    rcases lt_trichotomy (na : ℕ) (m : ℕ) with hn | hn | hn
    · exact Or.inr (Or.inl ⟨rfl, hn⟩)
    · have hnm : na = m := PNat.coe_injective hn
      subst hnm
      rcases lt_trichotomy ba.repr b.repr with hb | hb | hb
      · exact Or.inr (Or.inr ⟨rfl, rfl, lt_def.2 hb⟩)
      · have hbeq : ba = b := (@repr_inj ba b hα.snd hβ.snd).1 hb
        subst hbeq; exact absurd h (lt_irrefl _)
      · exact absurd (oadd_lt_oadd_3 (lt_def.2 hb)) (lt_asymm h)
    · exact absurd (oadd_lt_oadd_2 hβ hn) (lt_asymm h)
  · exact absurd (oadd_lt_oadd_1 hβ (lt_def.2 he)) (lt_asymm h)

/-- **The norm bound on a single CNF level.** If a normal-form `δ` has leading exponent
`≤ c` (i.e. `repr δ < ω^(repr c)·ω`) and norm `≤ x`, then `δ < ω^(repr c)·(x+1) =
oadd c (x+1) 0`. The workhorse for the limit cases of the key lemma: a small-norm notation
can't reach past the `(x+1)`-th rung `ω^c·(x+1)` of the relevant fundamental sequence. -/
theorem lt_oadd_of_lead_le {x : ℕ} {c : ONote} (hc : c.NF) {δ : ONote} (hδ : δ.NF)
    (hlead : δ.repr < ω ^ c.repr * ω) (hnorm : norm δ ≤ x) :
    δ < oadd c x.succPNat 0 := by
  cases δ with
  | zero => exact oadd_pos _ _ _
  | oadd ed nd bd =>
    have hpow : ω ^ ed.repr ≤ (oadd ed nd bd).repr := omega0_le_oadd ed nd bd
    have h2 : (ω : Ordinal) ^ ed.repr < ω ^ c.repr * ω := lt_of_le_of_lt hpow hlead
    rw [← opow_succ] at h2
    have hed_le : ed.repr ≤ c.repr :=
      Order.lt_succ_iff.1 ((opow_lt_opow_iff_right one_lt_omega0).1 h2)
    rcases lt_or_eq_of_le hed_le with hlt | heq
    · exact oadd_lt_oadd_1 hδ (lt_def.2 hlt)
    · have hedc : ed = c := (@repr_inj ed c hδ.fst hc).1 heq
      subst hedc
      rw [norm_oadd] at hnorm
      have hnd : (nd : ℕ) ≤ x := (le_max_of_le_right (le_max_left _ _)).trans hnorm
      refine oadd_lt_oadd_2 hδ ?_
      simpa [Nat.succPNat] using Nat.lt_succ_of_le hnd

/-- **The key cofinality bound (general Bachmann reachability core).** For a normal-form
*limit* `β` with standard fundamental sequence `g`, every `α < β` whose CNF norm is `≤ x`
already sits below the `x`-th rung `g x`. Equivalently: the budget `x ≥ norm α` is enough
for the descent of `β` to "catch" `α`.

Proved by structural induction on `β`, following the six branches of
`ONote.fundamentalSequence` exactly. The successor-producing branches contradict the limit
hypothesis. The five limit-producing branches each reduce, after decomposing `α`'s leading
CNF term (`lt_oadd_cases`), to either the inductive hypothesis on the exponent/tail or the
single-level norm bound `lt_oadd_of_lead_le`. This is the one genuinely new theorem of the
A4 development; once it holds, all of general reachability and index domination follow. -/
theorem lt_fundamentalSequence_of_norm_le {x : ℕ} :
    ∀ (β : ONote), β.NF → ∀ (g : ℕ → ONote), fundamentalSequence β = Sum.inr g →
      ∀ (α : ONote), α.NF → α < β → norm α ≤ x → α < g x := by
  intro β
  induction β with
  | zero => intro _ g hg _ _ _ _; exact (Sum.inl_ne_inr hg).elim
  | oadd a m b iha ihb =>
    intro hβ g hg α hα hαβ hnorm
    rcases hb : fundamentalSequence b with (_ | b') | hbf
    · -- b = 0 : leading-term cases
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 : `oadd 0 m 0` is a successor → contradicts the limit `hg`
        rcases hm : m.natPred with _ | k
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
      · -- a a successor (predecessor `a'`)
        have hpa := fundamentalSequence_has_prop a; rw [ha] at hpa
        have ha'NF : a'.NF := hpa.2 hβ.fst
        have harepr : a.repr = Order.succ a'.repr := hpa.1
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L2 : `g = fun i => ω^a'·(i+1)`, `m = 1`
          have hg' : g = fun i => oadd a' i.succPNat 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          refine lt_oadd_of_lead_le ha'NF hα ?_ hnorm
          have hlt : α.repr < (oadd a m b).repr := lt_def.1 hαβ
          rw [hb0, hm1] at hlt
          rw [show (oadd a 1 0).repr = ω ^ a.repr from by
            simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]] at hlt
          rw [harepr, opow_succ] at hlt
          exact hlt
        · -- L3 : `g = fun i => ω^a·(k+1) + ω^a'·(i+1)`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd a' i.succPNat 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases α with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hαβ
            rcases lt_oadd_cases hα (hb0 ▸ hβ) hαβ with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hα hlt
            · rw [heq] at hα hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hα (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat := PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                refine lt_oadd_of_lead_le ha'NF hα.snd ?_ ?_
                · have hba : ba.repr < ω ^ a.repr := hα.snd'.repr_lt
                  rw [harepr, opow_succ] at hba; exact hba
                · rw [norm_oadd] at hnorm
                  exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
      · -- a a limit (fundamental sequence `p`)
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L4 : `g = fun i => ω^(a[i])`, `m = 1`
          have hg' : g = fun i => oadd (p i) 1 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases α with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0, hm1] at hαβ
            rcases lt_oadd_cases hα ((hb0 ▸ hm1 ▸ hβ : NF (oadd a 1 0))) hαβ
              with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, _, hbalt⟩
            · have hnorm_ea : norm ea ≤ x := by
                rw [norm_oadd] at hnorm; exact (le_max_left _ _).trans hnorm
              have hep : ea < p x := iha hβ.fst p ha ea hα.fst hlt hnorm_ea
              exact oadd_lt_oadd_1 hα hep
            · simp only [PNat.one_coe] at hnlt; exact absurd hnlt (by have := na.pos; omega)
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
        · -- L5 : `g = fun i => ω^a·(k+1) + ω^(a[i])`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd (p i) 1 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases α with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hαβ
            rcases lt_oadd_cases hα (hb0 ▸ hβ) hαβ with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hα hlt
            · rw [heq] at hα hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hα (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat := PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                cases ba with
                | zero => exact oadd_pos _ _ _
                | oadd eb nb bb =>
                  have heb : eb.repr < a.repr := by
                    have hbb : (oadd eb nb bb).repr < ω ^ a.repr := hα.snd'.repr_lt
                    have hle : ω ^ eb.repr ≤ (oadd eb nb bb).repr := omega0_le_oadd eb nb bb
                    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hle hbb)
                  have hnorm_eb : norm eb ≤ x := by
                    rw [norm_oadd, norm_oadd] at hnorm
                    exact (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hnorm
                  have hep : eb < p x := iha hβ.fst p ha eb hα.snd.fst (lt_def.2 heb) hnorm_eb
                  exact oadd_lt_oadd_1 hα.snd hep
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
    · -- b a successor ⟹ `oadd a m b` is a successor → contradicts the limit `hg`
      rw [fundamentalSequence_oadd_succ hb] at hg; exact (Sum.inl_ne_inr hg).elim
    · -- L1 : b a limit, `g = fun i => oadd a m (b[i])` ; descend the tail
      have hg' : g = fun i => oadd a m (hbf i) := by
        rw [fundamentalSequence_oadd_limit hb] at hg; exact (Sum.inr.inj hg).symm
      rw [hg']
      cases α with
      | zero => exact oadd_pos _ _ _
      | oadd ea na ba =>
        rcases lt_oadd_cases hα hβ hαβ with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, hnm, hbalt⟩
        · exact oadd_lt_oadd_1 hα hlt
        · exact oadd_lt_oadd_2 hα hnlt
        · subst hnm
          have hnorm_ba : norm ba ≤ x := by
            rw [norm_oadd] at hnorm; exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
          exact oadd_lt_oadd_3 (ihb hβ.snd hbf hb ba hα.snd hbalt hnorm_ba)

/-- **General Bachmann reachability.** For normal-form `α < β`, once the budget `x` is at
least `norm α`, the standard fundamental-sequence descent of `β` reaches `α`:
`Reaches x β α`. Well-founded recursion on `β`: at a successor we step to the predecessor
and recurse (or stop); at a limit the key cofinality bound `lt_fundamentalSequence_of_norm_le`
guarantees `α < g x`, so we step to `g x` and recurse with the same budget. This is the
general engine `fastGrowing_bachmann_reach` only handled for consecutive indices. -/
theorem reaches_of_lt {x : ℕ} :
    ∀ (β : ONote), β.NF → ∀ (α : ONote), α.NF → α < β → norm α ≤ x → Reaches x β α := by
  intro β hβ α hα hαβ hnorm
  rcases e : fundamentalSequence β with (_ | γ) | g
  · exfalso
    have hβ0 : β = 0 := by have hp := fundamentalSequence_has_prop β; rwa [e] at hp
    rw [hβ0] at hαβ
    have hr : α.repr < 0 := by rw [← repr_zero]; exact lt_def.1 hαβ
    exact absurd hr not_lt_zero
  · have hp := fundamentalSequence_has_prop β; rw [e] at hp
    have hγNF : γ.NF := hp.2 hβ
    have hγβ : γ < β := lt_def.2 (by rw [hp.1]; exact Order.lt_succ _)
    have hαr : α.repr ≤ γ.repr := Order.lt_succ_iff.1 (by rw [← hp.1]; exact lt_def.1 hαβ)
    rcases eq_or_lt_of_le hαr with heq | hlt
    · have hαγ : α = γ := (@repr_inj α γ hα hγNF).1 heq
      subst hαγ; exact Reaches.succ e (Reaches.refl _)
    · exact Reaches.succ e (reaches_of_lt γ hγNF α hα (lt_def.2 hlt) hnorm)
  · have hp := fundamentalSequence_has_prop β; rw [e] at hp
    have hgxNF : (g x).NF := (hp.2.1 x).2.2 hβ
    have hgxlt : g x < β := (hp.2.1 x).2.1
    have hαgx : α < g x := lt_fundamentalSequence_of_norm_le β hβ g e α hα hαβ hnorm
    exact Reaches.limit e (reaches_of_lt (g x) hgxNF α hα hαgx hnorm)
termination_by β => β
decreasing_by all_goals assumption

/-- **Strict successor index step.** At a notation-successor `o` (predecessor `a`), the
value strictly increases for arguments `≥ 2`: `f_a(n) < f_o(n)`. Indeed
`f_o n = (f_a)^[n] n ≥ (f_a)^[2] n = f_a (f_a n) > f_a n`, the last step by strict
expansiveness (`lt_fastGrowing`) since `f_a n ≥ n ≥ 1`. (The `≤`-version is
`fastGrowing_le_succ_index`; strictness needs `2 ≤ n` to fit two iterations in.) -/
theorem fastGrowing_lt_succ_index {o a : ONote}
    (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ} (hn : 2 ≤ n) :
    fastGrowing a n < fastGrowing o n := by
  rw [fastGrowing_succ o h]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
  have h1n : 1 ≤ n := le_trans one_le_two hn
  have hge : n ≤ fastGrowing a n := le_fastGrowing a n
  have hlt2 : fastGrowing a n < fastGrowing a (fastGrowing a n) :=
    lt_fastGrowing a (le_trans h1n hge)
  have hstep2 : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
    Function.monotone_iterate_of_id_le hexp hn n
  have h2eq : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  calc fastGrowing a n < fastGrowing a (fastGrowing a n) := hlt2
    _ = (fastGrowing a)^[2] n := h2eq.symm
    _ ≤ (fastGrowing a)^[n] n := hstep2

/-! ### The notation successor `osucc` (for the strict step in index domination)

To bump the `≤` from `Reaches` to a strict `<` we route the descent through the
notation-successor of `o`: `Reaches n (tower n) (osucc o)` plus the strict successor index
step. `osucc` is defined structurally so its `fundamentalSequence` is transparent
(`inl (some o)`). -/

/-- The **notation successor** `osucc o` (with `repr (osucc o) = repr o + 1` and
`fundamentalSequence (osucc o) = inl (some o)` on normal forms). Defined structurally:
increment the finite tail, recursing through the CNF spine. -/
def osucc : ONote → ONote
  | 0 => oadd 0 1 0
  | oadd 0 n _ => oadd 0 (n + 1) 0
  | oadd (oadd e' n' a') m b => oadd (oadd e' n' a') m (osucc b)

theorem repr_osucc : ∀ {o : ONote}, o.NF → (osucc o).repr = o.repr + 1
  | 0, _ => by simp [osucc]
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [repr_zero, opow_zero] at hlt
        exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact lt_one_iff_zero.1 hlt)
      subst ha0
      show (oadd 0 (n + 1) 0).repr = (oadd 0 n 0).repr + 1
      simp only [ONote.repr, opow_zero, one_mul, add_zero, PNat.add_coe,
        PNat.one_coe, Nat.cast_add, Nat.cast_one]
  | oadd (oadd e' n' a') m b, h => by
      show (oadd (oadd e' n' a') m (osucc b)).repr = (oadd (oadd e' n' a') m b).repr + 1
      simp only [ONote.repr]
      rw [repr_osucc h.snd, ← add_assoc]

theorem osucc_NF : ∀ {o : ONote}, o.NF → (osucc o).NF
  | 0, _ => NF.oadd_zero 0 1
  | oadd 0 n _, _ => NF.oadd_zero 0 (n + 1)
  | oadd (oadd e' n' a') m b, h => by
      refine NF.oadd h.fst m (NF.below_of_lt' ?_ (osucc_NF h.snd))
      rw [repr_osucc h.snd, ← Order.succ_eq_add_one]
      have hElim : Order.IsSuccLimit (ω ^ (oadd e' n' a').repr) := by
        refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
        have hpos : (0 : Ordinal) < (oadd e' n' a').repr := by
          rw [← repr_zero]; exact lt_def.1 (oadd_pos e' n' a')
        exact hpos.ne'
      exact hElim.succ_lt h.snd'.repr_lt

theorem fundamentalSequence_osucc : ∀ {o : ONote}, o.NF →
    fundamentalSequence (osucc o) = Sum.inl (some o)
  | 0, _ => rfl
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [repr_zero, opow_zero] at hlt
        exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact lt_one_iff_zero.1 hlt)
      subst ha0
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k.succPNat := ⟨n.natPred, (PNat.succPNat_natPred n).symm⟩
      rfl
  | oadd (oadd e' n' a') m b, h =>
      fundamentalSequence_oadd_succ (fundamentalSequence_osucc h.snd)

theorem norm_osucc_le : ∀ {o : ONote}, norm (osucc o) ≤ norm o + 1
  | 0 => by simp [osucc, norm]
  | oadd 0 n _ => by
      simp only [osucc, norm_oadd, norm_zero, PNat.add_coe, PNat.one_coe]; omega
  | oadd (oadd e' n' a') m b => by
      have ih : norm (osucc b) ≤ norm b + 1 := norm_osucc_le
      simp only [osucc, norm_oadd]; omega

/-- The **diagonal tower** `0, 1, ω, ω^ω, …` underlying `ONote.fastGrowingε₀`:
`tower i = (fun a => ω^a)^[i] 0`. -/
def tower (i : ℕ) : ONote := (fun a => oadd a 1 0)^[i] 0

@[simp] theorem tower_zero : tower 0 = 0 := rfl

/-- `tower (i+1) = ω^{tower i}`. -/
theorem tower_succ (i : ℕ) : tower (i + 1) = oadd (tower i) 1 0 := by
  rw [tower, tower, Function.iterate_succ_apply']

/-- Every tower level is a normal-form notation. -/
theorem tower_NF : ∀ i, (tower i).NF
  | 0 => by rw [tower_zero]; exact NF.zero
  | i + 1 => by rw [tower_succ]; haveI := tower_NF i; exact NF.oadd_zero _ _

/-- The tower is **strictly increasing**: `tower i < tower (i+1) = ω^{tower i}`. The
strictness is exactly `repr_lt_opow_repr` at `tower i`. -/
theorem tower_lt_succ (i : ℕ) : tower i < tower (i + 1) := by
  rw [tower_succ, lt_def]
  have hrepr : ((tower i).oadd 1 0).repr = ω ^ (tower i).repr := by
    simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
  rw [hrepr]
  exact repr_lt_opow_repr _ (tower_NF i)

/-- The tower is monotone in its index. -/
theorem tower_strictMono : StrictMono tower :=
  strictMono_nat_of_lt_succ tower_lt_succ

/-- `repr (tower (i+1)) = ω ^ repr (tower i)`. -/
theorem repr_tower_succ (i : ℕ) : (tower (i + 1)).repr = ω ^ (tower i).repr := by
  rw [tower_succ]
  simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

/-- **Cofinality of the tower in `ε₀`.** Every normal-form notation is below some tower
level. Structural induction: for `o = ω^e·n + a`, the IH gives `e < tower j`, and then
`o < ω^(repr e + 1) ≤ ω^(repr (tower j)) = repr (tower (j+1))`, so `o < tower (j+1)`. -/
theorem tower_cofinal : ∀ (o : ONote), o.NF → ∃ k, o < tower k
  | 0, _ => ⟨1, by rw [lt_def]; simp [tower_succ]⟩
  | oadd e n a, h => by
      obtain ⟨j, hj⟩ := tower_cofinal e h.fst
      refine ⟨j + 1, ?_⟩
      rw [lt_def, repr_tower_succ]
      have hej : e.repr < (tower j).repr := (lt_def).mp hj
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (tower j).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt hej)
      exact lt_of_lt_of_le h1 h2

/-- `fastGrowingε₀ i = f_{tower i}(i)` — the definitional unfolding, as a named lemma. -/
theorem fastGrowingε₀_eq (i : ℕ) : fastGrowingε₀ i = fastGrowing (tower i) i := rfl

/-- **Index domination — the A4 core, proved axiom-clean.** Once a tower level has overtaken
`o` (`o < tower n`), it strictly dominates `o` at the diagonal argument:
`f_o(n) < f_{tower n}(n)`, for `n ≥ 2` past `norm o`. The full Bachmann reachability strength
(`reaches_of_lt`: `tower n` reaches the successor of `o` with budget `n`, generalizing
`fastGrowing_bachmann_reach` from consecutive indices to arbitrary `α < β`) plus one strict
successor step (`fastGrowing_lt_succ_index`). The growth gap of Kirby–Paris independence. -/
theorem fastGrowing_lt_of_lt_tower {o : ONote} (ho : o.NF) (n : ℕ)
    (hn : norm o < n) (h2 : 2 ≤ n) (h : o < tower n) :
    fastGrowing o n < fastGrowing (tower n) n := by
  -- `tower n` is a limit ordinal for `n ≥ 2`: `repr (tower n) = ω^(repr (tower (n-1)))`
  -- with `tower (n-1) > 0`, so `ω^· ` is a limit.
  have hlimit : Order.IsSuccLimit (tower n).repr := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [repr_tower_succ]
    refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
    have hpos : (0 : ONote) < tower j :=
      tower_zero ▸ tower_strictMono (show (0 : ℕ) < j by omega)
    rw [← repr_zero]; exact (lt_def.1 hpos).ne'
  -- Reach the *successor* of `o`, then take one strict successor step.
  have hNF : (osucc o).NF := osucc_NF ho
  have hlt : osucc o < tower n := by
    rw [lt_def, repr_osucc ho, ← Order.succ_eq_add_one]
    exact hlimit.succ_lt (lt_def.1 h)
  have hnorm : norm (osucc o) ≤ n := le_trans norm_osucc_le (by omega)
  have hreach : Reaches n (tower n) (osucc o) :=
    reaches_of_lt (tower n) (tower_NF n) (osucc o) hNF hlt hnorm
  have hle : fastGrowing (osucc o) n ≤ fastGrowing (tower n) n :=
    fastGrowing_le_of_reaches (le_trans one_le_two h2) hreach
  have hstrict : fastGrowing o n < fastGrowing (osucc o) n :=
    fastGrowing_lt_succ_index (fundamentalSequence_osucc ho) h2
  exact lt_of_lt_of_le hstrict hle

/-- **A4 — domination (the headline crux).** Every fixed level of the fast-growing
hierarchy is eventually strictly dominated by `fastGrowingε₀`. Reduced (axiom-clean modulo
the index-domination core) to `tower_cofinal` + `fastGrowing_lt_of_lt_tower`: pick `k` with
`o < tower k`; for `n ≥ max k 1`, `o < tower k ≤ tower n`, so `f_o(n) < f_{tower n}(n) =
fastGrowingε₀ n`. -/
theorem fastGrowing_lt_fastGrowingε₀ (o : ONote) (ho : o.NF) :
    ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n := by
  obtain ⟨k, hk⟩ := tower_cofinal o ho
  refine ⟨max (max k (norm o + 1)) 2, fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨⟨hkn, hnormn⟩, h2n⟩ := hn
  have hlt : o < tower n := lt_of_lt_of_le hk (tower_strictMono.monotone hkn)
  rw [fastGrowingε₀_eq]
  exact fastGrowing_lt_of_lt_tower ho n (by omega) h2n hlt

/-! ### Anti-vacuity anchors for `fastGrowingε₀` (`native_decide`) -/

example : fastGrowingε₀ 0 = 1 := by native_decide
example : fastGrowingε₀ 1 = 2 := by native_decide
example : fastGrowingε₀ 2 = 2048 := by native_decide
-- the tower really is `ω^ω` at level 3 (a genuine limit-of-limits index)
example : tower 3 = oadd (oadd 1 1 0) 1 0 := by native_decide

end LeanFormalizations.Logic.FastGrowing
