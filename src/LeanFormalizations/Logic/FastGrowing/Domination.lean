/-
# A4 — `fastGrowingε₀` dominates every fixed level (the headline domination crux)

The unboundedness that *is* the Goodstein/Kirby–Paris independence content:

> For every notation `o < ε₀`, eventually `fastGrowing o n < fastGrowingε₀ n`.

`fastGrowingε₀` is `mathlib`'s one-step extension of the fast-growing hierarchy to `ε₀`,
built on the *diagonal tower* fundamental sequence `0, 1, ω, ω^ω, ω^ω^ω, …` converging to
`ε₀`:

* `fastGrowingε₀ i = fastGrowing (tower i) i`, where `tower i = (fun a => ω^a)^[i] 0`.

This file pins the tower structure and **states A4**, reducing it to its hard core. With
A1 (`le_fastGrowing`), A2 (`fastGrowing_monotone`) and A3 (`fastGrowing_bachmann_reach`)
all proved axiom-clean in `Basic.lean`, the remaining content of A4 is an **index
domination** fact: each fixed `o` is eventually outgrown because the tower indices climb
past it (the towers are cofinal in `ε₀`).

## Attack plan (the disclosed `sorry` is the index-domination core)
1. **Tower structure** (done here): `tower (i+1) = ω^{tower i}`, `fastGrowingε₀` unfolds to
   `fastGrowing (tower i) i`.
2. **Cofinality** *(open)*: for NF `o`, `∃ k, o < tower k` — the towers exhaust `ε₀`.
   Needs `repr o < ε₀` (from `NF`) and `x < ω^x` for `x < ε₀` (strictness via `NF`).
3. **Index domination** *(open, the core)*: `o < tower n ⟹ fastGrowing o n ≤
   fastGrowing (tower n) n` for `n` past some threshold. The `Reaches`/Bachmann engine
   gives index monotonicity *along fundamental sequences*; lifting it to a general
   `α < β ⟹ eventually f_α ≤ f_β` is the genuine remaining work.
4. **Strictness**: bump `≤` to `<` via one successor step (`lt_fastGrowing`).
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
              exact absurd hr (Ordinal.not_lt_zero _)
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
              exact absurd hr (Ordinal.not_lt_zero _)
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
              exact absurd hr (Ordinal.not_lt_zero _)
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
    exact absurd hr (Ordinal.not_lt_zero _)
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

/-- **Index domination — the sharp remaining A4 core** *(disclosed `sorry`)*. Once a tower
level has overtaken `o` (`o < tower n`), it dominates `o` pointwise at the diagonal
argument: `f_o(n) < f_{tower n}(n)`. This is the full Bachmann reachability strength —
`tower n` reaches every `α < tower n` with budget `n` (generalizing
`fastGrowing_bachmann_reach`, which handles only the consecutive `o[n+1] → o[n]`) — plus
one strict step. It is the last unproved ingredient of the independence growth gap. -/
theorem fastGrowing_lt_of_lt_tower {o : ONote} (n : ℕ) (_hn : 1 ≤ n) (_h : o < tower n) :
    fastGrowing o n < fastGrowing (tower n) n := by
  sorry

/-- **A4 — domination (the headline crux).** Every fixed level of the fast-growing
hierarchy is eventually strictly dominated by `fastGrowingε₀`. Reduced (axiom-clean modulo
the index-domination core) to `tower_cofinal` + `fastGrowing_lt_of_lt_tower`: pick `k` with
`o < tower k`; for `n ≥ max k 1`, `o < tower k ≤ tower n`, so `f_o(n) < f_{tower n}(n) =
fastGrowingε₀ n`. -/
theorem fastGrowing_lt_fastGrowingε₀ (o : ONote) (ho : o.NF) :
    ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n := by
  obtain ⟨k, hk⟩ := tower_cofinal o ho
  refine ⟨max k 1, fun n hn => ?_⟩
  have hkn : k ≤ n := le_trans (le_max_left k 1) hn
  have h1n : 1 ≤ n := le_trans (le_max_right k 1) hn
  have hlt : o < tower n := lt_of_lt_of_le hk (tower_strictMono.monotone hkn)
  rw [fastGrowingε₀_eq]
  exact fastGrowing_lt_of_lt_tower n h1n hlt

/-! ### Anti-vacuity anchors for `fastGrowingε₀` (`native_decide`) -/

example : fastGrowingε₀ 0 = 1 := by native_decide
example : fastGrowingε₀ 1 = 2 := by native_decide
example : fastGrowingε₀ 2 = 2048 := by native_decide
-- the tower really is `ω^ω` at level 3 (a genuine limit-of-limits index)
example : tower 3 = oadd (oadd 1 1 0) 1 0 := by native_decide

end LeanFormalizations.Logic.FastGrowing
