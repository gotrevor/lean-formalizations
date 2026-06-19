/-
# The Hardy hierarchy `H_α`

The **Hardy hierarchy** is the companion of the fast-growing hierarchy used in the
Kirby–Paris / Goodstein growth argument. mathlib has `ONote.fastGrowing` but **not**
the Hardy hierarchy at all — this file introduces it, mirroring `fastGrowing`'s
structure on `ONote.fundamentalSequence`:

* `H₀(n) = n`              (identity, vs. `f₀ = succ`)
* `H_{α+1}(n) = H_α(n+1)`  (one step of `+1`, vs. `f_{α+1} n = f_α^[n] n`)
* `H_λ(n) = H_{λ[n]}(n)`   (limit, via the fundamental sequence — same as `fastGrowing`)

It is **computable** (it builds on the computable `fundamentalSequence`), so we can
pin small values with `native_decide` anchors. The classical identity `H_{ω^α} = f_α`
(a long-horizon target, B4) connects it back to `fastGrowing`.

The definition uses the *same* well-founded `<`-recursion on `ONote` that defines
`fastGrowing`; the characterization lemmas `hardy_zero'/_succ/_limit` mirror
`fastGrowing_zero'/_succ/_limit` and are proved the same way (`hardy_def` + `subst`).
-/
import Mathlib.SetTheory.Ordinal.Notation
import LeanFormalizations.Logic.FastGrowing.Basic
import LeanFormalizations.Logic.FastGrowing.Domination

namespace LeanFormalizations.Logic.FastGrowing

open ONote Ordinal

/-- The **Hardy hierarchy** `H_α : ℕ → ℕ` for ordinal notations `< ε₀`:
`H₀ = id`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)` (limit `λ`, via
`ONote.fundamentalSequence`). Same well-founded recursion as `ONote.fastGrowing`. -/
def hardy : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => id
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; exact Order.lt_succ _
      fun n => hardy a (n + 1)
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hardy (f n) n
  termination_by o => o

/-- Unfolding lemma for `hardy`, mirroring `ONote.fastGrowing_def`. -/
theorem hardy_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hardy o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => id
      | Sum.inl (some a), _ => fun n => hardy a (n + 1)
      | Sum.inr f, _ => fun n => hardy (f n) n := by
  subst x
  rw [hardy]

/-- `H_o = id` when `o = 0` (the `inl none` branch). -/
theorem hardy_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    hardy o = id := by
  rw [hardy_def h]

/-- `H_o(n) = H_a(n+1)` when `o` is the successor of `a`. -/
theorem hardy_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hardy o = fun n => hardy a (n + 1) := by
  rw [hardy_def h]

/-- `H_o(n) = H_{o[n]}(n)` when `o` is a limit with fundamental sequence `f`. -/
theorem hardy_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hardy o = fun n => hardy (f n) n := by
  rw [hardy_def h]

/-- `H₀ = id`. -/
@[simp]
theorem hardy_zero : hardy 0 = id :=
  hardy_zero' _ rfl

/-- `H₁(n) = n + 1` — the first successor level just adds one. -/
theorem hardy_one : hardy 1 = fun n => n + 1 := by
  rw [@hardy_succ 1 0 rfl]; funext n; rw [hardy_zero]; rfl

/-- `H₂(n) = n + 2`. -/
theorem hardy_two : hardy 2 = fun n => n + 2 := by
  rw [@hardy_succ 2 1 rfl]; funext n; rw [hardy_one]

/-! ### Growth theory of the Hardy hierarchy -/

/-- **Expansiveness of the Hardy hierarchy.** `n ≤ H_o(n)` for every notation `o`.
Well-founded recursion on `o` (no normal-form hypothesis): `H₀ = id`; the successor
step uses `n ≤ n+1 ≤ H_a(n+1)` and the limit step is the IH at `o[n] < o`. -/
theorem le_hardy (o : ONote) (n : ℕ) : n ≤ hardy o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact le_rfl
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [hardy_succ o e]
    exact le_trans (Nat.le_succ n) (le_hardy a (n + 1))
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [hardy_limit o e]
    exact le_hardy (f n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Value transfer for the Hardy hierarchy.** If `β` structurally reaches `α` at budget
`x` and *every* notation `β` reaches has a monotone Hardy level, then `H_α(x) ≤ H_β(x)`.
Unlike the fast-growing transfer, the successor step `H_β(x) = H_γ(x+1)` shifts the
argument, so it must absorb the `+1` using monotonicity of the intermediate `H_γ` — hence
the monotonicity hypothesis (supplied, in `hardy_monotone`, by the well-founded IH). -/
theorem hardy_le_of_reaches {x : ℕ} {β α : ONote} (h : Reaches x β α) :
    (∀ γ, Reaches x β γ → Monotone (hardy γ)) → hardy α x ≤ hardy β x := by
  induction h with
  | refl a => intro _; exact le_rfl
  | @succ β γ α hb _ ih =>
      intro hmono
      have hmγ : Monotone (hardy γ) := hmono γ (Reaches.succ hb (Reaches.refl γ))
      have ihγ : hardy α x ≤ hardy γ x := ih (fun δ hδ => hmono δ (Reaches.succ hb hδ))
      have heq : hardy β x = hardy γ (x + 1) := by rw [hardy_succ _ hb]
      rw [heq]; exact le_trans ihγ (hmγ (Nat.le_succ x))
  | @limit β α g hb _ ih =>
      intro hmono
      have ihg : hardy α x ≤ hardy (g x) x := ih (fun δ hδ => hmono δ (Reaches.limit hb hδ))
      have heq : hardy β x = hardy (g x) x := by rw [hardy_limit _ hb]
      rw [heq]; exact ihg

/-- **Monotonicity in the argument** of each Hardy level — fully proved, axiom-clean, for
EVERY notation `o`. Well-founded recursion on `o`: the successor case composes the IH at
`a < o`; the limit case combines monotonicity of `H_{o[n]}` (IH) with the index step
`H_{o[n]}(n+1) ≤ H_{o[n+1]}(n+1)`, which is `hardy_le_of_reaches` applied to the structural
Bachmann reach `fastGrowing_bachmann_reach` (every intermediate is `< o`, so the IH supplies
its monotonicity). The same `Reaches` engine that closes the fast-growing crux. -/
theorem hardy_monotone (o : ONote) : Monotone (hardy o) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact Nat.le_succ n
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [hardy_succ o e]
    exact hardy_monotone a (Nat.le_succ (n + 1))
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 n).2.1
    have hltn1 : f (n + 1) < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 (n + 1)).2.1
    rw [hardy_limit o e]
    have mono_fn : Monotone (hardy (f n)) := hardy_monotone (f n)
    have step : hardy (f n) (n + 1) ≤ hardy (f (n + 1)) (n + 1) := by
      apply hardy_le_of_reaches (fastGrowing_bachmann_reach e n)
      intro γ hγ
      have hγo : γ < o := lt_of_le_of_lt (reaches_le hγ) hltn1
      exact hardy_monotone γ
    exact le_trans (mono_fn (Nat.le_succ n)) step
termination_by o
decreasing_by
  · exact hlt
  · exact hlt
  · exact hγo

/-- **Monotonicity in the argument, successor form** `H_o(n) ≤ H_o(n+1)`. -/
theorem hardy_le_succ (o : ONote) (n : ℕ) : hardy o n ≤ hardy o (n + 1) :=
  hardy_monotone o (Nat.le_succ n)

/-- **The Hardy index-monotonicity crux (limit step), now fully proved.** The Hardy
analogue of `fastGrowing_fundSeq_step`: for a limit `o` with fundamental sequence `f`,
`H_{o[n]}(n+1) ≤ H_{o[n+1]}(n+1)`. A corollary of `hardy_le_of_reaches` on the Bachmann
reach, with monotonicity supplied by `hardy_monotone`. -/
theorem hardy_fundSeq_step {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    hardy (f n) (n + 1) ≤ hardy (f (n + 1)) (n + 1) :=
  hardy_le_of_reaches (fastGrowing_bachmann_reach h n) (fun γ _ => hardy_monotone γ)

/-- **Finite-level argument monotonicity for Hardy**, proved cleanly (no crux).
`Monotone (H_k)` for `k : ℕ`: `H_0 = id`; `H_{k+1} = H_k ∘ (·+1)` is monotone as a
composition. -/
theorem hardy_ofNat_monotone (k : ℕ) : Monotone (hardy (ofNat k)) := by
  induction k with
  | zero => simpa [ofNat_zero, hardy_zero] using monotone_id
  | succ k ih =>
      rw [hardy_succ _ (fundamentalSequence_ofNat_succ k)]
      exact ih.comp (monotone_id.add_const 1)

/-- **Finite-level index monotonicity for Hardy** (no positivity needed, unlike
`fastGrowing`): for `m ≤ n`, `H_m(x) ≤ H_n(x)`. Single step: `H_{k+1}(x) = H_k(x+1) ≥
H_k(x)` by `hardy_ofNat_monotone`. -/
theorem hardy_ofNat_mono {m n : ℕ} (hmn : m ≤ n) (x : ℕ) :
    hardy (ofNat m) x ≤ hardy (ofNat n) x := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
      refine le_trans ih ?_
      rw [hardy_succ _ (fundamentalSequence_ofNat_succ n)]
      exact hardy_ofNat_monotone n (Nat.le_succ x)

/-- **Monotonicity of `H_ω`, fully proved (axiom-clean).** The Hardy companion of
`fastGrowing_monotone_omega`: `H_ω(n) = H_{ofNat(n+1)}(n) ≤ H_{ofNat(n+2)}(n+1) =
H_ω(n+1)`, using only finite-level facts (`ω[n] = n+1`). -/
theorem hardy_monotone_omega : Monotone (hardy (oadd 1 1 0)) := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [hardy_limit _ hfs]
  calc hardy (ofNat (n + 1)) n
      ≤ hardy (ofNat (n + 1)) (n + 1) := hardy_ofNat_monotone (n + 1) (Nat.le_succ n)
    _ ≤ hardy (ofNat (n + 2)) (n + 1) := hardy_ofNat_mono (Nat.le_succ (n + 1)) (n + 1)

/-- **General index monotonicity of the Hardy hierarchy.** For normal-form `α < β` and
budget `x ≥ norm α`, `H_α(x) ≤ H_β(x)`. From general reachability (`reaches_of_lt`) and the
Hardy value transfer (`hardy_le_of_reaches`), discharging the latter's monotonicity side
condition with `hardy_monotone` (every Hardy level is monotone). The Hardy companion of
`fastGrowing_le_of_lt`. -/
theorem hardy_le_of_lt {x : ℕ} {α β : ONote} (hα : α.NF) (hβ : β.NF)
    (hαβ : α < β) (hnorm : norm α ≤ x) : hardy α x ≤ hardy β x :=
  hardy_le_of_reaches (reaches_of_lt β hβ α hα hαβ hnorm) (fun γ _ => hardy_monotone γ)

/-- **Closed form for finite Hardy levels:** `H_k(x) = x + k`. Induction on `k`: `H_0 = id`;
`H_{k+1}(x) = H_k(x+1) = (x+1) + k` via the successor step `(k+1)[·] = k`. -/
theorem hardy_ofNat (k x : ℕ) : hardy (ofNat k) x = x + k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    simp only [hardy_succ _ (fundamentalSequence_ofNat_succ k)]
    rw [ih (x + 1)]; omega

/-- **Closed form for `H_ω`.** `H_ω(n) = 2n + 1` — mathlib's `ω[n] = ofNat (n+1)` makes the
limit step land on the finite level `n+1`, so `H_ω(n) = H_{n+1}(n) = n + (n+1) = 2n+1`. (The
`+1` over the classical `H_ω(n)=n` is exactly the `ω[n]=n+1` convention shift.) -/
theorem hardy_omega (n : ℕ) : hardy (oadd 1 1 0) n = 2 * n + 1 := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  have h1 : hardy (oadd 1 1 0) n = hardy (ofNat (n + 1)) n := by
    simp only [hardy_limit _ hfs]
  rw [h1, hardy_ofNat (n + 1) n]
  omega

/-- **First super-linear Hardy lower bound:** `2n ≤ H_{ω^e}(n)` for every nonzero exponent
`e` (and `n ≥ 1`). Every `ω^e` with `e ≠ 0` is `≥ ω`, and the budget `norm ω = 1 ≤ n` is met,
so `H_ω(n) = 2n+1 ≤ H_{ω^e}(n)` by index monotonicity (`hardy_le_of_lt`); the `e = 1` boundary
is `H_ω` itself. A building block: Hardy values at limit indices grow at least linearly with
slope `≥ 2`, the first step past the identity `H₀ = id`. -/
theorem two_mul_le_hardy_pow {e : ONote} (he : e ≠ 0) (hNFe : e.NF) {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ hardy (oadd e 1 0) n := by
  have hNF1 : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  have hNFω : (oadd 1 1 0).NF := NF.oadd hNF1 1 NFBelow.zero
  have hNFe1 : (oadd e 1 0).NF := NF.oadd hNFe 1 NFBelow.zero
  have he_pos : 0 < e.repr := by
    rcases eq_zero_or_pos e.repr with h | h
    · exact absurd ((@repr_inj e 0 hNFe NF.zero).1 (by rw [h, repr_zero])) he
    · exact h
  -- `ω = ω^1 ≤ ω^(repr e)` since `1 ≤ repr e`
  have hle : (oadd 1 1 0).repr ≤ (oadd e 1 0).repr := by
    have hr1 : (oadd 1 1 0).repr = ω ^ (1 : Ordinal) := by simp [ONote.repr]
    have hre : (oadd e 1 0).repr = ω ^ e.repr := by simp [ONote.repr]
    rw [hr1, hre]
    exact opow_le_opow_right omega0_pos (Order.one_le_iff_pos.2 he_pos)
  rcases eq_or_lt_of_le hle with heq | hlt
  · have heqo : oadd 1 1 0 = oadd e 1 0 := (@repr_inj (oadd 1 1 0) (oadd e 1 0) hNFω hNFe1).1 heq
    rw [← heqo, hardy_omega]; omega
  · have hbudget : norm (oadd 1 1 0) ≤ n := by
      have hn1 : norm (oadd 1 1 0) = 1 := by decide
      omega
    have h := hardy_le_of_lt hNFω hNFe1 (lt_def.2 hlt) hbudget
    rw [hardy_omega] at h; omega

/-! ### The Hardy step `hstep` and the step invariant `H_o(n) = H_{hstep o n}(n+1)`

The Hardy hierarchy "counts the steps" of an ordinal descent in which the *argument* grows
by one each time the ordinal drops past a successor. To make that precise we isolate one
**budget-incrementing step** `hstep o n`: descend through limit stages of `o` (each at the
fixed argument `n`) until passing exactly one successor, returning the resulting notation.
The single intrinsic fact we need is then `H_o(n) = H_{hstep o n}(n+1)` (`hardy_hstep`) for
nonzero `o` — the engine that telescopes any unit-step ordinal descent into a Hardy value.
This is the FastGrowing-side prerequisite for C3 (`Goodstein/Growth.lean`), where the
Goodstein descent is shown to *be* this Hardy step (`hstep_seqONote`). -/

/-- The fundamental sequence of a limit notation is everywhere nonzero: every branch of
`ONote.fundamentalSequence` for a limit returns `fun i => oadd …`, and `oadd` is positive.
Needed so the limit recursion of `hstep`/`hardy_hstep` never collapses to `0` prematurely. -/
theorem fundamentalSequence_inr_ne_zero {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (i : ℕ) : f i ≠ 0 := by
  induction o with
  | zero => simp [fundamentalSequence] at h
  | oadd a m b iha ihb =>
    rw [fundamentalSequence] at h
    split at h
    · injection h with h'; subst h'; exact (oadd_pos _ _ _).ne'
    · exact (Sum.inl_ne_inr h).elim
    · split at h <;>
        first
          | exact (Sum.inl_ne_inr h).elim
          | (injection h with h'; subst h'; simp only []; exact (oadd_pos _ _ _).ne')

/-- One budget-incrementing **Hardy step** on a notation at argument `n`: descend through
limit stages (each at argument `n`) until passing exactly one successor; `hstep 0 n = 0`.
Same well-founded `<`-recursion on `ONote` as `hardy`/`fastGrowing`. -/
def hstep : ONote → ℕ → ONote
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), _ => fun _ => a
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hstep (f n) n
  termination_by o => o

/-- Unfolding lemma for `hstep`, mirroring `hardy_def`. -/
theorem hstep_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hstep o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ONote)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => fun _ => 0
      | Sum.inl (some a), _ => fun _ => a
      | Sum.inr f, _ => fun n => hstep (f n) n := by
  subst x; rw [hstep]

/-- `hstep o = fun _ => a` when `o` is the successor of `a`. -/
theorem hstep_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hstep o = fun _ => a := by rw [hstep_def h]

/-- `hstep o = fun n => hstep (o[n]) n` when `o` is a limit with fundamental sequence `f`. -/
theorem hstep_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hstep o = fun n => hstep (f n) n := by rw [hstep_def h]

/-- **Intrinsic Hardy step invariant.** For a nonzero notation, one budget-incrementing
Hardy step preserves the Hardy value: `H_o(n) = H_{hstep o n}(n+1)`. The successor case is
definitional (`H_{a+1}(n) = H_a(n+1)`); the limit case recurses (each fundamental-sequence
member is nonzero by `fundamentalSequence_inr_ne_zero`, so the IH applies). -/
theorem hardy_hstep (o : ONote) (n : ℕ) (h : o ≠ 0) :
    hardy o n = hardy (hstep o n) (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · exact absurd ((fundamentalSequenceProp_inl_none o).1 (e ▸ fundamentalSequence_has_prop o)) h
  · rw [hardy_succ o e, hstep_succ o e]
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact (hp.2.1 n).2.1
    rw [hardy_limit o e, hstep_limit o e]
    exact hardy_hstep (f n) n (fundamentalSequence_inr_ne_zero e n)
termination_by o
decreasing_by exact hlt

/-- **Peeling the leading term of a Hardy step.** When the tail `R` is nonzero, a Hardy step
on `oadd E C R` happens entirely inside the tail: `hstep (oadd E C R) b = oadd E C (hstep R b)`.
Well-founded induction on `R` (its `ONote <`, via `InvImage repr`): if `R` is a successor the
step peels directly; if `R` is a limit the step descends to `R[b] ≠ 0 < R` and the IH applies.
The actual decrement only occurs once `R = 0`. -/
theorem hstep_oadd_tail (E : ONote) (C : ℕ+) (b : ℕ) :
    ∀ R, R ≠ 0 → hstep (oadd E C R) b = oadd E C (hstep R b) := by
  intro R
  induction R using (InvImage.wf repr Ordinal.lt_wf).induction with
  | _ R ih =>
    intro hR
    rcases e : fundamentalSequence R with (_ | R') | g
    · exact absurd ((fundamentalSequenceProp_inl_none R).1 (e ▸ fundamentalSequence_has_prop R)) hR
    · rw [hstep_succ _ (fundamentalSequence_oadd_succ e), hstep_succ _ e]
    · rw [hstep_limit _ (fundamentalSequence_oadd_limit e), hstep_limit _ e]
      have hgb : g b ≠ 0 := fundamentalSequence_inr_ne_zero e b
      have hglt : g b < R := by
        have hp := fundamentalSequence_has_prop R; rw [e] at hp; exact (hp.2.1 b).2.1
      exact ih (g b) (lt_def.1 hglt) hgb

/-! ### Anti-vacuity anchors (`native_decide`)

Standalone witnesses, off any headline axiom path, that a *wrong* definition of
`hardy` would fail to satisfy. They pin both the successor branch (`H_k(n) = n + k`)
and the limit branch: mathlib's fundamental sequence for `ω` is `ω[n] = n + 1`, so
`H_ω(n) = H_{n+1}(n) = n + (n+1) = 2n + 1`. -/

example : hardy 0 5 = 5 := by native_decide
example : hardy 1 5 = 6 := by native_decide
example : hardy 2 5 = 7 := by native_decide
example : hardy 3 5 = 8 := by native_decide
example : hardy 4 5 = 9 := by native_decide
-- limit branch: `H_ω(n) = 2n + 1` (`ω = oadd 1 1 0`, `ω[n] = n + 1`)
example : hardy (oadd 1 1 0) 2 = 5 := by native_decide
example : hardy (oadd 1 1 0) 4 = 9 := by native_decide
example : hardy (oadd 1 1 0) 6 = 13 := by native_decide
-- the new closed forms / lower bound, witnessed concretely (a wrong proof would mis-evaluate):
example : hardy (ofNat 4) 5 = 5 + 4 := by native_decide       -- hardy_ofNat
example : hardy (oadd 1 1 0) 6 = 2 * 6 + 1 := by native_decide -- hardy_omega
example : 2 * 2 ≤ hardy (oadd (oadd 0 2 0) 1 0) 2 := by native_decide -- two_mul_le_hardy_pow at ω²: 4 ≤ 23
-- `hstep`: successor drops one level; `ω` at budget `3` descends to `ω[3]=4` then to `3`.
example : hstep 5 0 = 4 := by native_decide
example : hstep (oadd 1 1 0) 3 = 3 := by native_decide
-- the step invariant in action: `H_ω(3) = H_{hstep ω 3}(4) = H_3(4)`
example : hardy (oadd 1 1 0) 3 = hardy (hstep (oadd 1 1 0) 3) 4 := by native_decide

/-- **Hardy tail-peeling — the additive law, ONote-native form.** Splitting off the tail of an `oadd`
composes the Hardy functions: `hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n)` (i.e.
`H_{ω^{repr a}·m + repr b}(n) = H_{ω^{repr a}·m}(H_{repr b}(n))`, valid since the tail `b` cannot absorb
the leading term). By well-founded recursion on the tail `b` — the same recursion `hardy`/
`fundamentalSequence` use (the fund. seq. of `oadd a m b` acts on the tail `b`): the successor and
limit tail cases each reduce to the IH at the smaller tail; the `b = 0` case is `hardy 0 = id`. No
ordinal-addition machinery needed — purely structural.

This is the **non-absorbing Hardy additive law** (the general `H_{α+β}=H_α∘H_β` is false —
`1+ω=ω` makes `H_{1+ω}=H_ω ≠ H_1∘H_ω`). It is the key brick for the coefficient lemma
`H_{ω^β·j} = (H_{ω^β})^[j]` and hence for B4 (`H_{ω^α} = f_α` at finite `α`). -/
theorem hardy_oadd_tail (a : ONote) (m : ℕ+) (b : ONote) (n : ℕ) :
    hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n) := by
  rcases e : fundamentalSequence b with (_ | b') | f
  · have hb0 : b = 0 := by
      have hp := fundamentalSequence_has_prop b; rw [e] at hp; simpa using hp
    rw [hardy_zero' b e, hb0]; rfl
  · have hlt : b' < b := by
      have hp := fundamentalSequence_has_prop b; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    have hfs : fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_succ _ hfs, hardy_succ b e]
    exact hardy_oadd_tail a m b' (n + 1)
  · have hlt : f n < b := by
      have hp := fundamentalSequence_has_prop b; rw [e] at hp
      exact (hp.2.1 n).2.1
    have hfs : fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (f i)) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_limit _ hfs, hardy_limit b e]
    exact hardy_oadd_tail a m (f n) n
termination_by b
decreasing_by all_goals exact hlt

/-- Anti-vacuity for `hardy_oadd_tail`: `H_{ω·2 + 1}(2) = H_{ω·2}(H_1(2)) = H_{ω·2}(3)`. -/
example : hardy (oadd 1 2 1) 2 = hardy (oadd 1 2 0) (hardy 1 2) := hardy_oadd_tail 1 2 1 2

/-- **Coefficient step.** Bumping the coefficient of `ω^β` by one composes with `H_{ω^β}`:
`H_{ω^β·(j+1)}(x) = H_{ω^β·j}(H_{ω^β}(x))` (for `β ≠ 0`). Case `β` succ/limit, compute the
fundamental sequence of `oadd β (j+1) 0` (its `[x]` is `ω^β·j + (ω^β)[x]`, an `oadd β j _`), then
peel the tail with `hardy_oadd_tail`. -/
theorem hardy_oadd_coeff_step (β : ONote) (hβ : β ≠ 0) (k x : ℕ) :
    hardy (oadd β (k + 1).succPNat 0) x
      = hardy (oadd β k.succPNat 0) (hardy (oadd β 1 0) x) := by
  rcases e : fundamentalSequence β with (_ | β') | f
  · exfalso; apply hβ
    have hp := fundamentalSequence_has_prop β; rw [e] at hp; simpa using hp
  · have hfs : fundamentalSequence (oadd β (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd β k.succPNat (oadd β' i.succPNat 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    show hardy (oadd β k.succPNat (oadd β' x.succPNat 0)) x
        = hardy (oadd β k.succPNat 0) (hardy (oadd β 1 0) x)
    rw [hardy_oadd_tail β k.succPNat (oadd β' x.succPNat 0) x,
        hardy_limit (oadd β 1 0) (fundamentalSequence_omega_pow_succ e)]
  · have hfs : fundamentalSequence (oadd β (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd β k.succPNat (oadd (f i) 1 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    show hardy (oadd β k.succPNat (oadd (f x) 1 0)) x
        = hardy (oadd β k.succPNat 0) (hardy (oadd β 1 0) x)
    rw [hardy_oadd_tail β k.succPNat (oadd (f x) 1 0) x,
        hardy_limit (oadd β 1 0) (fundamentalSequence_omega_pow_limit e)]

/-- **The coefficient lemma `H_{ω^β·j} = (H_{ω^β})^[j]`** (`β ≠ 0`, `j = k+1`):
`hardy (oadd β (k+1) 0) x = (hardy (oadd β 1 0))^[k+1] x`. By induction on `k` via the step. -/
theorem hardy_oadd_coeff (β : ONote) (hβ : β ≠ 0) (k x : ℕ) :
    hardy (oadd β k.succPNat 0) x = (hardy (oadd β 1 0))^[k + 1] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [hardy_oadd_coeff_step β hβ k x, ih (hardy (oadd β 1 0) x), ← Function.iterate_succ_apply]

/-- Iterate-offset transfer: if `g y + 1 = F (y+1)` for all `y`, then `g^[m] y + 1 = F^[m] (y+1)`. -/
theorem iterate_offset {g F : ℕ → ℕ} (h : ∀ y, g y + 1 = F (y + 1)) (m y : ℕ) :
    g^[m] y + 1 = F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (g y), h y]

private theorem ofNat_succ_ne_zero (k : ℕ) : (ofNat (k + 1) : ONote) ≠ 0 := by
  rw [ofNat_succ]; intro h; exact ONote.noConfusion h

private theorem hardy_omega_pow_ofNat_succ (k x : ℕ) :
    hardy (oadd (ofNat (k + 1)) 1 0) x + 1 = fastGrowing (ofNat (k + 1)) (x + 1) := by
  induction k generalizing x with
  | zero =>
    show hardy (oadd 1 1 0) x + 1 = fastGrowing 1 (x + 1)
    rw [hardy_omega, fastGrowing_one]
    show 2 * x + 1 + 1 = 2 * (x + 1)
    omega
  | succ k ih =>
    rw [fastGrowing_succ _ (fundamentalSequence_ofNat_succ (k + 1)),
        hardy_limit _ (fundamentalSequence_omega_pow_succ (fundamentalSequence_ofNat_succ (k + 1)))]
    show hardy (oadd (ofNat (k + 1)) x.succPNat 0) x + 1
        = (fastGrowing (ofNat (k + 1)))^[x + 1] (x + 1)
    rw [hardy_oadd_coeff (ofNat (k + 1)) (ofNat_succ_ne_zero k) x x]
    exact iterate_offset ih (x + 1) x

/-- **B4 at finite levels: `H_{ω^k}(n) + 1 = f_k(n+1)`** for every `k : ℕ`. The classical Hardy↔
fast-growing identity `H_{ω^α} = f_α`, made precise under mathlib's `ω[n]=n+1` fundamental-sequence
convention — which shifts it by the `+1`/argument-bump seen here. (NB: the clean identity is special to
*finite/successor* exponents; at limit `α` the convention makes `H_{ω^α}` and `f_α` pick different
levels — e.g. `H_{ω^ω}(1)+1 = 8 ≠ f_ω(2) = 2048`.) Proof: induction on `k` from the `ω` base
(`hardy_omega`), the coefficient lemma turning `(ω^{k+1})[x] = ω^k·(x+1)` into `(H_{ω^k})^[x+1]`, and
`iterate_offset` carrying the `+1` through the iteration against `f_{k+1} = (f_k)^[·]`. -/
theorem hardy_omega_pow_ofNat (k x : ℕ) :
    hardy (oadd (ofNat k) 1 0) x + 1 = fastGrowing (ofNat k) (x + 1) := by
  cases k with
  | zero =>
    show hardy (oadd 0 1 0) x + 1 = fastGrowing 0 (x + 1)
    rw [show (oadd 0 1 0 : ONote) = 1 from rfl, hardy_one, fastGrowing_zero]
  | succ k => exact hardy_omega_pow_ofNat_succ k x

-- anti-vacuity: B4 at `ω^2` — `H_{ω^2}(2) + 1 = 23 + 1 = 24 = f_2(3)`
example : hardy (oadd (ofNat 2) 1 0) 2 + 1 = fastGrowing (ofNat 2) 3 := by native_decide

/-- **Hardy is dominated by fast-growing at the same index.** For `n ≥ 2`,
`hardy o n ≤ fastGrowing o n` (no `NF` needed). By well-founded recursion on the notation, mirroring
`le_fastGrowing`: the limit case is the IH verbatim; the successor case chains
`H_o(n) = H_a(n+1) ≤ f_a(n+1) ≤ f_a(f_a n) = (f_a)^[2] n ≤ (f_a)^[n] n = f_o(n)` (IH at `a`, then
`f_a` monotone via `n+1 ≤ f_a n` from `lt_fastGrowing`, then iterate-count monotone for `n ≥ 2`).

The two hierarchies the expedition built are comparable: the Hardy hierarchy (the Goodstein-length
side, via the Cichoń identity `goodsteinLength m = H_{o_m}(2) − 2`) never outruns the fast-growing
hierarchy at the same ordinal index. A reusable bridge toward the matching *upper* bound and `B4`. -/
theorem hardy_le_fastGrowing (o : ONote) (n : ℕ) (hn : 2 ≤ n) :
    hardy o n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e, fastGrowing_zero' o e]; simp
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [hardy_succ o e, fastGrowing_succ o e]
    have ih : hardy a (n + 1) ≤ fastGrowing a (n + 1) := hardy_le_fastGrowing a (n + 1) (by omega)
    have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    have hmono : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
      Function.monotone_iterate_of_id_le hexp hn n
    have h2it : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
    have hfn : n + 1 ≤ fastGrowing a n := lt_fastGrowing a (by omega)
    have hstep : fastGrowing a (n + 1) ≤ fastGrowing a (fastGrowing a n) := fastGrowing_monotone a hfn
    calc hardy a (n + 1) ≤ fastGrowing a (n + 1) := ih
      _ ≤ fastGrowing a (fastGrowing a n) := hstep
      _ = (fastGrowing a)^[2] n := h2it.symm
      _ ≤ (fastGrowing a)^[n] n := hmono
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [hardy_limit o e, fastGrowing_limit o e]
    exact hardy_le_fastGrowing (f n) n hn
termination_by o
decreasing_by all_goals exact hlt

/-- Anti-vacuity for `hardy_le_fastGrowing` at a genuine limit: `H_ω(2) = 5 ≤ f_ω(2) = 2048`. -/
example : hardy (oadd 1 1 0) 2 ≤ fastGrowing (oadd 1 1 0) 2 := hardy_le_fastGrowing _ _ (by norm_num)

end LeanFormalizations.Logic.FastGrowing
