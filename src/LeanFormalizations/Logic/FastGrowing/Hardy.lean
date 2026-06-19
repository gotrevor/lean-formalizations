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

namespace LeanFormalizations.Logic.FastGrowing

open ONote

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

end LeanFormalizations.Logic.FastGrowing
