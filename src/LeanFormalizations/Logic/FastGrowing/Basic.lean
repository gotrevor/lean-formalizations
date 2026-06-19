/-
# Growth theory of the fast-growing hierarchy

`Mathlib.SetTheory.Ordinal.Notation` already provides the **fast-growing hierarchy**
on ordinal notations below `ε₀`:

* `ONote.fastGrowing : ONote → ℕ → ℕ`  with `f₀ = succ`, `f_{α+1} = fun n => f_α^[n] n`,
  `f_λ = fun n => f_{λ[n]} n` (limit `λ`, via `ONote.fundamentalSequence`);
* `ONote.fastGrowingε₀ : ℕ → ℕ`, the one-step extension to `ε₀` itself.

mathlib proves the *small values* (`fastGrowing_one = (2 * ·)`, `fastGrowing_two = fun n => 2^n * n`,
`fastGrowingε₀_zero = 1`, `fastGrowingε₀_one = 2`) but **none of the growth theory**:
no expansiveness, no monotonicity, no domination. Those are exactly the facts the
Kirby–Paris growth argument needs, and they are the targets here.

These lemmas are mathlib-PR-shaped (they belong next to `ONote.fastGrowing`); developing
them here both serves the Goodstein-independence growth content and is independently useful.

## Normal-form hypotheses
`fastGrowing` is total on all of `ONote`, but the intended (and provable) statements
hold for **normal-form** notations (`ONote.NF`). Carry `[o.NF]`/`(h : o.NF)` where the
proof needs it; the `fundamentalSequence` correctness lemmas
(`ONote.fundamentalSequence_has_prop`, `ONote.FundamentalSequenceProp`) and the
`fastGrowing_zero'/_succ/_limit` characterizations are the entry points.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Iterate

namespace LeanFormalizations.Logic.FastGrowing

open ONote

/-- **Expansiveness.** Every level of the fast-growing hierarchy dominates the
identity: `n ≤ f_o(n)` for every notation `o` (no normal-form hypothesis needed —
`fundamentalSequence_has_prop` holds for all `o`).

Proof by well-founded recursion on `o` (the same `<`-recursion that *defines*
`fastGrowing`), via the three characterizations `fastGrowing_zero'/_succ/_limit`:
* `o = 0`: `f_o = Nat.succ`, so `n ≤ n+1`.
* successor `o = a+1`: `f_o n = (f_a)^[n] n`; by IH `id ≤ f_a`, and iterating a
  function that dominates the identity stays `≥ id` (`id_le_iterate_of_id_le`).
* limit: `f_o n = f_{o[n]} n` with `o[n] < o`, so the IH applies directly. -/
theorem le_fastGrowing (o : ONote) (n : ℕ) : n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · -- `o = 0`: `fastGrowing o = Nat.succ`
    rw [fastGrowing_zero' o e]
    exact Nat.le_succ n
  · -- successor: `fastGrowing o n = (fastGrowing a)^[n] n`, `a < o`
    have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    have ih : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    exact Function.id_le_iterate_of_id_le ih n n
  · -- limit: `fastGrowing o n = fastGrowing (f n) n`, `f n < o`
    have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    exact le_fastGrowing (f n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Strict expansiveness for positive input.** For `n ≥ 1` every level strictly
exceeds the identity, `n < f_o(n)`.

Same well-founded recursion as `le_fastGrowing`:
* `o = 0`: `f_o n = n+1 > n`.
* successor: `n < f_a n` (strict IH) and `f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
  (iterate count is monotone for `id ≤ f_a`, and `1 ≤ n`).
* limit: `n < f_{o[n]} n` directly by the strict IH at `o[n] < o`. -/
theorem lt_fastGrowing (o : ONote) {n : ℕ} (hn : 1 ≤ n) : n < fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [fastGrowing_zero' o e]
    exact Nat.lt_succ_self n
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    -- `n < f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
    have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    have hstep : fastGrowing a n ≤ (fastGrowing a)^[n] n := by
      have hmono := Function.monotone_iterate_of_id_le hexp hn
      simpa using hmono n
    exact lt_of_lt_of_le (lt_fastGrowing a hn) hstep
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    exact lt_fastGrowing (f n) hn
termination_by o
decreasing_by all_goals exact hlt

/-- **Index step at a successor** (a genuine A3 stepping stone, proved directly).
If `o` is the successor of `a` (`fundamentalSequence o = inl (some a)`), then for a
positive argument the next index can only grow the value:
`f_a(n) ≤ f_o(n)`. Indeed `f_o n = (f_a)^[n] n ≥ (f_a)^[1] n = f_a n` once `1 ≤ n`. -/
theorem fastGrowing_le_succ_index {o a : ONote}
    (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ} (hn : 1 ≤ n) :
    fastGrowing a n ≤ fastGrowing o n := by
  rw [fastGrowing_succ o h]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
  simpa using (Function.monotone_iterate_of_id_le hexp hn) n

/-- The fundamental sequence of a successor *natural-number* notation is its
predecessor: `(k+1)[·] = k`. (Both branches reduce to `rfl`.) -/
theorem fundamentalSequence_ofNat_succ (k : ℕ) :
    fundamentalSequence (ofNat (k + 1)) = Sum.inl (some (ofNat k)) := by
  cases k with
  | zero => rfl
  | succ k' => rfl

/-- **Finite-level index monotonicity** — the base case of the whole index
hierarchy, fully proved. For natural-number levels `m ≤ n` and positive argument,
`f_m(x) ≤ f_n(x)`. Telescopes `fastGrowing_le_succ_index` along
`fundamentalSequence_ofNat_succ`.

This is exactly the comparison the limit case needs whenever the fundamental
sequence lands on finite levels (e.g. `ω[n] = n+1`), so it discharges the index
crux for `o = ω` and is the seed for the general CNF induction. -/
theorem fastGrowing_ofNat_mono {m n : ℕ} (hmn : m ≤ n) {x : ℕ} (hx : 1 ≤ x) :
    fastGrowing (ofNat m) x ≤ fastGrowing (ofNat n) x := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
      exact le_trans ih (fastGrowing_le_succ_index (fundamentalSequence_ofNat_succ n) hx)

/-- **The index-monotonicity crux (A3), limit step.**  *(disclosed `sorry` — this is
the genuine hard core of the growth theory, banged on across laps.)*

For a limit notation `o` with fundamental sequence `f` (`o[i] = f i`), stepping from
index `f n` to the next index `f (n+1)` does not decrease the value at the argument
`n+1`:  `f_{o[n]}(n+1) ≤ f_{o[n+1]}(n+1)`.

This is the single inequality the monotonicity proof needs in the limit case (the
argument `n+1` outpaces the index norm, which is exactly why the classical
Wainer/Cichoń–Wainer proof works here). The successor analogue is
`fastGrowing_le_succ_index` (proved). Reducing `fastGrowing_le_succ`/`fastGrowing_monotone`
to *this* statement isolates all remaining difficulty into one clean lemma. -/
theorem fastGrowing_fundSeq_step {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    fastGrowing (f n) (n + 1) ≤ fastGrowing (f (n + 1)) (n + 1) := by
  sorry

/-- **Monotonicity in the argument, successor form** `f_o(n) ≤ f_o(n+1)`.
Well-founded recursion on `o`; the limit case is reduced to the single crux
`fastGrowing_fundSeq_step`, everything else is `le_fastGrowing` + iterate monotonicity. -/
theorem fastGrowing_le_succ (o : ONote) (n : ℕ) :
    fastGrowing o n ≤ fastGrowing o (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | g
  · rw [fastGrowing_zero' o e]
    exact Nat.le_succ _
  · -- successor: `(f_a)^[n] n ≤ (f_a)^[n+1] (n+1)`
    have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    have hmono_a : Monotone (fastGrowing a) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ a k
    calc (fastGrowing a)^[n] n
        ≤ (fastGrowing a)^[n] (n + 1) := hmono_a.iterate n (Nat.le_succ n)
      _ ≤ (fastGrowing a)^[n + 1] (n + 1) := by
            rw [Function.iterate_succ_apply']
            exact le_fastGrowing a _
  · -- limit: `f_{g n}(n) ≤ f_{g (n+1)}(n+1)`
    have hlt : g n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    have hmono_gn : Monotone (fastGrowing (g n)) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ (g n) k
    calc fastGrowing (g n) n
        ≤ fastGrowing (g n) (n + 1) := hmono_gn (Nat.le_succ n)
      _ ≤ fastGrowing (g (n + 1)) (n + 1) := fastGrowing_fundSeq_step e n
termination_by o
decreasing_by all_goals exact hlt

/-- **Monotonicity in the argument.** Each level `f_o` is a monotone function of `n`.
Immediate from `fastGrowing_le_succ` via `monotone_nat_of_le_succ`. -/
theorem fastGrowing_monotone (o : ONote) : Monotone (fastGrowing o) :=
  monotone_nat_of_le_succ (fastGrowing_le_succ o)

end LeanFormalizations.Logic.FastGrowing
