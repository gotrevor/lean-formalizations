/-
Goal: prove `hstep_pred_pow` (the `sorry` at the bottom).

Context (Cichoń's correspondence between Goodstein descents and the Hardy hierarchy):
`hstep o n` is one "budget-incrementing Hardy step" on an ordinal notation `ONote`
(`Mathlib.SetTheory.Ordinal.Notation`): descend through limit stages at argument `n`
until passing exactly one successor. `toONote b p` is the notation of the natural number
`p` written in hereditary base `b` (base read as ω). `bump b n` rewrites base `b ↦ b+1`.

The lemma to prove is the "borrowing" base case: one Hardy step on `ω^δ · c`
(δ = repr of `toONote b L`, `L ≥ 1`) at argument `b` is the notation of `c·(b+1)^(bump b L) − 1`
in base `b+1`. Several supporting facts are provided as `axiom`s (all are theorems already
proved elsewhere); use them freely.

Everything compiles against mathlib as-is except the final `sorry`. Prove it.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Nat.Log

namespace Cichon
open ONote

/-- Hereditary base bump. -/
def bump (b : ℕ) (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

/-- Notation of `n` in hereditary base `b` (base read as ω). -/
def toONote (b : ℕ) (n : ℕ) : ONote :=
  if h : n = 0 then 0
  else oadd (toONote b (Nat.log b n)) (n / b ^ Nat.log b n).toPNat'
        (toONote b (n % b ^ Nat.log b n))
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

/-- One budget-incrementing Hardy step on a notation at argument `n`. -/
def hstep : ONote → ℕ → ONote
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), _ => fun _ => a
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hstep (f n) n
  termination_by o => o

-- ── Supporting facts (all proved elsewhere; usable as given) ──────────────────

axiom hstep_succ (o : ONote) {a : ONote} (h : fundamentalSequence o = Sum.inl (some a)) :
    hstep o = fun _ => a
axiom hstep_limit (o : ONote) {f : ℕ → ONote} (h : fundamentalSequence o = Sum.inr f) :
    hstep o = fun n => hstep (f n) n
/-- Hardy step peels the leading `oadd` term when the tail is nonzero. -/
axiom hstep_oadd_tail (E : ONote) (C : ℕ+) (b : ℕ) (R : ONote) (hR : R ≠ 0) :
    hstep (oadd E C R) b = oadd E C (hstep R b)
/-- Constructor form of `toONote`: for `1 ≤ c < b` and `s < b^e`. -/
axiom toONote_oadd (b : ℕ) (hb : 2 ≤ b) {c e s : ℕ} (hc : 1 ≤ c) (hcb : c < b)
    (hs : s < b ^ e) : toONote b (c * b ^ e + s) = oadd (toONote b e) ⟨c, hc⟩ (toONote b s)
/-- `toONote` is invariant under `bump`. -/
axiom toONote_bump (b : ℕ) (hb : 2 ≤ b) (n : ℕ) : toONote (b + 1) (bump b n) = toONote b n
axiom toONote_zero (b : ℕ) : toONote b 0 = 0
/-- Single digit `1 ≤ d < b`. -/
axiom toONote_single (b : ℕ) (hb : 2 ≤ b) {d : ℕ} (hd1 : 1 ≤ d) (hdb : d < b) :
    toONote b d = oadd 0 ⟨d, hd1⟩ 0
axiom bump_zero (b : ℕ) : bump b 0 = 0
axiom bump_pos_unfold (b n : ℕ) (h : n ≠ 0) :
    bump b n = n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
/-- `r < b^e ⟹ bump b r < (b+1)^(bump b e)`. -/
axiom bump_lt_pow (b : ℕ) (hb : 2 ≤ b) {r e : ℕ} (h : r < b ^ e) : bump b r < (b + 1) ^ bump b e
/-- `toONote b L ≠ 0` for `L ≥ 1`. -/
axiom toONote_ne_zero (b : ℕ) (hb : 2 ≤ b) {L : ℕ} (hL : 1 ≤ L) : toONote b L ≠ 0

-- ── The lemma to prove ────────────────────────────────────────────────────────

/-- **The borrowing base case.** One Hardy step on `ω^δ · c` (δ = repr (toONote b L), L ≥ 1),
at argument `b`, is the notation (base `b+1`) of `c·(b+1)^(bump b L) − 1`. -/
theorem hstep_pred_pow (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (hL : 1 ≤ L)
    (c : ℕ) (hc1 : 1 ≤ c) (hcb : c < b) :
    hstep (oadd (toONote b L) ⟨c, hc1⟩ 0) b = toONote (b + 1) (c * (b + 1) ^ bump b L - 1) := by
  sorry

end Cichon
