/-
# The growth theorem: `goodsteinLength` grows like `f_{ε₀}` — Cichoń's lower bound (audit surface)

**Designated audit surface for the growth headline (C3 of `DIRECTION.md`).** The proof lives in
`TowerDomination.lean` and its siblings; this file states the headline thinly and faithfully, the way
`Statement.lean` does for termination.

## What this says (the mathematical heart of Kirby–Paris)
Goodstein's theorem (termination) is proved in `Statement.lean`. Its *companion* — why Peano
Arithmetic cannot prove it (Kirby–Paris 1982) — rests on a growth gap: every PA-provably-total
function is dominated by some `f_α` with `α < ε₀`, while the Goodstein length function outgrows all of
them. The PA-syntactic statement is out of scope (see `Statement.lean` / `README.md`); the *growth
gap itself*, which lives entirely in mathlib, is the content here.

**`goodsteinLength_eventually_dominates_fastGrowing`**: for EVERY ordinal notation `o < ε₀` (every
normal-form `ONote`), `goodsteinLength` eventually dominates the fast-growing function `f_o`:
`∃ N, ∀ m ≥ N, fastGrowing o m ≤ goodsteinLength m + 2`. Since every PA-provably-total function is
dominated by some such `f_o`, `goodsteinLength` outgrows every PA-provably-total function — the formal
"Goodstein grows too fast for PA." The additive `+ 2` is the standard constant from Cichoń's identity
`goodsteinLength m = H_{o_m}(2) − 2`; the statement is domination up to `O(1)`.

This is Cichoń's lower bound in full: not merely along the `ω`-power tower `ω↑↑k` (which is cofinal in
`ε₀`), but at *every* ordinal below `ε₀`.

## Proof (delegated)
`TowerDomination.lean`: the descent ordinal of the base-2 Goodstein run stays above `ω↑↑(k+1)` for
`≈ m` steps (general ordinal bridge `omegaTower_succ_le_seqONote_repr`), where `k` is chosen by tower
cofinality (`exists_repr_lt_omegaTower`: every `o < ε₀` is below some `ω↑↑k`). The step count is
supplied by the general length bootstrap `two_mul_le_goodsteinLength_iter`, itself powered by the
already-proved `o = ω` domination and the clean finite-level tower bound `towerN_le_fastGrowing`. The
diagonal reduction `goodstein_dominates_of_index_le` (the Cichoń pipeline through the Hardy hierarchy)
closes it.

## Axioms
The unconditional closures carry the bare trust base `[propext, Classical.choice, Quot.sound]` plus
the finite-base-case `native_decide` artifacts (the computed lengths of the finitely many small
Goodstein runs `4 ≤ M < 16`) — a 🟢 finite/computational dependency, excluded from the math-axiom
count per the discharge doctrine. There are **no math axioms** and **no `sorry`**.
-/
import LeanFormalizations.Logic.Goodstein.TowerDomination

namespace LeanFormalizations.Logic.Goodstein

open ONote Ordinal
open LeanFormalizations.Logic.FastGrowing

/-- **THE GROWTH HEADLINE (C3) — Cichoń's lower bound, complete to ε₀.** For every ordinal notation
`o < ε₀` (every normal-form `ONote`), `goodsteinLength` eventually dominates `f_o`:
`∃ N, ∀ m ≥ N, fastGrowing o m ≤ goodsteinLength m + 2`. The thin, faithful audit statement;
the proof is `TowerDomination.goodsteinLength_eventually_dominates_fastGrowing`. -/
theorem goodsteinLength_dominates_fastGrowing {o : ONote} (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2 :=
  goodsteinLength_eventually_dominates_fastGrowing ho

/-- **`towerO` IS mathlib's `ε₀` fundamental sequence.** The iterate `(a ↦ ω^a)` from `0` that defines
`fastGrowingε₀` (mathlib's one-step extension to `ε₀`) is exactly our `towerO`:
`(fun a => oadd a 1 0)^[k+1] 0 = towerO k`. Faithfulness anchor: the tower domination really targets
the genuine `ε₀` hierarchy `ω, ω^ω, ω^{ω^ω}, …`. -/
theorem iterate_oadd_eq_towerO (k : ℕ) : (fun a => ONote.oadd a 1 0)^[k + 1] 0 = towerO k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- Consequently `fastGrowingε₀ (k+1) = fastGrowing (towerO k) (k+1)`: mathlib's `ε₀`-level function
is the diagonal over our tower. (Its *level* `k` grows with the argument, so this diagonal is genuinely
`ε₀`-fast and is NOT what the per-level headline dominates — the headline dominates each *fixed* `f_o`,
the faithful reading of "tracks `f_{ε₀}`".) -/
theorem fastGrowingε₀_eq_towerO (k : ℕ) :
    ONote.fastGrowingε₀ (k + 1) = fastGrowing (towerO k) (k + 1) := by
  rw [ONote.fastGrowingε₀, iterate_oadd_eq_towerO]

/-- **The matching UPPER bound.** `goodsteinLength m + 2 ≤ f_{o_m}(2)`, where `o_m = seqONote m 0` is
the base-2 ordinal of `m` (`= toONote 2 m`). Immediate from the Cichoń identity
`goodsteinLength m + 2 = H_{o_m}(2)` (`hardy_seqONote_zero`) and `hardy_le_fastGrowing` (Hardy ≤
fast-growing at the same index). Together with `goodsteinLength_dominates_fastGrowing` this squeezes
`goodsteinLength` inside the fast-growing hierarchy at the `ε₀` frontier — the two-sided "grows like
`f_{ε₀}`": from below it eventually beats every fixed `f_o` (`o < ε₀`); from above it never exceeds
`f` at its own ordinal `o_m < ε₀` (argument `2`). -/
theorem goodsteinLength_le_fastGrowing_ordinal (m : ℕ) :
    goodsteinLength m + 2 ≤ fastGrowing (seqONote m 0) 2 := by
  rw [← hardy_seqONote_zero m]
  exact hardy_le_fastGrowing (seqONote m 0) 2 (by norm_num)

/-- **THE TWO-SIDED CAPSTONE — "`goodsteinLength` grows like `f_{ε₀}`".** Packaging both directions as
the single definitive audit surface: for every `o < ε₀` (every NF `ONote`),
* **(lower)** `goodsteinLength` eventually dominates `f_o`: `∃ N, ∀ m ≥ N, f_o(m) ≤ goodsteinLength m + 2`;
* **(upper)** `goodsteinLength` never exceeds `f` at its own base-2 ordinal: `goodsteinLength m + 2 ≤
  f_{o_m}(2)` for all `m`.
So `goodsteinLength` sits exactly within the fast-growing hierarchy at the `ε₀` frontier — the formal
"Goodstein grows too fast for PA" (every PA-provably-total function is some `f_o`, `o < ε₀`; all are
eventually dominated). The exact Hardy pin is `hardy_seqONote_zero` (Cichoń) + `hardy_omega_pow_ofNat`
(B4, `H_{ω^k}=f_k`). -/
theorem goodsteinLength_grows_like_fastGrowingε₀ :
    (∀ (o : ONote), o.NF → ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2)
    ∧ (∀ m, goodsteinLength m + 2 ≤ fastGrowing (seqONote m 0) 2) :=
  ⟨fun _ ho => goodsteinLength_dominates_fastGrowing ho, goodsteinLength_le_fastGrowing_ordinal⟩

/-- Anti-vacuity: `f_{ε₀}` is the genuine extension to `ε₀` (mathlib's known value), and the tower the
headline ranges over is the genuine one. -/
example : ONote.fastGrowingε₀ 2 = 2048 := ONote.fastGrowingε₀_two
example : (towerO 1).repr = (ω : Ordinal) := by show (oadd 1 1 0 : ONote).repr = _; simp [ONote.repr]

end LeanFormalizations.Logic.Goodstein
