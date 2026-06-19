/-
# C2 — the semantic bridge `Engine.toOrdinal` ↔ `ONote.repr`

The Goodstein termination proof (`Logic/Goodstein/Engine.lean`) maps each Goodstein term to
an ordinal `< ε₀` via `toOrdinal b n` — read `n` in hereditary base `b`, replace `b` by `ω`.
That ordinal is exactly the `ONote.repr` of the Cantor-normal-form notation of `n` in base
`b`. This file builds that notation, `toONote b n`, and proves the bridge

  `repr (toONote b n) = toOrdinal b n`  (`repr_toONote`)   and   `(toONote b n).NF`.

With the bridge, the engine's ε₀-descent (`Engine.seqOrd_step`) is expressed on the
*computable* ordinal notations `ONote`, the home of the fast-growing growth theory
(`Logic/FastGrowing/*`). This is the prerequisite (C2) for the growth theorem C3
(`goodsteinLength` tracks `fastGrowingε₀`).
-/
import Mathlib.SetTheory.Ordinal.Notation
import LeanFormalizations.Logic.Goodstein.Engine
import LeanFormalizations.Logic.Goodstein.Length

namespace LeanFormalizations.Logic.Goodstein

open ONote Ordinal

/-- The ordinal **notation** whose `repr` is `Engine.toOrdinal b n`: the Cantor normal form
of `n` written in base `b` with the base read as `ω`. Mirrors `toOrdinal`'s recursion
(peel the top power `b^(log b n)`), keeping everything computable. -/
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

@[simp] theorem toONote_zero (b : ℕ) : toONote b 0 = 0 := by rw [toONote]; simp

/-- **The bridge (repr side).** `repr (toONote b n) = toOrdinal b n`: the notation really does
represent the engine's ordinal. Structural induction mirroring `toOrdinal_pos`. -/
theorem repr_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ n, (toONote b n).repr = toOrdinal b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      rw [toONote, dif_neg hn, toOrdinal_pos b n hn, ONote.repr, ih _ hlog, ih _ hr_lt_n]
      congr 2
      exact_mod_cast PNat.toPNat'_coe hc_pos

/-- **The bridge (normal-form side).** `toONote b n` is a genuine normal-form notation. The
only nontrivial obligation is the leading-exponent ordering of each `oadd`, i.e. the tail's
ordinal sits below `ω^(leading exponent)` — exactly the remainder bound inside
`Engine.toOrdinal_mono_and_bound` (`toOrdinal b r < ω^(toOrdinal b e')` when `r < b^e'`),
reconstructed here from the public monotonicity + bound. -/
theorem toONote_NF (b : ℕ) (hb : 2 ≤ b) : ∀ n, (toONote b n).NF := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [toONote_zero]; exact NF.zero
    · have hb1 : 1 < b := by omega
      have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have hbound : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) := by
        rcases eq_or_ne (n % b ^ Nat.log b n) 0 with hr0 | hr0
        · rw [hr0, toOrdinal_zero]; exact opow_pos _ omega0_pos
        · have hlogr : Nat.log b (n % b ^ Nat.log b n) < Nat.log b n :=
            (Nat.log_lt_iff_lt_pow hb1 hr0).2 hr_lt
          have hmono : toOrdinal b (Nat.log b (n % b ^ Nat.log b n)) < toOrdinal b (Nat.log b n) :=
            (toOrdinal_mono_and_bound b hb (Nat.log b n)).1 _ hlogr
          refine ((toOrdinal_mono_and_bound b hb (n % b ^ Nat.log b n)).2 hr0).trans_le
            (opow_le_opow_right omega0_pos ?_)
          rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hmono
      rw [toONote, dif_neg hn]
      refine NF.oadd (ih _ hlog) _ (NF.below_of_lt' ?_ (ih _ hr_lt_n))
      rw [repr_toONote b hb, repr_toONote b hb]; exact hbound

/-! ### The Goodstein descent, expressed on `ONote`

With the bridge in hand, the engine's ordinal value `Engine.seqOrd m k` becomes a computable
notation `seqONote m k`, and the strict ε₀-descent `Engine.seqOrd_step` becomes a strict
`ONote` `<`-descent. This is the C2 deliverable: the Goodstein termination descent now lives
on the same `ONote` where the fast-growing growth theory (`Logic/FastGrowing/*`, A4) does —
the bridge that C3 (the growth theorem) will cross. -/

/-- The `k`-th Goodstein term as an ordinal **notation** (read in its base `k+2`). -/
def seqONote (m k : ℕ) : ONote := toONote (k + 2) (goodsteinSeq m k)

theorem seqONote_NF (m k : ℕ) : (seqONote m k).NF := toONote_NF (k + 2) (by omega) _

/-- `repr (seqONote m k) = Engine.seqOrd m k`: the notation carries the engine's ordinal. -/
theorem repr_seqONote (m k : ℕ) : (seqONote m k).repr = seqOrd m k :=
  repr_toONote (k + 2) (by omega) _

/-- **The Goodstein descent on `ONote`.** While the term is nonzero, one Goodstein step
strictly lowers the notation: `seqONote m (k+1) < seqONote m k`. Transported from
`Engine.seqOrd_step` through the `repr` bridge. -/
theorem seqONote_lt (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    seqONote m (k + 1) < seqONote m k := by
  rw [lt_def, repr_seqONote, repr_seqONote]
  exact seqOrd_step m k h

/-- `toONote b n = 0 ↔ n = 0`: the notation vanishes exactly when its argument does (a
nonzero argument produces an `oadd`, which is positive). -/
theorem toONote_eq_zero_iff (b n : ℕ) : toONote b n = 0 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, toONote_zero]⟩
  by_contra hn
  rw [toONote, dif_neg hn] at h
  exact absurd h (oadd_pos _ _ _).ne'

/-- `seqONote m k = 0 ↔ goodsteinSeq m k = 0`: the notation hits `0` exactly at termination.
Hence the ONote descent `seqONote m 0 > seqONote m 1 > …` has length `goodsteinLength m` —
the connection `goodsteinLength` ↔ ε₀-descent that C3 will turn into a Hardy growth bound. -/
theorem seqONote_eq_zero_iff (m k : ℕ) : seqONote m k = 0 ↔ goodsteinSeq m k = 0 :=
  toONote_eq_zero_iff (k + 2) (goodsteinSeq m k)

/-- The ONote descent reaches `0` exactly at index `goodsteinLength m`. -/
theorem seqONote_goodsteinLength (m : ℕ) : seqONote m (goodsteinLength m) = 0 :=
  (seqONote_eq_zero_iff m (goodsteinLength m)).2 (goodsteinSeq_goodsteinLength m)

/-- Before `goodsteinLength m` the descent is strictly positive. So `goodsteinLength m` is
*precisely* the length of the strict `ONote` descent `seqONote m 0 > … > 0` — the quantity
C3 must identify with a Hardy value of `seqONote m 0`. -/
theorem seqONote_ne_zero_of_lt (m : ℕ) {k : ℕ} (h : k < goodsteinLength m) :
    seqONote m k ≠ 0 :=
  fun hz => goodsteinSeq_ne_zero_of_lt h ((seqONote_eq_zero_iff m k).1 hz)

/-! ### Anti-vacuity anchors (`native_decide`)

The notations are computable; small values pin them (a wrong recursion would fail). -/

example : toONote 2 1 = oadd 0 1 0 := by native_decide          -- `1 = ω^0`
example : toONote 2 2 = oadd (oadd 0 1 0) 1 0 := by native_decide -- `2 = 2^1 ↦ ω^1 = ω`
example : toONote 2 4 = oadd (oadd (oadd 0 1 0) 1 0) 1 0 := by native_decide -- `4 = 2^2 ↦ ω^ω`
example : toONote 3 5 = oadd (oadd 0 1 0) 1 (oadd 0 2 0) := by native_decide  -- `5 = 1·3^1 + 2`
-- the descent: `goodsteinSeq 3` starts `3 ↦ 3 ↦ 3 ↦ 2 ↦ …`, notations strictly drop
example : seqONote 3 0 = oadd (oadd 0 1 0) 1 (oadd 0 1 0) := by native_decide -- `G₀=3` in base 2 ↦ `ω+1`

end LeanFormalizations.Logic.Goodstein
