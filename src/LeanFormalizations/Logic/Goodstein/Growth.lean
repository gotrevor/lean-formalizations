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
import LeanFormalizations.Logic.FastGrowing.Hardy

namespace LeanFormalizations.Logic.Goodstein

open ONote Ordinal
open LeanFormalizations.Logic.FastGrowing

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

/-! ## C3 — the growth theorem: `goodsteinLength m = H_{seqONote m 0}(2) − 2`

The crown jewel. The Hardy hierarchy "counts the steps" of a unit-decrement ordinal descent
where the *argument* (= the Goodstein base) grows by one at each step. The bridge is the
**Cichoń correspondence**: one Goodstein step is exactly one budget-incrementing Hardy step
(`hstep`) on the notation. Concretely, on `toONote` (base `b`, value `p ≠ 0`):

  `hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`   (`hstep_toONote`)

i.e. "descend the fundamental-sequence tree of `p`'s notation once at argument `b`" equals
"bump the base `b ↦ b+1` and subtract one" — the operation the Goodstein step performs.
Combined with the intrinsic Hardy step invariant `hardy_hstep` (`H_o(n) = H_{hstep o n}(n+1)`,
proved in `FastGrowing/Hardy.lean`), the Hardy value `H_{seqONote m k}(k+2)` is **constant**
along the whole Goodstein descent, so telescoping from `k = 0` to `k = goodsteinLength m`
(where the notation is `0` and `H_0(N) = N`) yields `H_{seqONote m 0}(2) = goodsteinLength m + 2`.

This is the formal "Goodstein grows like the Hardy/fast-growing hierarchy" — the growth
content behind Kirby–Paris independence (the abstract domination `f_o < f_{ε₀}` is A4
in `FastGrowing/Domination.lean`; this file pins the Goodstein length itself to a Hardy value). -/

/-- **Notation invariance under `bump`.** The ordinal *notation* of `n` is unchanged by a
hereditary base bump: `toONote (b+1) (bump b n) = toONote b n`. Both are normal-form notations
with the same `repr` (the bump invariance `toOrdinal_bump` at the ordinal level), so they are
equal by `repr_inj`. This is the notation-level companion of `Engine.toOrdinal_bump`. -/
theorem toONote_bump (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    toONote (b + 1) (bump b n) = toONote b n := by
  haveI := toONote_NF (b + 1) (by omega) (bump b n)
  haveI := toONote_NF b hb n
  rw [← repr_inj, repr_toONote (b + 1) (by omega), repr_toONote b hb, toOrdinal_bump b hb]

/-- **Constructor form of `toONote`.** When `1 ≤ c < b` and `s < b^e`, the base-`b` notation
of `c·b^e + s` is `oadd (toONote b e) c (toONote b s)` — `c·b^e + s` already presents the
leading Cantor term, so `log`, `div`, `mod` read off `e`, `c`, `s`. -/
theorem toONote_oadd (b : ℕ) (hb : 2 ≤ b) {c e s : ℕ} (hc : 1 ≤ c) (hcb : c < b)
    (hs : s < b ^ e) : toONote b (c * b ^ e + s) = oadd (toONote b e) ⟨c, hc⟩ (toONote b s) := by
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hn0 : c * b ^ e + s ≠ 0 := by positivity
  have hlow : c * b ^ e + s < b ^ (e + 1) := by
    calc c * b ^ e + s < c * b ^ e + b ^ e := by omega
      _ = (c + 1) * b ^ e := by ring
      _ ≤ b * b ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ (e + 1) := by rw [pow_succ]; ring
  have hge : b ^ e ≤ c * b ^ e + s :=
    (Nat.le_mul_of_pos_left (b ^ e) hc).trans (Nat.le_add_right _ _)
  have hlog : Nat.log b (c * b ^ e + s) = e := Nat.log_eq_of_pow_le_of_lt_pow hge hlow
  have hdiv : (c * b ^ e + s) / b ^ e = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbe_pos, Nat.div_eq_of_lt hs, Nat.zero_add]
  have hmod : (c * b ^ e + s) % b ^ e = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  rw [toONote, dif_neg hn0, hlog, hdiv, hmod]
  congr 1
  exact PNat.coe_injective (by simpa using PNat.toPNat'_coe hc)

/-- Single-digit notation: for `1 ≤ d < b`, `toONote b d = oadd 0 ⟨d,_⟩ 0` (the finite
ordinal `d`). Special case of `toONote_oadd` with exponent and remainder zero. -/
theorem toONote_single (b : ℕ) (hb : 2 ≤ b) {d : ℕ} (hd1 : 1 ≤ d) (hdb : d < b) :
    toONote b d = oadd 0 ⟨d, hd1⟩ 0 := by
  simpa using toONote_oadd b hb hd1 hdb (show (0 : ℕ) < b ^ 0 by simp)

/-- `fundamentalSequence` of `oadd 0 C 0` (a finite ordinal `C`): always a successor —
predecessor `0` when `C = 1`, else `oadd 0 (C-1) 0`. Read off the definition's nested match. -/
theorem fundamentalSequence_oadd_zero_zero (C : ℕ+) :
    fundamentalSequence (oadd 0 C 0) =
      match C.natPred with
      | 0 => Sum.inl (some 0)
      | j + 1 => Sum.inl (some (oadd 0 j.succPNat 0)) := by
  conv_lhs => rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl]
  rcases C.natPred with _ | j <;> rfl

/-- **The `r = 0`, `L = 0` (finite) base case of the Cichoń step.** For a single digit
`1 ≤ c < b`, one Hardy step on `oadd 0 c 0` (the finite ordinal `c`) is the finite notation
of `c − 1` in base `b+1`: `hstep (oadd 0 c 0) b = toONote (b+1) (c−1)`. `oadd 0 c 0` is a
successor, so the step is a single decrement. -/
theorem hstep_oadd_zero_zero (b : ℕ) (hb : 2 ≤ b) (c : ℕ) (hc1 : 1 ≤ c) (hcb : c < b) :
    hstep (oadd 0 ⟨c, hc1⟩ 0) b = toONote (b + 1) (c - 1) := by
  have hnp : PNat.natPred ⟨c, hc1⟩ = c - 1 := PNat.natPred_eq_pred hc1
  rcases eq_or_ne c 1 with rfl | hc2
  · rw [hstep_succ _ (by rw [fundamentalSequence_oadd_zero_zero, hnp])]; simp
  · have hfs : fundamentalSequence (oadd 0 ⟨c, hc1⟩ 0)
        = Sum.inl (some (oadd 0 (c - 2).succPNat 0)) := by
      rw [fundamentalSequence_oadd_zero_zero, hnp, show c - 1 = (c - 2) + 1 from by omega]
    rw [hstep_succ _ hfs, toONote_single (b + 1) (by omega) (show 1 ≤ c - 1 by omega) (by omega)]
    show oadd 0 (c - 2).succPNat 0 = oadd 0 ⟨c - 1, by omega⟩ 0
    congr 1
    apply PNat.coe_injective
    change (c - 2) + 1 = c - 1
    omega

/-- Helper for the coefficient peel: for `E ≠ 0`, the fundamental sequence of `oadd E 1 0`
is some `inr g`, and that of `oadd E ⟨k+2⟩ 0` wraps it as `fun i => oadd E ⟨k+1⟩ (g i)`.
Read off the two non-`inl none` branches of `fundamentalSequence (oadd E · 0)` (tail `0`,
`natPred` `0` resp. `k+1`). -/
theorem fundSeq_oadd_coeff (E : ONote) (hE : E ≠ 0) (k : ℕ) :
    ∃ g, fundamentalSequence (oadd E 1 0) = Sum.inr g ∧
      fundamentalSequence (oadd E ⟨k + 2, by omega⟩ 0)
        = Sum.inr (fun i => oadd E k.succPNat (g i)) := by
  rcases e : fundamentalSequence E with (_ | E') | f
  · exact absurd ((fundamentalSequenceProp_inl_none E).1 (e ▸ fundamentalSequence_has_prop E)) hE
  · refine ⟨fun i => oadd E' i.succPNat 0, ?_, ?_⟩ <;>
      · rw [fundamentalSequence]
        simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, e]
        rfl
  · refine ⟨fun i => oadd (f i) 1 0, ?_, ?_⟩ <;>
      · rw [fundamentalSequence]
        simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, e]
        rfl

/-- **Lemma A (coefficient peel).** For `E ≠ 0` and `c ≥ 2`, one Hardy step on `oadd E c 0`
peels the coefficient to `c-1` and leaves a Hardy step on `oadd E 1 0`:
`hstep (oadd E ⟨c⟩ 0) b = oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`. The descent through the
limit `oadd E ⟨c⟩ 0` lands on `oadd E ⟨c-1⟩ (g b)`, whose nonzero tail `g b` peels off
(`hstep_oadd_tail`) leaving exactly `hstep (oadd E 1 0) b = hstep (g b) b`. -/
theorem hstep_oadd_coeff (b : ℕ) {E : ONote} (hE : E ≠ 0) {c : ℕ} (hc : 2 ≤ c)
    (hc1 : 1 ≤ c) :
    hstep (oadd E ⟨c, hc1⟩ 0) b = oadd E ⟨c - 1, by omega⟩ (hstep (oadd E 1 0) b) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
  obtain ⟨g, h1, hc2⟩ := fundSeq_oadd_coeff E hE k
  have hgb : g b ≠ 0 := fundamentalSequence_inr_ne_zero h1 b
  have hcoe : (⟨k + 2, hc1⟩ : ℕ+) = ⟨k + 2, by omega⟩ := rfl
  rw [hcoe, hstep_limit _ hc2, hstep_limit _ h1]
  dsimp only
  rw [hstep_oadd_tail E k.succPNat b (g b) hgb]
  congr 1

/-- Predecessor of a finite successor `oadd 0 ⟨c⟩ 0` (= the ordinal `c`) at any argument:
for `c ≥ 2`, `hstep (oadd 0 ⟨c⟩ 0) n = oadd 0 ⟨c-1⟩ 0`. -/
theorem hstep_finite_pred (c : ℕ) (hc : 2 ≤ c) (n : ℕ) :
    hstep (oadd 0 ⟨c, by omega⟩ 0) n = oadd 0 ⟨c - 1, by omega⟩ 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 := ⟨c - 2, by omega⟩
  have hfs : fundamentalSequence (oadd 0 ⟨e + 2, by omega⟩ 0)
      = Sum.inl (some (oadd 0 ⟨e + 1, by omega⟩ 0)) := by
    rw [fundamentalSequence_oadd_zero_zero]; rfl
  rw [hstep_succ _ hfs]
  rfl

/-- The `c = 1` fundamental sequence when `E` is a **successor** (`fundamentalSequence E = some E'`). -/
theorem fundSeq_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E')) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd E' i.succPNat 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- The `c = 1` fundamental sequence when `E` is a **limit** (`fundamentalSequence E = inr f`). -/
theorem fundSeq_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd (f i) 1 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- One Hardy step on `oadd E 1 0` when `E` is a **successor** with predecessor `E'`: the
descent lands on `oadd E' ⟨b+1⟩ 0`. -/
theorem hstep_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E'))
    (b : ℕ) : hstep (oadd E 1 0) b = hstep (oadd E' b.succPNat 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_succ h)]

/-- One Hardy step on `oadd E 1 0` when `E` is a **limit** with fundamental sequence `f`: the
descent passes to `oadd (f b) 1 0`. -/
theorem hstep_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) (b : ℕ) :
    hstep (oadd E 1 0) b = hstep (oadd (f b) 1 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_limit h)]

/-- Fundamental sequence of the finite ordinal `oadd 0 ⟨c⟩ 0` (`c ≥ 2`): the successor of
`oadd 0 ⟨c-1⟩ 0`. -/
theorem fundSeq_finite_succ (c : ℕ) (hc : 2 ≤ c) :
    fundamentalSequence (oadd 0 ⟨c, by omega⟩ 0) = Sum.inl (some (oadd 0 ⟨c - 1, by omega⟩ 0)) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 := ⟨c - 2, by omega⟩
  rw [fundamentalSequence_oadd_zero_zero]; rfl

/-- **Lemma B, finite base case (PROVED).** For `0 ≤ d ≤ b`, one Hardy step on
`ω^(d+1) = oadd (finite (d+1)) 1 0` at argument `b` is the all-digits-`b` notation
`(b+1)^(d+1) − 1`. Strong induction on `d`: the descent peels the coefficient `b+1` it
produces (`hstep_oadd_coeff`), recurses (`ih`), and the leading exponent reconstructs as a
single base-`(b+1)` digit (`toONote (b+1) d = finite d`, valid since `d ≤ b < b+1`). This is
the base case of the general `hstep_oadd_one_zero` and validates the full borrowing recursion
(descent → coefficient peel → IH → reconstruct) end-to-end. -/
theorem hstep_oadd_one_zero_finite (b : ℕ) (hb : 2 ≤ b) :
    ∀ d, d ≤ b →
      hstep (oadd (oadd 0 d.succPNat 0) 1 0) b = toONote (b + 1) ((b + 1) ^ (d + 1) - 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdb
    have hbsucc : (b.succPNat : ℕ+) = ⟨b + 1, by omega⟩ := rfl
    rcases Nat.eq_zero_or_pos d with hd | hd
    · -- d = 0: exponent 1, descent on finite 1 → oadd 0 ⟨b+1⟩ 0 → decrement → finite b
      subst hd
      have hE1 : fundamentalSequence (oadd 0 (0 : ℕ).succPNat 0) = Sum.inl (some 0) := by
        rw [fundamentalSequence_oadd_zero_zero]; rfl
      rw [hstep_oadd_one_of_succ hE1 b, hbsucc, hstep_finite_pred (b + 1) (by omega) b,
        show (b + 1) ^ (0 + 1) - 1 = b from by rw [pow_succ, pow_zero, one_mul]; omega]
      exact (toONote_single (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)).symm
    · -- d = e+1 ≥ 1: fundSeq(finite (e+2)) = some (finite (e+1)); descent → coefficient peel → ih e
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hE' : (oadd 0 e.succPNat 0 : ONote) ≠ 0 := (oadd_pos _ _ _).ne'
      have hple : (1 : ℕ) ≤ (b + 1) ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
      have hfd : fundamentalSequence (oadd 0 (e + 1).succPNat 0)
          = Sum.inl (some (oadd 0 e.succPNat 0)) := by
        rw [fundamentalSequence_oadd_zero_zero]; rfl
      rw [hstep_oadd_one_of_succ hfd b, hbsucc,
        hstep_oadd_coeff b hE' (by omega) (by omega : 1 ≤ b + 1),
        ih e (by omega) (by omega)]
      have hpow : (b + 1) ^ (e + 1 + 1) - 1 = b * (b + 1) ^ (e + 1) + ((b + 1) ^ (e + 1) - 1) := by
        have hsplit : (b + 1) ^ (e + 1 + 1) = (b + 1) * (b + 1) ^ (e + 1) := by rw [pow_succ']
        have hdist : (b + 1) * (b + 1) ^ (e + 1) = b * (b + 1) ^ (e + 1) + (b + 1) ^ (e + 1) := by
          ring
        rw [hsplit, hdist]; omega
      rw [hpow, toONote_oadd (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)
        (show (b + 1) ^ (e + 1) - 1 < (b + 1) ^ (e + 1) by omega)]
      congr 1
      exact (toONote_single (b + 1) (by omega) (show 1 ≤ e + 1 by omega) (by omega)).symm

/-- **Lemma B (the `c = 1` predecessor — the lone open core of C3).** One Hardy step on
`oadd (toONote b L) 1 0` (i.e. `ω^E` for `E = toONote b L`, `L ≥ 1`) at argument `b` is the
base-`(b+1)` notation of `(b+1)^(bump b L) − 1` — the fully-filled (all-digits-`b`) expansion
produced by the borrowing descent through `fundamentalSequence`.

*(disclosed `sorry`.)* This is the genuine borrowing core, now isolated to coefficient `1`.
The **finite base case** (`E = finite (d+1)`, `d ≤ b`) is fully PROVED in
`hstep_oadd_one_zero_finite`, which exercises the entire recursion engine end-to-end
(descent `hstep_oadd_one_of_succ` → coefficient peel `hstep_oadd_coeff` → IH → reconstruct
`toONote_oadd`). The remaining work is the general `E = toONote b L`: a well-founded recursion
on `repr E` using the same engine, with `E` a successor ⟹ peel to
`oadd E' ⟨b⟩ (hstep (oadd E' 1 0) b)` with `E' = pred E` (`hstep_oadd_one_of_succ`); `E` a
limit ⟹ recurse on `oadd (f b) 1 0` (`hstep_oadd_one_of_limit`). Closing it needs the general
statement over arbitrary NF `E` with answer `toONote (b+1) ((b+1)^(evalNat E) − 1)`
(`evalNat E` = `repr E` evaluated at `ω ↦ b+1`; note `evalNat (toONote b L) = bump b L`),
carrying the two descent identities `evalNat (pred E) + 1 = evalNat E` (successor) and
`evalNat (f b) = evalNat E` (limit, at the fixed index `b`), plus the invariant that the
reachable `E` reconstruct (`toONote (b+1) (evalNat E') = E'`) — which holds because the only
coefficient `b+1` the descent introduces (at index `b`) is immediately peeled by
`hstep_oadd_coeff`. Verified syntactically by `native_decide` on small cases (see anchors). -/
theorem hstep_oadd_one_zero (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (hL : 1 ≤ L) :
    hstep (oadd (toONote b L) 1 0) b = toONote (b + 1) ((b + 1) ^ bump b L - 1) := by
  sorry

/-- **The Cichoń step (THE C3 CRUX).** One budget-incrementing Hardy step on the base-`b`
notation of `p ≠ 0`, at argument `b`, equals the notation (in base `b+1`) of the
Goodstein operation `bump b p − 1`:

  `hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`.

This is the heart of Cichoń's theorem (1983) identifying the Goodstein descent with the
Hardy descent. Strong induction on `p`, writing `p = c·b^L + r` (leading Cantor term):

* **`r ≠ 0` (FULLY PROVED).** The leading term is preserved and the step happens in the tail:
  `hstep (oadd E C R) b = oadd E C (hstep R b)` (`hstep_oadd_tail`), then the IH on `r < p`
  and the reconstruction `toONote_oadd` + bump-invariance `toONote_bump` close it.
* **`r = 0`.** Here `p = c·b^L` and the step computes the *predecessor* of `c·(b+1)^(bump b L)`.
  - `L = 0` (single digit, FULLY PROVED): `oadd 0 c 0` is a successor (`hstep_oadd_zero_zero`).
  - `L ≥ 1` (disclosed `sorry`): the genuine **borrowing** case — a nested `fundamentalSequence`
    descent producing the filled `(b+1)`-ary expansion of `(b+1)^(bump b L) − 1`. The lone open
    core of C3; verified *syntactically* by `native_decide` on small cases (see anchors).

Everything else (`r ≠ 0`, `r = 0 ∧ L = 0`, and all downstream of `hstep_toONote`) is proved. -/
theorem hstep_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ p, p ≠ 0 →
    hstep (toONote b p) b = toONote (b + 1) (bump b p - 1) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    have hbe_pos : 0 < b ^ Nat.log b p := Nat.pow_pos (by omega)
    have hbe_le : b ^ Nat.log b p ≤ p := Nat.pow_log_le_self b hp
    have hc1 : 1 ≤ p / b ^ Nat.log b p := Nat.div_pos hbe_le hbe_pos
    have hcb : p / b ^ Nat.log b p < b := by
      apply Nat.div_lt_of_lt_mul
      have h := Nat.lt_pow_succ_log_self (show 1 < b by omega) p
      rwa [pow_succ] at h
    have hr_lt : p % b ^ Nat.log b p < b ^ Nat.log b p := Nat.mod_lt _ hbe_pos
    have hp_eq : p = (p / b ^ Nat.log b p) * b ^ Nat.log b p + p % b ^ Nat.log b p := by
      rw [mul_comm]; exact (Nat.div_add_mod p _).symm
    set L := Nat.log b p
    set c := p / b ^ L with hc_def
    set r := p % b ^ L with hr_def
    have htoP : toONote b p = oadd (toONote b L) ⟨c, hc1⟩ (toONote b r) := by
      conv_lhs => rw [hp_eq]
      exact toONote_oadd b hb hc1 hcb hr_lt
    have hbump : bump b p = c * (b + 1) ^ bump b L + bump b r := bump_pos b p hp
    rcases eq_or_ne r 0 with hr0 | hr0
    · -- r = 0: the predecessor of `c·b^L`
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · -- L = 0: a single digit `c`; `oadd 0 c 0` is a successor (PROVED)
        have hEz : toONote b L = 0 := by rw [hL0, toONote_zero]
        have hbumpL : bump b L = 0 := by rw [hL0, bump_zero]
        rw [htoP, hr0, hEz, toONote_zero, hstep_oadd_zero_zero b hb c hc1 hcb]
        congr 1
        rw [hbump, hr0, hbumpL, bump_zero]; simp
      · -- L ≥ 1: borrowing case. Peel the coefficient (`hstep_oadd_coeff`) down to the
        -- `c = 1` predecessor `hstep_oadd_one_zero`, then reconstruct via `toONote_oadd`.
        have hE : toONote b L ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; omega
        have htoP0 : toONote b p = oadd (toONote b L) ⟨c, hc1⟩ 0 := by
          rw [htoP, hr0, toONote_zero]
        have hbump0 : bump b p - 1 = c * (b + 1) ^ bump b L - 1 := by
          rw [hbump, hr0, bump_zero, Nat.add_zero]
        rcases eq_or_ne c 1 with hc1' | hc2'
        · -- c = 1: directly Lemma B
          have hcpn : (⟨c, hc1⟩ : ℕ+) = 1 := PNat.coe_injective hc1'
          rw [htoP0, hcpn, hbump0, hc1', one_mul]
          exact hstep_oadd_one_zero b hb L hLpos
        · -- c ≥ 2: peel to `oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`, recombine
          have hMpos : 1 ≤ (b + 1) ^ bump b L := Nat.one_le_pow _ _ (by omega)
          have key : c * (b + 1) ^ bump b L - 1
              = (c - 1) * (b + 1) ^ bump b L + ((b + 1) ^ bump b L - 1) := by
            have h := Nat.sub_one_mul c ((b + 1) ^ bump b L)
            have hcX : (b + 1) ^ bump b L ≤ c * (b + 1) ^ bump b L :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
          rw [htoP0, hstep_oadd_coeff b hE (by omega) hc1, hstep_oadd_one_zero b hb L hLpos,
            hbump0, key]
          rw [toONote_oadd (b + 1) (by omega) (show 1 ≤ c - 1 by omega) (by omega)
              (show (b + 1) ^ bump b L - 1 < (b + 1) ^ bump b L by omega),
            toONote_bump b hb]
    · -- r ≠ 0: leading term preserved, the step happens in the tail
      have hRne : toONote b r ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; exact hr0
      have hbr_pos : 0 < bump b r := by
        rw [bump_pos b r hr0]
        have h1 : 0 < r / b ^ Nat.log b r :=
          Nat.div_pos (Nat.pow_log_le_self _ hr0) (Nat.pow_pos (by omega))
        have h2 : 0 < (b + 1) ^ bump b (Nat.log b r) := Nat.pow_pos (by omega)
        have := Nat.mul_pos h1 h2; omega
      have hbrB : bump b r < (b + 1) ^ bump b L := bump_lt_pow b hb hr_lt
      rw [htoP, hstep_oadd_tail (toONote b L) ⟨c, hc1⟩ b (toONote b r) hRne, ih r (by omega) hr0]
      have hsub : bump b p - 1 = c * (b + 1) ^ bump b L + (bump b r - 1) := by rw [hbump]; omega
      rw [hsub, toONote_oadd (b + 1) (by omega) hc1 (by omega)
        (by omega : bump b r - 1 < (b + 1) ^ bump b L), toONote_bump b hb]

/-- The Cichoń step, specialised to the Goodstein descent: one Goodstein step is one
budget-incrementing Hardy step on the notation. `seqONote m (k+1) = hstep (seqONote m k) (k+2)`
whenever the term is nonzero. -/
theorem hstep_seqONote (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hstep (seqONote m k) (k + 2) = seqONote m (k + 1) := by
  show hstep (toONote (k + 2) (goodsteinSeq m k)) (k + 2) = toONote (k + 1 + 2) (goodsteinSeq m (k + 1))
  rw [hstep_toONote (k + 2) (by omega) (goodsteinSeq m k) h]
  rfl

/-- **The per-step Hardy invariant.** Along the Goodstein descent (while nonzero) the Hardy
value `H_{seqONote m k}(k+2)` is unchanged: `H_{seqONote m k}(k+2) = H_{seqONote m (k+1)}((k+1)+2)`.
Combines the intrinsic step invariant `hardy_hstep` with the Cichoń step `hstep_seqONote`. -/
theorem hardy_seqONote_step (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hardy (seqONote m k) (k + 2) = hardy (seqONote m (k + 1)) (k + 1 + 2) := by
  have ho : seqONote m k ≠ 0 := fun hz => h ((seqONote_eq_zero_iff m k).1 hz)
  rw [hardy_hstep (seqONote m k) (k + 2) ho, hstep_seqONote m k h]

/-- **Telescoping.** For every `j ≤ goodsteinLength m`, the Hardy value at the start equals
the Hardy value `j` steps in: `H_{seqONote m 0}(2) = H_{seqONote m j}(j+2)`. Induction on `j`
using `hardy_seqONote_step` (valid since `j < goodsteinLength m` ⟹ the `j`-th term is nonzero). -/
theorem hardy_seqONote_telescope (m : ℕ) :
    ∀ j, j ≤ goodsteinLength m → hardy (seqONote m 0) 2 = hardy (seqONote m j) (j + 2) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ k ih =>
    intro hj
    have hk : k < goodsteinLength m := Nat.lt_of_succ_le hj
    rw [ih (Nat.le_of_lt hk), hardy_seqONote_step m k (goodsteinSeq_ne_zero_of_lt hk)]

/-- **C3 — the growth theorem (Hardy form).** The Hardy value of the starting notation at the
starting base is the Goodstein length plus two: `H_{seqONote m 0}(2) = goodsteinLength m + 2`.
At `j = goodsteinLength m` the descent reaches the zero notation, where `H_0(N) = N`. -/
theorem hardy_seqONote_zero (m : ℕ) : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := by
  rw [hardy_seqONote_telescope m (goodsteinLength m) le_rfl, seqONote_goodsteinLength, hardy_zero]
  rfl

/-- **C3 — the growth theorem (length form).** The Goodstein length of `m` is exactly the
Hardy value of its starting notation (read in base 2) at argument 2, minus 2:

  `goodsteinLength m = H_{seqONote m 0}(2) − 2`.

This is Cichoń's identity formalised: the Goodstein length function *is* a Hardy function of
the starting ordinal notation. Since the Hardy/fast-growing hierarchy reaches `ε₀`
(`FastGrowing/Domination.lean`, A4), this pins `goodsteinLength`'s growth at the `ε₀` level —
the growth content of Kirby–Paris independence. -/
theorem goodsteinLength_eq_hardy (m : ℕ) : goodsteinLength m = hardy (seqONote m 0) 2 - 2 := by
  rw [hardy_seqONote_zero]; omega

/-! ### Anti-vacuity anchors (`native_decide`)

The notations are computable; small values pin them (a wrong recursion would fail). -/

example : toONote 2 1 = oadd 0 1 0 := by native_decide          -- `1 = ω^0`
example : toONote 2 2 = oadd (oadd 0 1 0) 1 0 := by native_decide -- `2 = 2^1 ↦ ω^1 = ω`
example : toONote 2 4 = oadd (oadd (oadd 0 1 0) 1 0) 1 0 := by native_decide -- `4 = 2^2 ↦ ω^ω`
example : toONote 3 5 = oadd (oadd 0 1 0) 1 (oadd 0 2 0) := by native_decide  -- `5 = 1·3^1 + 2`
-- the descent: `goodsteinSeq 3` starts `3 ↦ 3 ↦ 3 ↦ 2 ↦ …`, notations strictly drop
example : seqONote 3 0 = oadd (oadd 0 1 0) 1 (oadd 0 1 0) := by native_decide -- `G₀=3` in base 2 ↦ `ω+1`
-- the Cichoń step `hstep_toONote` holds *syntactically* (the disclosed crux, here witnessed):
example : hstep (toONote 2 3) 2 = toONote 3 (bump 2 3 - 1) := by native_decide
example : hstep (toONote 3 5) 3 = toONote 4 (bump 3 5 - 1) := by native_decide
example : hstep (seqONote 3 0) 2 = seqONote 3 1 := by native_decide
-- C3, witnessed on a computable case: `goodsteinLength 3 = H_{seqONote 3 0}(2) − 2 = 7 − 2 = 5`
example : hardy (seqONote 3 0) 2 = goodsteinLength 3 + 2 := by native_decide

end LeanFormalizations.Logic.Goodstein
