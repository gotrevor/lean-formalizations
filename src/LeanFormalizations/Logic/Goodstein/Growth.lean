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

/-- **The Cichoń step (THE C3 CRUX).** One budget-incrementing Hardy step on the base-`b`
notation of `p ≠ 0`, at argument `b`, equals the notation (in base `b+1`) of the
Goodstein operation `bump b p − 1`:

  `hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`.

This is the heart of Cichoń's theorem (1983) identifying the Goodstein descent with the
Hardy descent. Strong induction on `p`, writing `p = c·b^L + r` (leading Cantor term):

* **`r ≠ 0` (FULLY PROVED).** The leading term is preserved and the step happens in the tail:
  `hstep (oadd E C R) b = oadd E C (hstep R b)` (`hstep_oadd_tail`), then the IH on `r < p`
  and the reconstruction `toONote_oadd` + bump-invariance `toONote_bump` close it.
* **`r = 0` (the remaining base case, disclosed `sorry`).** Here `p = c·b^L` and the step must
  compute the *predecessor* of `c·(b+1)^(bump b L)` — the borrowing case. Verified to hold
  *syntactically* by `native_decide` on small cases (see anchors). This is the lone open core.

Everything downstream of `hstep_toONote` is fully proved; only the `r = 0` predecessor remains. -/
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
    · -- r = 0: the predecessor of `c·b^L`  (the borrowing base case)
      sorry
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
