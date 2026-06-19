/-
# Toward `o = ω`: the limit-level diagonal, isolated to its crux

With the finite-level diagonal `f_n(m) ≤ goodsteinLength m + 2` closed
(`DominationBaseCases.lean`), the next tier of Cichoń's lower bound is the **limit ordinal `ω`**:
`f_ω(m) ≤ goodsteinLength m + 2`. This file builds the ordinal bridge for `ω^ω` and reduces the
`o = ω` diagonal to a single open hypothesis — exactly the way `Domination.lean`'s
`goodstein_dominates_of_index` framed the finite levels in lap 6.

The crux it isolates: the descent's **leading exponent stays in the LARGE regime** (`≥ base`) at step
`m − 2`. For finite `o = n` we only needed `leadExp ≥ n` (a fixed constant); for `o = ω` we need
`leadExp ≥ base = m`, i.e. the leading exponent itself reaches `ω` at the ordinal level. This is one
recursion deeper than the lap-9 self-similarity (see `PENDING_WORK.md` → "NEXT FRONTIER"), and is the
genuine remaining growth content — NOT to be axiomatized.
-/
import LeanFormalizations.Logic.Goodstein.Domination
import LeanFormalizations.Logic.Goodstein.DominationBaseCases

namespace LeanFormalizations.Logic.Goodstein

open ONote Ordinal
open LeanFormalizations.Logic.FastGrowing

/-- **Ordinal bridge for `ω^ω`.** If the leading exponent of `G_i` is in the *large regime*
(`base i ≤ log_{base i} G_i`), the descent ordinal dominates `ω^ω`: the leading CNF exponent
`toOrdinal (base i) (leadExp)` is then `≥ toOrdinal (base i) (base i) = ω`, so the leading term is
`≥ ω^ω`. The `ω`-level analog of `opow_le_seqONote_repr` (which handled finite exponents `ω^k`). -/
theorem omega_omega_le_seqONote_repr {m i : ℕ}
    (hreg : base i ≤ Nat.log (base i) (goodsteinSeq m i)) (hv : goodsteinSeq m i ≠ 0) :
    (ω : Ordinal) ^ (ω : Ordinal) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  rw [repr_seqONote]
  show (ω : Ordinal) ^ (ω : Ordinal) ≤ toOrdinal (base i) (goodsteinSeq m i)
  have h1 : toOrdinal (base i) 1 = 1 := by
    have h := toOrdinal_pow (base i) hb 0; simpa using h
  have hbb : toOrdinal (base i) (base i) = ω := by
    have h := toOrdinal_pow (base i) hb 1
    rw [pow_one, h1, opow_one] at h; exact h
  have hSM : StrictMono (toOrdinal (base i)) := fun a c hac =>
    (toOrdinal_mono_and_bound (base i) hb c).1 a hac
  have homega_le : (ω : Ordinal) ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) := by
    rw [← hbb]; exact hSM.monotone hreg
  calc (ω : Ordinal) ^ (ω : Ordinal)
      ≤ ω ^ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
        opow_le_opow_right omega0_pos homega_le
    _ ≤ toOrdinal (base i) (goodsteinSeq m i) := opow_toOrdinal_log_le (base i) hb hv

/-- **The `o = ω` diagonal domination, REDUCED to its crux** (`hreg`). If the Goodstein descent's
leading exponent is still in the LARGE regime at step `m − 2` (`base (m−2) ≤ leadExp_{m−2}`), then
`fastGrowing ω m ≤ goodsteinLength m + 2` (with `ω = oadd 1 1 0`). Assembly mirrors the finite-level
`fastGrowing_ofNat_le_goodsteinLength_of_log_length`: the large-regime hypothesis gives
`ω^ω ≤ (seqONote m (m−2)).repr` (`omega_omega_le_seqONote_repr`); the diagonal reduction
`goodstein_dominates_of_index_le` (budget `m`) closes it. **The hypothesis `hreg` IS Cichoń's lower
bound at the limit level `ω`** — the open obligation for the next lap (route (a) in `PENDING_WORK.md`:
iterate the self-similarity so the one-level-down value stays `≥ base` for `~m` steps). -/
theorem fastGrowing_omega_le_goodsteinLength_of_largeRegime {m : ℕ} (hm : 4 ≤ m)
    (hreg : base (m - 2) ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2))) :
    fastGrowing (oadd 1 1 0) m ≤ goodsteinLength m + 2 := by
  set j := m - 2 with hj
  have ho : (oadd 1 1 0 : ONote).NF := by decide
  have hv : goodsteinSeq m j ≠ 0 := by have := goodsteinSeq_ge_init m j (by omega); omega
  have hidx : (oadd (oadd 1 1 0) 1 0).repr ≤ (seqONote m j).repr := by
    have hr : (oadd (oadd 1 1 0) 1 0 : ONote).repr = ω ^ (ω : Ordinal) := by simp [ONote.repr]
    rw [hr]; exact omega_omega_le_seqONote_repr hreg hv
  have hnorm : norm (oadd 1 1 0 : ONote) ≤ j + 2 := by
    have : norm (oadd 1 1 0 : ONote) = 1 := by decide
    omega
  have hgl : j ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le (o := oadd 1 1 0) (m := m) (j := j) ho hgl (by omega) hnorm hidx

/-- **Doubly-iterated length bound — the `ω`-level analog of `goodsteinLength_exp_lower`.** For every
`m ≥ 2^16` the *one-level-down* Goodstein sequence (seed `L = Nat.log 2 m`) runs at least `2m − 2`
steps: `2 * m ≤ goodsteinLength (Nat.log 2 m) + 2`. The finite-level diagonal used the *exponential*
length bound `goodsteinLength M ≥ 2^{M+1}+M` at the smaller seed; that gives only `≈ m` and cannot
push the leading exponent past a fixed constant. The limit level needs more, so this lemma applies the
full unconditional **`o = 2` diagonal** `2^L·L = f_2(L) ≤ goodsteinLength L + 2`
(`fastGrowing_two_le_goodsteinLength`) at the seed `L ≥ 16`: since `m < 2^{L+1}` we have
`2·2^L ≥ m+1`, so `2^L·L ≥ 16·2^L = 8·(2·2^L) ≥ 8(m+1) ≥ 2m`. The surplus over the seed is exactly
what lifts the leading exponent into the LARGE regime (`≥ base`), discharging `hreg` below. -/
theorem two_mul_le_goodsteinLength_log {m : ℕ} (hm : 2 ^ 16 ≤ m) :
    2 * m ≤ goodsteinLength (Nat.log 2 m) + 2 := by
  have hL16 : 16 ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm
  have hf2 := fastGrowing_two_le_goodsteinLength (m := Nat.log 2 m) hL16
  simp only [ONote.fastGrowing_two] at hf2
  set L := Nat.log 2 m with hLdef
  set P := 2 ^ L with hPdef
  have hpow : m + 1 ≤ 2 ^ (L + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    rw [← hLdef] at h; omega
  have hpowsucc : (2 : ℕ) ^ (L + 1) = P * 2 := by rw [hPdef, pow_succ]
  rw [hpowsucc] at hpow
  have hmono : P * 16 ≤ P * L := Nat.mul_le_mul (le_refl P) hL16
  -- hf2 : P * L ≤ goodsteinLength L + 2 ;  hmono : P*16 ≤ P*L ;  hpow : m+1 ≤ P*2
  omega

/-- **THE `o = ω` DIAGONAL DOMINATION — UNCONDITIONAL (every `m ≥ 2^16`):**
`fastGrowing ω m ≤ goodsteinLength m + 2`, i.e. `f_ω(m) ≤ goodsteinLength m + 2`, with
`ω = oadd 1 1 0`. This is Cichoń's lower bound at the **first limit ordinal** — the leading CNF
exponent of the Goodstein descent provably reaches `ω` (the LARGE regime `≥ base`) and stays there
through step `m − 2`, so the descent ordinal dominates `ω^ω`.

The crux `hreg` (leading exponent `≥ base (m−2) = m` at step `m − 2`) is discharged by **iterating
the self-similarity once more**: `leadExp_ge_goodsteinSeq_log` bounds the leading exponent below by
the *one-level-down* Goodstein value `goodsteinSeq (log₂ m) (m−2)`, and `n_le_goodsteinSeq` keeps that
value `≥ m` provided the one-level-down sequence still has `≥ m` steps to run — supplied by the
doubly-iterated length bound `two_mul_le_goodsteinLength_log` (`goodsteinLength (log₂ m) ≥ 2m − 2`).
For finite `o = n` the analog only needed value `≥ n` (a constant); the jump to `o = ω` is precisely
the jump from "value `≥ n`" to "value `≥ base = m`", which the *factor-of-two* surplus in the length
bound provides. The whole reduction is then closed by `fastGrowing_omega_le_goodsteinLength_of_largeRegime`. -/
theorem fastGrowing_omega_le_goodsteinLength {m : ℕ} (hm : 2 ^ 16 ≤ m) :
    fastGrowing (oadd 1 1 0) m ≤ goodsteinLength m + 2 := by
  have h4 : 4 ≤ m := le_trans (by norm_num) hm
  apply fastGrowing_omega_le_goodsteinLength_of_largeRegime h4
  -- hreg : base (m - 2) ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2))
  have hbase : base (m - 2) = m := by simp only [base]; omega
  have hlen : (m - 2) + m ≤ goodsteinLength (Nat.log 2 m) := by
    have := two_mul_le_goodsteinLength_log hm; omega
  calc base (m - 2)
      = m := hbase
    _ ≤ goodsteinSeq (Nat.log 2 m) (m - 2) :=
        n_le_goodsteinSeq (Nat.log 2 m) (m - 2) m hbase.ge hlen
    _ ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2)) := leadExp_ge_goodsteinSeq_log m (m - 2)

/-- Anti-vacuity: `ω = oadd 1 1 0` really has `repr = ω`, and `oadd ω 1 0` has `repr = ω^ω` — so the
reduction targets the genuine limit level, not a finite stand-in. -/
example : (oadd 1 1 0 : ONote).repr = ω := by simp [ONote.repr]
example : (oadd (oadd 1 1 0) 1 0 : ONote).repr = ω ^ (ω : Ordinal) := by simp [ONote.repr]

end LeanFormalizations.Logic.Goodstein
