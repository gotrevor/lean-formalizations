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
import LeanFormalizations.Logic.Goodstein.GoodsteinLike
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

/-! ### Toward `o = ω^j`: the SECOND-level tower (next limit tier of Cichoń)

`o = ω` needed the leading exponent in the LARGE regime (`leadExp ≥ base`). The next tier `o = ω^j`
needs the *second-level* leading exponent `≥ j` — equivalently the leading exponent `≥ base^j` — at
step `m − 2`. We build the general ordinal bridge and reduce `o = ω^j` to a single length bound on the
*doubly-iterated* seed `(log₂)^[2] m`, via the self-similarity tower `iterLeadExp_dominates`. -/

/-- **`ω^k ≤ toOrdinal b w`** from the leading exponent `log_b w ≥ k` (with `k < b`, `w ≠ 0`). The
`toOrdinal`-level core of `opow_le_seqONote_repr`, factored out so it applies at the *second* level
(to the leading exponent itself) — the brick of the `ω^j` tower. -/
theorem opow_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) {w k : ℕ}
    (hk : k ≤ Nat.log b w) (hw : w ≠ 0) (hkb : k < b) :
    (ω : Ordinal) ^ (k : Ordinal) ≤ toOrdinal b w := by
  have htk : toOrdinal b k = (k : Ordinal) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · have hlog0 : Nat.log b k = 0 := Nat.log_eq_zero_iff.2 (Or.inl hkb)
      rw [toOrdinal_pos b k (by omega), hlog0]
      simp [pow_zero, Nat.div_one, Nat.mod_one, toOrdinal_zero]
  have hmono : toOrdinal b k ≤ toOrdinal b (Nat.log b w) := by
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt ((toOrdinal_mono_and_bound b hb _).1 k h)
  calc (ω : Ordinal) ^ (k : Ordinal) = ω ^ toOrdinal b k := by rw [htk]
    _ ≤ ω ^ toOrdinal b (Nat.log b w) := opow_le_opow_right omega0_pos hmono
    _ ≤ toOrdinal b w := opow_toOrdinal_log_le b hb hw

/-- **Level-2 ordinal bridge: `ω^{ω^j} ≤ descent`.** If the SECOND-level leading exponent is `≥ j`
(`j ≤ log_{base i}(log_{base i} G_i)`), with `j < base i` and the value/leading-exponent nonzero, the
Goodstein descent ordinal dominates `ω^{ω^j}`. Applies `opow_le_toOrdinal` to the leading exponent
(`ω^j ≤ toOrdinal (base i)(leadExp)`), then `opow_toOrdinal_log_le` once more. The `ω^j`-flavoured
analog of `omega_omega_le_seqONote_repr` (the `j` "= base", `ω^ω` case). -/
theorem omega_pow_pow_le_seqONote_repr {m i j : ℕ}
    (hj : j ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)))
    (hjb : j < base i) (hv : goodsteinSeq m i ≠ 0)
    (hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0) :
    (ω : Ordinal) ^ ((ω : Ordinal) ^ (j : Ordinal)) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  rw [repr_seqONote]
  show (ω : Ordinal) ^ ((ω : Ordinal) ^ (j : Ordinal)) ≤ toOrdinal (base i) (goodsteinSeq m i)
  have hA : (ω : Ordinal) ^ (j : Ordinal)
      ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
    opow_le_toOrdinal (base i) hb hj hlead hjb
  calc (ω : Ordinal) ^ ((ω : Ordinal) ^ (j : Ordinal))
      ≤ ω ^ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
        opow_le_opow_right omega0_pos hA
    _ ≤ toOrdinal (base i) (goodsteinSeq m i) := opow_toOrdinal_log_le (base i) hb hv

/-- **The `o = ω^j` diagonal, REDUCED to its second-level crux.** For finite `j ≥ 1`, if the SECOND
leading exponent of the seed-`m` descent is `≥ j` at step `m − 2`, then
`fastGrowing (ω^j) m ≤ goodsteinLength m + 2` with `ω^j = oadd (ofNat j) 1 0` (`repr = ω^j`). Mirrors
`fastGrowing_omega_le_goodsteinLength_of_largeRegime` one level up: `omega_pow_pow_le_seqONote_repr`
gives `ω^{ω^j} ≤ descent`; `goodstein_dominates_of_index_le` (budget `m`) closes it. `hreg2` is
Cichoń's lower bound at the level `ω^j`. -/
theorem fastGrowing_omega_pow_le_goodsteinLength_of_crux {m j : ℕ} (hm : 4 ≤ m) (hj1 : 1 ≤ j)
    (hjm : j < m)
    (hreg2 : j ≤ Nat.log (base (m - 2)) (Nat.log (base (m - 2)) (goodsteinSeq m (m - 2)))) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  set i := m - 2 with hi
  have hbase : base i = m := by simp only [base, hi]; omega
  have ho : (oadd (ONote.ofNat j) 1 0 : ONote).NF := NF.oadd inferInstance 1 NFBelow.zero
  have hv : goodsteinSeq m i ≠ 0 := by have := goodsteinSeq_ge_init m i (by omega); omega
  have hjb : j < base i := by rw [hbase]; exact hjm
  have hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0 := by
    intro h0; rw [h0, Nat.log_zero_right] at hreg2; omega
  have hidx : (oadd (oadd (ONote.ofNat j) 1 0) 1 0).repr ≤ (seqONote m i).repr := by
    have hr : (oadd (oadd (ONote.ofNat j) 1 0) 1 0 : ONote).repr
        = ω ^ ((ω : Ordinal) ^ (j : Ordinal)) := by
      simp [ONote.repr, ONote.repr_ofNat]
    rw [hr]
    exact omega_pow_pow_le_seqONote_repr hreg2 hjb hv hlead
  have hnorm : norm (oadd (ONote.ofNat j) 1 0) ≤ i + 2 := by
    rw [norm_oadd, norm_ofNat, norm_zero]; simp only [PNat.one_coe]; omega
  have hgl : i ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le ho hgl (by omega) hnorm hidx

/-- **The `o = ω^j` diagonal, REDUCED to a doubly-iterated length bound.** For finite `j ≥ 1`, if the
*doubly-iterated* seed `(log₂)^[2] m` has a Goodstein length `≥ (m−2)+j`, then
`fastGrowing (ω^j) m ≤ goodsteinLength m + 2`. The second-level crux `hreg2` is discharged by the
self-similarity tower (`iterLeadExp_dominates m 2`): the second leading exponent at step `m−2`
dominates `goodsteinSeq ((log₂)^[2] m) (m−2)`, which `n_le_goodsteinSeq` keeps `≥ j` exactly when the
doubly-iterated sequence still has `≥ j` steps to run. This is the limit-level analog of
`fastGrowing_omega_le_goodsteinLength_of_largeRegime` reduced one more scale down: the SOLE remaining
obligation is the length bound `goodsteinLength ((log₂)^[2] m) ≥ m` (next-lap crux — needs an
`f_ω`-strength lower bound at the deep seed, bootstrapped from `fastGrowing_omega_le_goodsteinLength`
itself). -/
theorem fastGrowing_omega_pow_le_goodsteinLength_of_length {m j : ℕ} (hm : 4 ≤ m) (hj1 : 1 ≤ j)
    (hjm : j < m)
    (hlen : (m - 2) + j ≤ goodsteinLength ((Nat.log 2)^[2] m)) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  apply fastGrowing_omega_pow_le_goodsteinLength_of_crux hm hj1 hjm
  have hbase : base (m - 2) = m := by simp only [base]; omega
  have hval : j ≤ goodsteinSeq ((Nat.log 2)^[2] m) (m - 2) :=
    n_le_goodsteinSeq ((Nat.log 2)^[2] m) (m - 2) j (by rw [hbase]; omega) hlen
  have hdom := iterLeadExp_dominates m 2 (m - 2)
  exact le_trans hval hdom

/-! ### Discharging the `o = ω^j` crux: an `f_ω`-strength length bound at the deep seed

The sole remaining obligation is `goodsteinLength ((log₂)^[2] m) ≥ m`. The exponential length bound is
far too weak at the doubly-iterated seed `t = (log₂)^[2] m` (it gives only `≈ 2^t`, while `m ≈ 2^{2^t}`).
But we now have `f_ω(t) ≤ goodsteinLength t + 2` — a *tower-strength* lower bound — and `f_ω` outgrows
`2^{2^{·}}`. Bootstrapping the `o = ω` result against itself closes the `o = ω^j` tier. -/

/-- `f_2(n) = 2^n · n` (mathlib's closed form, transported to the `ofNat 2` notation). -/
theorem fastGrowing_ofNat_two (n : ℕ) : fastGrowing (ONote.ofNat 2) n = 2 ^ n * n := by
  rw [show (ONote.ofNat 2 : ONote) = 2 from by decide, ONote.fastGrowing_two]

/-- **`f_3` is doubly-exponential:** `2^{2^t · t} ≤ f_3(t)` for `t ≥ 2`. Since `f_3(t) = (f_2)^[t](t)`
(`fastGrowing_succ`), and `f_2` is expansive, `(f_2)^[t](t) ≥ (f_2)^[2](t) = f_2(f_2(t)) =
2^{2^t·t}·(2^t·t) ≥ 2^{2^t·t}`. The engine that makes `f_ω` outrun `2^{2^{·}}`. -/
theorem two_pow_le_fastGrowing_ofNat_three {t : ℕ} (ht : 2 ≤ t) :
    2 ^ (2 ^ t * t) ≤ fastGrowing (ONote.ofNat 3) t := by
  have hf3 : fastGrowing (ONote.ofNat 3) t = (fastGrowing (ONote.ofNat 2))^[t] t := by
    rw [show (ONote.ofNat 3 : ONote) = ONote.ofNat (2 + 1) from rfl,
        fastGrowing_succ _ (fundamentalSequence_ofNat_succ 2)]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing (ONote.ofNat 2) := fun n => le_fastGrowing _ n
  have hmono : (fastGrowing (ONote.ofNat 2))^[2] t ≤ (fastGrowing (ONote.ofNat 2))^[t] t :=
    Function.monotone_iterate_of_id_le hexp ht t
  have h2it : (fastGrowing (ONote.ofNat 2))^[2] t
      = fastGrowing (ONote.ofNat 2) (fastGrowing (ONote.ofNat 2) t) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
  rw [hf3]
  refine le_trans ?_ hmono
  rw [h2it, fastGrowing_ofNat_two, fastGrowing_ofNat_two]
  have hpos : 1 ≤ 2 ^ t * t := by
    have : 0 < 2 ^ t * t := Nat.mul_pos (pow_pos (by norm_num) t) (by omega); omega
  calc 2 ^ (2 ^ t * t) = 2 ^ (2 ^ t * t) * 1 := (mul_one _).symm
    _ ≤ 2 ^ (2 ^ t * t) * (2 ^ t * t) := by gcongr

/-- `f_ω(t) = f_{t+1}(t)`: the fundamental sequence of `ω = oadd 1 1 0` is `i ↦ ofNat (i+1)`. -/
theorem fastGrowing_omega_eq (t : ℕ) :
    fastGrowing (oadd 1 1 0) t = fastGrowing (ONote.ofNat (t + 1)) t := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ONote.ofNat (i + 1)) := rfl
  rw [fastGrowing_limit (oadd 1 1 0) hfs]

/-- **The doubly-iterated length bound — `o = ω^j`'s crux DISCHARGED.** For `m` with the doubly-
iterated seed `t = (log₂)^[2] m ≥ 2^16`, `goodsteinLength t ≥ 2m`. Bootstraps the `o = ω` domination
against itself: `goodsteinLength t ≥ f_ω(t) − 2 = f_{t+1}(t) − 2 ≥ f_3(t) − 2 ≥ 2^{2^t·t} − 2`
(`fastGrowing_omega_le_goodsteinLength` ⊕ `fastGrowing_ofNat_mono` ⊕ `two_pow_le_fastGrowing_ofNat_three`),
while `m < 2^{2^{t+1}}` and `2^t·t ≥ 2^{t+1}+1` (for `t ≥ 3`) give `2^{2^t·t} ≥ 2(m+1)`. The `f_ω`
length bound carries the finite-base-case `native_decide` axioms (documented split). -/
theorem two_mul_le_goodsteinLength_loglog {m : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) :
    2 * m ≤ goodsteinLength ((Nat.log 2)^[2] m) := by
  set t := (Nat.log 2)^[2] m with htdef
  have hteq : t = Nat.log 2 (Nat.log 2 m) := rfl
  have hA : Nat.log 2 m + 1 ≤ 2 ^ (t + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Nat.log 2 m)
    rw [hteq]; omega
  have hB : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hD : 2 ^ (Nat.log 2 m + 1) ≤ 2 ^ (2 ^ (t + 1)) := Nat.pow_le_pow_right (by norm_num) hA
  have hm1 : m + 1 ≤ 2 ^ (2 ^ (t + 1)) := by omega
  have hlen := fastGrowing_omega_le_goodsteinLength (m := t) ht
  rw [fastGrowing_omega_eq] at hlen
  have hidx : fastGrowing (ONote.ofNat 3) t ≤ fastGrowing (ONote.ofNat (t + 1)) t :=
    fastGrowing_ofNat_mono (by omega) (by omega)
  have hf3 := two_pow_le_fastGrowing_ofNat_three (t := t) (by omega)
  have hexp_ge : 2 ^ (t + 1) + 1 ≤ 2 ^ t * t := by
    have h2t : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
    have hb : 2 ^ t * 3 ≤ 2 ^ t * t := by gcongr <;> omega
    have hp : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    omega
  have hpow_ge : 2 * (m + 1) ≤ 2 ^ (2 ^ t * t) := by
    have h2 : 2 * 2 ^ (2 ^ (t + 1)) = 2 ^ (2 ^ (t + 1) + 1) := by rw [pow_succ]; ring
    have h3 : 2 ^ (2 ^ (t + 1) + 1) ≤ 2 ^ (2 ^ t * t) := Nat.pow_le_pow_right (by norm_num) hexp_ge
    omega
  omega

/-- **THE `o = ω^j` DIAGONAL DOMINATION — UNCONDITIONAL** (every finite `j ≥ 1`, for `m` with
`(log₂)^[2] m ≥ 2^16`): `fastGrowing (ω^j) m ≤ goodsteinLength m + 2`, with `ω^j = oadd (ofNat j) 1 0`.
Cichoń's lower bound at the limit levels `ω, ω^2, ω^3, …` — fully machine-checked. The doubly-iterated
length bound `two_mul_le_goodsteinLength_loglog` discharges the `of_length` reduction's hypothesis
(`(m−2)+j < 2m ≤ goodsteinLength ((log₂)^[2] m)`). Carries the finite-base-case `native_decide` axioms
(documented split), inherited through the `f_ω` bootstrap. -/
theorem fastGrowing_omega_pow_le_goodsteinLength {m j : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) (hj1 : 1 ≤ j) (hjm : j < m) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  have h1' : 1 ≤ (Nat.log 2)^[2] m := le_trans (by norm_num) ht
  have hlm0 : Nat.log 2 m ≠ 0 := by
    intro h
    rw [show (Nat.log 2)^[2] m = Nat.log 2 (Nat.log 2 m) from rfl, h, Nat.log_zero_right] at h1'
    omega
  have hlogm2 : 2 ≤ Nat.log 2 m := by
    have h := Nat.pow_le_of_le_log hlm0 (show 1 ≤ Nat.log 2 (Nat.log 2 m) from h1'); simpa using h
  have hm0 : m ≠ 0 := by intro h; rw [h, Nat.log_zero_right] at hlogm2; omega
  have hm : 4 ≤ m := by have h := Nat.pow_le_of_le_log hm0 hlogm2; simpa using h
  apply fastGrowing_omega_pow_le_goodsteinLength_of_length hm hj1 hjm
  have h2m := two_mul_le_goodsteinLength_loglog ht
  omega

/-- Anti-vacuity: `ω = oadd 1 1 0` really has `repr = ω`, and `oadd ω 1 0` has `repr = ω^ω` — so the
reduction targets the genuine limit level, not a finite stand-in. -/
example : (oadd 1 1 0 : ONote).repr = ω := by simp [ONote.repr]
example : (oadd (oadd 1 1 0) 1 0 : ONote).repr = ω ^ (ω : Ordinal) := by simp [ONote.repr]
example (j : ℕ) : (oadd (oadd (ONote.ofNat j) 1 0) 1 0 : ONote).repr
    = ω ^ ((ω : Ordinal) ^ (j : Ordinal)) := by simp [ONote.repr, ONote.repr_ofNat]

end LeanFormalizations.Logic.Goodstein
