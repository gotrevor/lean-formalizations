/-
# The Hardy ↔ fast-growing bridge: `f_α ≤ H_{ω^α}`

The Cichoń identity (`Logic/Goodstein/Growth.lean`) gives
`goodsteinLength m = H_{toONote 2 m}(2) − 2`. To turn that into "Goodstein grows like the
fast-growing hierarchy" we relate the Hardy hierarchy `H_α` to the fast-growing hierarchy
`f_α`. The classical identity `H_{ω^α} = f_α` holds under the `ω[n]=n` convention; mathlib uses
`ω[n] = n+1`, which makes `H_{ω^α}` strictly *bigger*, so we prove the robust one-sided bound

  `fastGrowing α n ≤ hardy (oadd α 1 0) n`   (`fastGrowing_le_hardy_pow`).

The linchpin is the **Hardy iteration law** `H_{ω^e·(k+1)} = (H_{ω^e})^[k+1]`
(`hardy_oadd_iter`), whose engine is the **leading-term split**
`H_{ω^e·c + R}(n) = H_{ω^e·c}(H_R(n))` (`hardy_split`) — valid because the `NF` condition
`repr R < ω^(repr e)` is exactly the no-absorption side condition the Hardy additive law needs.
-/
import LeanFormalizations.Logic.Goodstein.Growth

namespace LeanFormalizations.Logic.Goodstein

open ONote Ordinal
open LeanFormalizations.Logic.FastGrowing

/-- **Iterate domination.** If `f ≤ g` pointwise and `g` is monotone, then `f^[j] ≤ g^[j]`
pointwise. -/
theorem iterate_le_iterate {f g : ℕ → ℕ} (hfg : ∀ m, f m ≤ g m) (hg : Monotone g) :
    ∀ j x, f^[j] x ≤ g^[j] x := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ j ih =>
    intro x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (ih (f x)).trans ((hg.iterate j) (hfg x))

/-- `(· + 1)^[j] n = n + j`. -/
theorem succ_iterate (j n : ℕ) : (fun m => m + 1)^[j] n = n + j := by
  induction j with
  | zero => simp
  | succ j ih => simp only [Function.iterate_succ_apply', ih]; omega

/-- **Leading-term split for the Hardy hierarchy.** For a normal-form notation `oadd e c R`
(so `repr R < ω^(repr e)`), the Hardy function splits its leading Cantor term off the tail:
`H_{ω^e·c + R}(n) = H_{ω^e·c}(H_R(n))`. Well-founded recursion on `repr R`. The `NF` hypothesis
is the no-absorption side condition that makes the Hardy additive law hold. -/
theorem hardy_split (e : ONote) (c : ℕ+) (R : ONote) (hNF : (oadd e c R).NF) (n : ℕ) :
    hardy (oadd e c R) n = hardy (oadd e c 0) (hardy R n) := by
  suffices H : ∀ o : Ordinal, ∀ R : ONote, R.repr = o → (oadd e c R).NF → ∀ n,
      hardy (oadd e c R) n = hardy (oadd e c 0) (hardy R n) by
    exact H R.repr R rfl hNF n
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro R hrepr hNFR n
    have hNFe : e.NF := hNFR.fst
    have hbelowR : R.repr < ω ^ e.repr := hNFR.snd'.repr_lt
    rcases hfs : fundamentalSequence R with (_ | R') | g
    · -- R = 0
      have hR0 : R = 0 :=
        (fundamentalSequenceProp_inl_none R).1 (hfs ▸ fundamentalSequence_has_prop R)
      subst hR0
      simp
    · -- R successor R'
      have hsucc := (fundamentalSequenceProp_inl_some R R').1 (hfs ▸ fundamentalSequence_has_prop R)
      have hNFR' : R'.NF := hsucc.2 hNFR.snd
      have hltR' : R'.repr < o := by rw [← hrepr, hsucc.1]; exact Order.lt_succ _
      have hbelowR' : R'.repr < ω ^ e.repr :=
        lt_trans (by rw [hrepr]; exact hltR') hbelowR
      have hNFnew : (oadd e c R').NF := NF.oadd hNFe c (NF.below_of_lt' hbelowR' hNFR')
      have hfsnew : fundamentalSequence (oadd e c R) = Sum.inl (some (oadd e c R')) := by
        rw [fundamentalSequence, hfs]
      simp only [hardy_succ _ hfsnew, hardy_succ _ hfs]
      exact ih R'.repr hltR' R' rfl hNFnew (n + 1)
    · -- R limit g
      have hprop := hfs ▸ fundamentalSequence_has_prop R
      have hgnlt : (g n).repr < o := by rw [← hrepr]; exact repr_lt_repr (hprop.2.1 n).2.1
      have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFR.snd
      have hbelowgn : (g n).repr < ω ^ e.repr :=
        lt_trans (by rw [hrepr]; exact hgnlt) hbelowR
      have hNFnew : (oadd e c (g n)).NF := NF.oadd hNFe c (NF.below_of_lt' hbelowgn hNFgn)
      have hfsnew : fundamentalSequence (oadd e c R) = Sum.inr (fun i => oadd e c (g i)) := by
        rw [fundamentalSequence, hfs]
      simp only [hardy_limit _ hfsnew, hardy_limit _ hfs]
      exact ih (g n).repr hgnlt (g n) rfl hNFnew n

/-- Finite Hardy values: `H_{j+1}(n) = n + (j+1)` (the notation `oadd 0 ⟨j+1⟩ 0`). -/
theorem hardy_finite : ∀ j n, hardy (oadd 0 ⟨j + 1, Nat.succ_pos j⟩ 0) n = n + (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro n
    show hardy (oadd 0 1 0) n = n + 1
    rw [show (oadd (0 : ONote) 1 0) = 1 from rfl, hardy_one]
  | succ j ih =>
    intro n
    have hfs : fundamentalSequence (oadd 0 ⟨j + 2, Nat.succ_pos _⟩ 0)
        = Sum.inl (some (oadd 0 ⟨j + 1, Nat.succ_pos j⟩ 0)) := by
      rw [fundamentalSequence_oadd_zero_zero]; rfl
    simp only [hardy_succ _ hfs]
    rw [ih (n + 1)]; omega

/-- **Hardy coefficient step (nonzero exponent).** For `e ≠ 0`,
`H_{ω^e·(k+2)}(n) = H_{ω^e·(k+1)}(H_{ω^e}(n))`. The descent peels one coefficient
(`fundSeq_oadd_coeff`), then `hardy_split` separates the freshly-created lowest term, whose
Hardy value is exactly `H_{ω^e}(n)` (it is the index-`n` fundamental term of `ω^e`). -/
theorem hardy_oadd_coeff_step_ne (e : ONote) (he : e ≠ 0) (hNFe : e.NF) (k n : ℕ) :
    hardy (oadd e ⟨k + 2, Nat.succ_pos _⟩ 0) n
      = hardy (oadd e ⟨k + 1, Nat.succ_pos k⟩ 0) (hardy (oadd e 1 0) n) := by
  obtain ⟨g, hg1, hgk⟩ := fundSeq_oadd_coeff e he k
  have hNFe1 : (oadd e 1 0).NF := NF.oadd hNFe 1 NFBelow.zero
  have hprop := hg1 ▸ fundamentalSequence_has_prop (oadd e 1 0)
  have hgnlt : (g n).repr < (oadd e 1 0).repr := repr_lt_repr (hprop.2.1 n).2.1
  have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFe1
  have hbelow : (g n).repr < ω ^ e.repr := by
    have he1 : (oadd e 1 0).repr = ω ^ e.repr := by simp
    rwa [he1] at hgnlt
  have hNFsplit : (oadd e k.succPNat (g n)).NF :=
    NF.oadd hNFe _ (NF.below_of_lt' hbelow hNFgn)
  simp only [hardy_limit _ hgk]
  show hardy (oadd e k.succPNat (g n)) n
      = hardy (oadd e k.succPNat 0) (hardy (oadd e 1 0) n)
  rw [hardy_split e k.succPNat (g n) hNFsplit n]
  have heq : hardy (oadd e 1 0) n = hardy (g n) n := by simp only [hardy_limit _ hg1]
  rw [heq]

/-- **The Hardy iteration law.** `H_{ω^e·(k+1)} = (H_{ω^e})^[k+1]`. For `e = 0` this is
`H_{k+1}(n) = n+(k+1) = (·+1)^[k+1] n`; for `e ≠ 0` it is induction on `k` via the coefficient
step `hardy_oadd_coeff_step_ne`. The linchpin tying Hardy coefficients to iteration. -/
theorem hardy_oadd_iter (e : ONote) (hNFe : e.NF) :
    ∀ k n, hardy (oadd e ⟨k + 1, Nat.succ_pos k⟩ 0) n = (hardy (oadd e 1 0))^[k + 1] n := by
  rcases eq_or_ne e 0 with rfl | he
  · -- e = 0
    have hg : hardy (oadd (0 : ONote) 1 0) = fun n => n + 1 := by
      rw [show (oadd (0 : ONote) 1 0) = 1 from rfl]; exact hardy_one
    intro k n
    rw [hardy_finite k n, hg, succ_iterate]
  · -- e ≠ 0: induction on k via the coefficient step
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have hcoeff := hardy_oadd_coeff_step_ne e he hNFe k n
      have hk2 : (⟨k + 1 + 1, Nat.succ_pos (k + 1)⟩ : ℕ+) = ⟨k + 2, Nat.succ_pos _⟩ := rfl
      rw [hk2, hcoeff, ih (hardy (oadd e 1 0) n), ← Function.iterate_succ_apply]

/-- **The Hardy ↔ fast-growing bridge.** `fastGrowing α n ≤ hardy (oadd α 1 0) n`, i.e.
`f_α ≤ H_{ω^α}`. Well-founded recursion on `repr α`: base/limit are direct; the successor case
`f_{α'+1}(n) = (f_{α'})^[n](n)` is dominated by `(H_{ω^{α'}})^[n+1](n) = H_{ω^{α'+1}}(n)` via the
iteration law, the IH lifted through `iterate_le_iterate`, and one extra expansive iterate. -/
theorem fastGrowing_le_hardy_pow (α : ONote) (hNF : α.NF) (n : ℕ) :
    fastGrowing α n ≤ hardy (oadd α 1 0) n := by
  suffices H : ∀ o : Ordinal, ∀ α : ONote, α.repr = o → α.NF → ∀ n,
      fastGrowing α n ≤ hardy (oadd α 1 0) n by
    exact H α.repr α rfl hNF n
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro α hrepr hNFα n
    rcases hfs : fundamentalSequence α with (_ | α') | g
    · -- α = 0
      have hα0 : α = 0 :=
        (fundamentalSequenceProp_inl_none α).1 (hfs ▸ fundamentalSequence_has_prop α)
      subst hα0
      rw [fastGrowing_zero' 0 rfl]
      show Nat.succ n ≤ hardy (oadd 0 1 0) n
      rw [show (oadd (0 : ONote) 1 0) = 1 from rfl, hardy_one]
    · -- α successor α'
      have hsucc := (fundamentalSequenceProp_inl_some α α').1 (hfs ▸ fundamentalSequence_has_prop α)
      have hNFα' : α'.NF := hsucc.2 hNFα
      have hltα' : α'.repr < o := by rw [← hrepr, hsucc.1]; exact Order.lt_succ _
      rw [fastGrowing_succ α hfs]
      simp only [hardy_limit _ (fundSeq_oadd_one_of_succ hfs)]
      show (fastGrowing α')^[n] n ≤ hardy (oadd α' n.succPNat 0) n
      rw [show (n.succPNat : ℕ+) = ⟨n + 1, Nat.succ_pos n⟩ from rfl, hardy_oadd_iter α' hNFα' n n]
      calc (fastGrowing α')^[n] n
          ≤ (hardy (oadd α' 1 0))^[n] n :=
            iterate_le_iterate (fun m => ih α'.repr hltα' α' rfl hNFα' m) (hardy_monotone _) n n
        _ ≤ (hardy (oadd α' 1 0))^[n + 1] n := by
            rw [Function.iterate_succ_apply']
            exact le_hardy (oadd α' 1 0) _
    · -- α limit g
      have hprop := hfs ▸ fundamentalSequence_has_prop α
      have hgnlt : (g n).repr < o := by rw [← hrepr]; exact repr_lt_repr (hprop.2.1 n).2.1
      have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFα
      rw [fastGrowing_limit α hfs]
      simp only [hardy_limit _ (fundSeq_oadd_one_of_limit hfs)]
      show fastGrowing (g n) n ≤ hardy (oadd (g n) 1 0) n
      exact ih (g n).repr hgnlt (g n) rfl hNFgn n

/-- **`toOrdinal 2` is cofinal below ε₀.** Every notation `β` is eventually exceeded by some
`toOrdinal 2 N` — the Goodstein ordinals `repr (toONote 2 m)` reach arbitrarily high below ε₀.
Structural induction on `β`: for `oadd e c r`, `repr β < ω^(repr e + 1) ≤ ω^(toOrdinal 2 Ne)
= toOrdinal 2 (2^Ne)` using `toOrdinal_pow` and the IH on the exponent `e`. -/
theorem toOrdinal_two_cofinal : ∀ β : ONote, β.NF → ∃ N : ℕ, β.repr < toOrdinal 2 N := by
  intro β
  induction β with
  | zero =>
    intro _
    refine ⟨1, ?_⟩
    have h1 : toOrdinal 2 1 = 1 := by have h := toOrdinal_pow 2 le_rfl 0; simpa using h
    have h0 : (ONote.zero : ONote).repr = 0 := rfl
    rw [h0, h1]; exact zero_lt_one
  | oadd e c r ihe _ =>
    intro hNF
    obtain ⟨Ne, hNe⟩ := ihe hNF.fst
    refine ⟨2 ^ Ne, ?_⟩
    have hbound : (oadd e c r).repr < ω ^ (e.repr + 1) := by
      have h := (NF.below_of_lt (b := e.repr + 1)
        (by rw [← Order.succ_eq_add_one]; exact Order.lt_succ _) hNF).repr_lt
      exact h
    have hle : e.repr + 1 ≤ toOrdinal 2 Ne := by
      rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hNe
    calc (oadd e c r).repr < ω ^ (e.repr + 1) := hbound
      _ ≤ ω ^ toOrdinal 2 Ne := opow_le_opow_right omega0_pos hle
      _ = toOrdinal 2 (2 ^ Ne) := (toOrdinal_pow 2 le_rfl Ne).symm

/-! ### A linear lower bound on the Goodstein length

`goodsteinLength m ≥ m`: a concrete (citable) growth lower bound, and sub-fact (i) toward the
full domination headline (it makes the high-budget step `j = m-2` of the telescope available).
The engine is `le_bump` (the hereditary bump never decreases its argument), which gives
`G_{k+1} = bump(..) − 1 ≥ G_k − 1`, hence `G_k ≥ m − k`, so `G_k ≠ 0` for `k < m`. -/

/-- **The hereditary bump never decreases:** `n ≤ bump b n` for `b ≥ 2`. Reading `n` in
hereditary base `b` and replacing `b` by `b+1` can only grow each digit's place value. Strong
induction mirroring `bump`'s recursion: `(b+1)^(bump b L) ≥ b^L` (via the IH `L ≤ bump b L`). -/
theorem le_bump (b : ℕ) (hb : 2 ≤ b) : ∀ n, n ≤ bump b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [bump_pos b n hn]
      set L := Nat.log b n with hL
      have hbe_pos : 0 < b ^ L := Nat.pow_pos (by omega)
      have hbe_le : b ^ L ≤ n := Nat.pow_log_le_self b hn
      have hlog : L < n := Nat.log_lt_self b hn
      have hr_lt : n % b ^ L < n := lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have h1 : b ^ L ≤ (b + 1) ^ bump b L :=
        calc b ^ L ≤ (b + 1) ^ L := Nat.pow_le_pow_left (by omega) L
          _ ≤ (b + 1) ^ bump b L := Nat.pow_le_pow_right (by omega) (ih L hlog)
      have h2 : n % b ^ L ≤ bump b (n % b ^ L) := ih _ hr_lt
      have key : n / b ^ L * b ^ L + n % b ^ L
          ≤ n / b ^ L * (b + 1) ^ bump b L + bump b (n % b ^ L) := by gcongr
      have hdm : n / b ^ L * b ^ L + n % b ^ L = n := Nat.div_add_mod' n (b ^ L)
      omega

/-- Each Goodstein term is at least `m − k` (truncated): `m − k ≤ goodsteinSeq m k`. Induction
on `k` using `le_bump` (`G_{k+1} = bump(base k, G_k) − 1 ≥ G_k − 1`). -/
theorem goodsteinSeq_ge_sub (m : ℕ) : ∀ k, m - k ≤ goodsteinSeq m k := by
  intro k
  induction k with
  | zero => have h0 : goodsteinSeq m 0 = m := rfl; omega
  | succ k ih =>
    have hb : goodsteinSeq m k ≤ bump (base k) (goodsteinSeq m k) :=
      le_bump (base k) (Nat.le_add_left 2 k) _
    show m - (k + 1) ≤ bump (base k) (goodsteinSeq m k) - 1
    omega

/-- **Goodstein length grows at least linearly:** `m ≤ goodsteinLength m`. Since
`goodsteinSeq m k ≥ m − k ≥ 1` for every `k < m`, the sequence is nonzero before step `m`, so its
first zero is at step `≥ m`. -/
theorem le_goodsteinLength (m : ℕ) : m ≤ goodsteinLength m := by
  rw [goodsteinLength, Nat.le_find_iff]
  intro k hk
  have hge := goodsteinSeq_ge_sub m k
  omega

/-! ### Growth: the Goodstein term stays `≥ m` for the first `m` steps

The linear bound `goodsteinSeq m k ≥ m − k` above only certifies *non-vanishing*; it says nothing
about growth. The genuine engine of Goodstein growth is that, **while the value is at least the
current base, one bump step does not decrease it** (`bump b n ≥ n + 1` for `n ≥ b` — the leading
power `b^L` strictly grows to `(b+1)^{bump b L} > b^L`, dominating the `−1`). Since the start value
`m` exceeds the base `k+2` for all `k ≤ m−2`, the sequence is non-decreasing across that whole
range, hence stays `≥ m`. Consequently the descent ordinal `seqOrd m j` stays `≥ ω` for the first
`~m` steps — the first "ordinal-stays-high" lower bound, and exactly sub-fact (ii) at level `o = 1`. -/

/-- **Strict growth above the base.** For `2 ≤ b` and `b ≤ n`, one bump step strictly increases
the value: `n + 1 ≤ bump b n`. The leading power `b^L` (with `L = log b n ≥ 1`) is sent to
`(b+1)^{bump b L} ≥ (b+1)^L > b^L`, so the leading term alone already exceeds `n`. -/
theorem bump_gt (b : ℕ) (hb : 2 ≤ b) {n : ℕ} (hn : b ≤ n) : n + 1 ≤ bump b n := by
  have hb1 : 1 < b := by omega
  have hn0 : n ≠ 0 := by omega
  set L := Nat.log b n with hL
  have hL1 : 1 ≤ L := Nat.log_pos hb1 hn
  have hbe_pos : 0 < b ^ L := Nat.pow_pos (by omega)
  have hbe_le : b ^ L ≤ n := Nat.pow_log_le_self b hn0
  have hq1 : 1 ≤ n / b ^ L := Nat.div_pos hbe_le hbe_pos
  have hpow_lt : b ^ L < (b + 1) ^ L := Nat.pow_lt_pow_left (by omega) (by omega)
  have hpow_le : (b + 1) ^ L ≤ (b + 1) ^ bump b L :=
    Nat.pow_le_pow_right (by omega) (le_bump b hb L)
  have hP : b ^ L + 1 ≤ (b + 1) ^ bump b L := by omega
  have hr_le : n % b ^ L ≤ bump b (n % b ^ L) := le_bump b hb _
  have hbump : bump b n = n / b ^ L * (b + 1) ^ bump b L + bump b (n % b ^ L) := bump_pos b n hn0
  have hn_eq : n / b ^ L * b ^ L + n % b ^ L = n := Nat.div_add_mod' n (b ^ L)
  set q := n / b ^ L with hq
  set BL := b ^ L with hBL
  set P := (b + 1) ^ bump b L with hPdef
  have hmul : q * (BL + 1) ≤ q * P := by gcongr
  have hexp : q * (BL + 1) = q * BL + q := by ring
  rw [hbump]
  omega

/-- **The leading exponent bumps itself.** `Nat.log (b+1) (bump b n) = bump b (Nat.log b n)`:
reading `bump b n` in the new base `b+1`, its leading exponent is the bump of `n`'s leading
exponent. The recursive skeleton behind Goodstein growth — the *exponent* evolves like a
lower-level Goodstein term, which is why the descent ordinal's leading CNF exponent stays high for
astronomically many steps. (Extracted from the `hlog` step of `toOrdinal_bump`.) -/
theorem log_bump (b : ℕ) (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    Nat.log (b + 1) (bump b n) = bump b (Nat.log b n) := by
  have hb1 : 1 < b := by omega
  set e := Nat.log b n with he
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hbe_le : b ^ e ≤ n := Nat.pow_log_le_self b hn
  have hc_pos : 0 < n / b ^ e := Nat.div_pos hbe_le hbe_pos
  have hc_lt : n / b ^ e < b := by
    rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']; exact Nat.lt_pow_succ_log_self hb1 n
  have hr_lt : n % b ^ e < b ^ e := Nat.mod_lt _ hbe_pos
  have hR_lt : bump b (n % b ^ e) < (b + 1) ^ bump b e := bump_lt_pow b hb hr_lt
  have hbump_eq : bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := bump_pos b n hn
  rw [hbump_eq]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · calc (b + 1) ^ bump b e = 1 * (b + 1) ^ bump b e := (one_mul _).symm
      _ ≤ n / b ^ e * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ hc_pos
      _ ≤ n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := Nat.le_add_right _ _
  · calc n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e)
        < n / b ^ e * (b + 1) ^ bump b e + (b + 1) ^ bump b e := Nat.add_lt_add_left hR_lt _
      _ = (n / b ^ e + 1) * (b + 1) ^ bump b e := by ring
      _ ≤ (b + 1) * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ (by omega)
      _ = (b + 1) ^ (bump b e + 1) := by rw [pow_succ]; ring

/-- **The leading exponent does NOT drop at a non-pure-power step.** If `n` is *not* a pure power of
`b` — i.e. `b ^ log_b n < n`, equivalently `n` has a leading coefficient `≥ 2` or a nonzero lower
remainder — then the Goodstein `−1` is absorbed by the lower terms and the leading exponent is
exactly preserved across the step:
`Nat.log (b+1) (bump b n − 1) = bump b (Nat.log b n)` (the same value `log_bump` gives for `bump b n`
itself). The reason: `bump b n = c·(b+1)^{bump b e} + R` with `c ≥ 1`, `R < (b+1)^{bump b e}`, and the
not-a-pure-power hypothesis forces `bump b n > (b+1)^{bump b e}`, so subtracting `1` cannot cross the
power boundary. (When `n = b^{log_b n}` is a pure power the log *does* drop by one — the rare "borrow"
event.) **This is the structural reason leading-exponent drops are RARE** — they occur only at the
pure-power boundaries — and is the first brick of the steps-between-drops recursion that would upgrade
the domination budget `log₂ m → m` (closing the diagonal `f_o(m) ≤ goodsteinLength m`). -/
theorem log_bump_pred_of_not_pow (b : ℕ) (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0)
    (hnp : b ^ Nat.log b n < n) :
    Nat.log (b + 1) (bump b n - 1) = bump b (Nat.log b n) := by
  have hb1 : 1 < b := by omega
  set e := Nat.log b n with he
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hbe_le : b ^ e ≤ n := Nat.pow_log_le_self b hn
  have hc_pos : 0 < n / b ^ e := Nat.div_pos hbe_le hbe_pos
  have hr_lt : n % b ^ e < b ^ e := Nat.mod_lt _ hbe_pos
  have hR_lt : bump b (n % b ^ e) < (b + 1) ^ bump b e := bump_lt_pow b hb hr_lt
  have hbump_eq : bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := bump_pos b n hn
  have hP_pos : 0 < (b + 1) ^ bump b e := Nat.pow_pos (by omega)
  -- the not-a-pure-power hypothesis: leading coeff `≥ 2`, or nonzero remainder
  have hcase : 2 ≤ n / b ^ e ∨ 0 < n % b ^ e := by
    rcases Nat.eq_zero_or_pos (n % b ^ e) with hr0 | hrpos
    · left
      have key : b ^ e * (n / b ^ e) + n % b ^ e = n := Nat.div_add_mod n (b ^ e)
      rcases Nat.lt_or_ge (n / b ^ e) 2 with hlt | hge
      · have hc1 : n / b ^ e = 1 := by omega
        rw [hc1, hr0, mul_one, add_zero] at key
        omega
      · exact hge
    · right; exact hrpos
  -- hence `bump b n > (b+1)^{bump b e}`, so the `−1` does not cross the power boundary
  have hgt : (b + 1) ^ bump b e < bump b n := by
    rcases hcase with hc2 | hrpos
    · have h2P : 2 * (b + 1) ^ bump b e ≤ n / b ^ e * (b + 1) ^ bump b e := by gcongr
      rw [hbump_eq]; omega
    · have hR1 : 1 ≤ bump b (n % b ^ e) := le_trans hrpos (le_bump b hb _)
      have hPle : (b + 1) ^ bump b e ≤ n / b ^ e * (b + 1) ^ bump b e := by
        conv_lhs => rw [← one_mul ((b + 1) ^ bump b e)]
        gcongr; omega
      rw [hbump_eq]; omega
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · have hub : bump b n < (b + 1) ^ (bump b e + 1) := by
      calc bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := hbump_eq
        _ < n / b ^ e * (b + 1) ^ bump b e + (b + 1) ^ bump b e := by omega
        _ = (n / b ^ e + 1) * (b + 1) ^ bump b e := by ring
        _ ≤ (b + 1) * (b + 1) ^ bump b e := by
            apply Nat.mul_le_mul_right
            have hc_lt : n / b ^ e < b := by
              rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']; exact Nat.lt_pow_succ_log_self hb1 n
            omega
        _ = (b + 1) ^ (bump b e + 1) := by rw [pow_succ]; ring
    omega

/-- **The leading exponent drops by exactly one at a pure-power step** (the rare "borrow" event).
If `n = b ^ log_b n` is a pure power with `log_b n ≥ 1`, then `bump b n = (b+1)^{bump b (log_b n)}`
exactly (coefficient `1`, no lower terms), so the Goodstein `−1` borrows from the top and the leading
exponent decrements:
`Nat.log (b+1) (bump b n − 1) = bump b (Nat.log b n) − 1`.
Together with `log_bump_pred_of_not_pow` (no drop off the pure-power boundaries) this is the complete
per-step behaviour of the leading exponent: it bumps itself and grows everywhere except at the pure
powers, where it falls by exactly one. The steps-between-drops recursion = the gaps between these
pure-power events, each itself a sub-Goodstein-length. -/
theorem log_bump_pred_of_pow (b : ℕ) (hb : 2 ≤ b) {n : ℕ}
    (he1 : 1 ≤ Nat.log b n) (hnp : n = b ^ Nat.log b n) :
    Nat.log (b + 1) (bump b n - 1) = bump b (Nat.log b n) - 1 := by
  have hb1 : 1 < b := by omega
  set e := Nat.log b n with he
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hn0 : n ≠ 0 := by rw [hnp]; positivity
  have hbump_eq : bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := bump_pos b n hn0
  have hdiv : n / b ^ e = 1 := by rw [hnp]; exact Nat.div_self hbe_pos
  have hmod : n % b ^ e = 0 := by rw [hnp]; exact Nat.mod_self _
  have hb0 : bump b 0 = 0 := by rw [bump]; simp
  rw [hdiv, hmod, one_mul, hb0, add_zero] at hbump_eq
  set B := bump b e with hB
  have hB1 : 1 ≤ B := le_trans he1 (le_bump b hb e)
  have hbp_pos : 0 < (b + 1) ^ B := Nat.pow_pos (by omega)
  rw [hbump_eq]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hlt : (b + 1) ^ (B - 1) < (b + 1) ^ B := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  · have hBeq : (B - 1) + 1 = B := by omega
    rw [hBeq]; omega

/-- **Decrementing lowers a logarithm by at most one:** `Nat.log b x ≤ Nat.log b (x − 1) + 1`
(for `1 < b`). If `L = log b x ≥ 1` then `b^L ≤ x`, so `b^(L−1) < b^L ≤ x`, hence `b^(L−1) ≤ x−1`
and `L − 1 ≤ log b (x − 1)`. The general fact that a single decrement crosses at most one power. -/
theorem log_le_log_pred_succ (b : ℕ) (hb : 1 < b) (x : ℕ) :
    Nat.log b x ≤ Nat.log b (x - 1) + 1 := by
  rcases Nat.eq_zero_or_pos (Nat.log b x) with hL0 | hLpos
  · omega
  · have hx0 : x ≠ 0 := by
      intro h; rw [h, Nat.log_zero_right] at hLpos; exact Nat.lt_irrefl 0 hLpos
    have hbL : b ^ Nat.log b x ≤ x := Nat.pow_log_le_self b hx0
    have hb1L : b ^ 1 ≤ b ^ Nat.log b x := Nat.pow_le_pow_right (by omega) hLpos
    have hge : b ≤ x := by rw [pow_one] at hb1L; omega
    have hx1 : x - 1 ≠ 0 := by omega
    have hpowlt : b ^ (Nat.log b x - 1) < b ^ Nat.log b x := Nat.pow_lt_pow_right hb (by omega)
    have hpow : b ^ (Nat.log b x - 1) ≤ x - 1 := by omega
    have := (Nat.le_log_iff_pow_le hb hx1).2 hpow
    omega

/-- **The leading CNF exponent drops by at most one per Goodstein step** (while the term is at
least its base). Reading the leading exponent `L_k = log_{base k}(G_k)`, the step gives
`L_k ≤ L_{k+1} + 1`: `log_bump` sends the exponent `L_k` to `bump (base k) L_k ≥ L_k` in the new
base, and the `− 1` in `G_{k+1} = bump _ G_k − 1` lowers that log by at most one
(`log_le_log_pred_succ`). This is the recursion's per-level skeleton: the leading exponent itself
descends Goodstein-style, so it cannot fall below a fixed level `o` until astronomically many
steps have passed — the structural reason sub-fact (ii) holds for every fixed `o`. -/
theorem leadExp_drop_le_one (m k : ℕ) (h : base k ≤ goodsteinSeq m k) :
    Nat.log (base k) (goodsteinSeq m k)
      ≤ Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) + 1 := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hv0 : goodsteinSeq m k ≠ 0 := by omega
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  rw [hbb1, hstep]
  have h1 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      ≤ Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k) - 1) + 1 :=
    log_le_log_pred_succ (base k + 1) (by omega) _
  have h2 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      = bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := log_bump (base k) hb hv0
  have h3 : Nat.log (base k) (goodsteinSeq m k)
      ≤ bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := le_bump (base k) hb _
  omega

/-- **The leading exponent is non-decreasing while it is itself `≥ base`** (the level-2 analog of
`goodsteinSeq_ge_init`). If `L_k = log_{base k}(G_k) ≥ base k` then `bump (base k) L_k ≥ L_k + 1`
(`bump_gt`), so even after the `−1`-induced log drop, `L_{k+1} ≥ L_k`. The same non-decrease
mechanism that keeps the *value* high keeps the *leading exponent* high — one level up. -/
theorem leadExp_ge_of_base_le (m k : ℕ)
    (h : base k ≤ Nat.log (base k) (goodsteinSeq m k)) :
    Nat.log (base k) (goodsteinSeq m k) ≤ Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hv : goodsteinSeq m k ≠ 0 := by
    intro h0; rw [h0, Nat.log_zero_right] at h; omega
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  rw [hbb1, hstep]
  have h2 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      = bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := log_bump (base k) hb hv
  have hbg : Nat.log (base k) (goodsteinSeq m k) + 1
      ≤ bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := bump_gt (base k) hb h
  have h1 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      ≤ Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k) - 1) + 1 :=
    log_le_log_pred_succ (base k + 1) (by omega) _
  omega

/-- **The leading exponent is non-decreasing at every NON-pure-power step** — *unconditionally* (no
`≥ base` hypothesis, unlike `leadExp_ge_of_base_le`). If `G_k` is not a pure power of `base k`, then
`log_bump_pred_of_not_pow` preserves the leading exponent exactly (`L_{k+1} = bump (base k) L_k`) and
`le_bump` gives `L_k ≤ bump (base k) L_k = L_{k+1}`. So the leading exponent only ever *falls* at the
rare pure-power steps; everywhere else it stays or grows. This is the lemma that, once paired with a
bound on the number of pure-power events, lifts the `log₂ m`-step guarantee (`leadExp_ge_sub`, which
needs `L_k ≥ base k`) to the `m`-step guarantee the diagonal `f_o(m)` headline requires. -/
theorem leadExp_ge_of_not_pow (m k : ℕ)
    (hnp : base k ^ Nat.log (base k) (goodsteinSeq m k) < goodsteinSeq m k) :
    Nat.log (base k) (goodsteinSeq m k) ≤ Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hv0 : goodsteinSeq m k ≠ 0 := by
    have : 0 < base k ^ Nat.log (base k) (goodsteinSeq m k) := Nat.pow_pos (by omega)
    omega
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  rw [hbb1, hstep, log_bump_pred_of_not_pow (base k) hb hv0 hnp]
  exact le_bump (base k) hb _

/-- **The Goodstein term stays `≥ m` for the first `m` steps:** `m ≤ goodsteinSeq m k` whenever
`k + 1 ≤ m`. Induction on `k` using `bump_gt`: while `k + 2 ≤ m ≤ goodsteinSeq m k` the value is
above the base, so `goodsteinSeq m (k+1) = bump (k+2) (goodsteinSeq m k) − 1 ≥ goodsteinSeq m k`. -/
theorem goodsteinSeq_ge_init (m : ℕ) : ∀ k, k + 1 ≤ m → m ≤ goodsteinSeq m k := by
  intro k
  induction k with
  | zero => intro _; exact le_of_eq rfl
  | succ k ih =>
    intro hk
    have hv : m ≤ goodsteinSeq m k := ih (by omega)
    have hble : k + 2 ≤ goodsteinSeq m k := by omega
    have hgt : goodsteinSeq m k + 1 ≤ bump (k + 2) (goodsteinSeq m k) :=
      bump_gt (k + 2) (by omega) hble
    have hbase : base k = k + 2 := rfl
    show m ≤ bump (base k) (goodsteinSeq m k) - 1
    rw [hbase]; omega

/-- **The ordinal of a numeral dominates `ω` raised to its leading-exponent ordinal:**
`ω ^ (toOrdinal b (Nat.log b v)) ≤ toOrdinal b v` (for `v ≠ 0`, `b ≥ 2`). Immediate from
`toOrdinal_pos`: the leading Cantor term is `ω ^ (…) · c` with digit `c ≥ 1`. The bridge from the
**leading exponent** (a natural number, controlled by `leadExp_ge_sub`) to the **descent ordinal**
(`seqOrd`), needed to turn `leadExp ≥ k` into `seqOrd ≥ ω^k`. -/
theorem opow_toOrdinal_log_le (b : ℕ) (hb : 2 ≤ b) {v : ℕ} (hv : v ≠ 0) :
    ω ^ toOrdinal b (Nat.log b v) ≤ toOrdinal b v := by
  rw [toOrdinal_pos b v hv]
  have hc : (1 : Ordinal) ≤ (v / b ^ Nat.log b v : ℕ) := by
    have h0 : 0 < v / b ^ Nat.log b v :=
      Nat.div_pos (Nat.pow_log_le_self b hv) (Nat.pow_pos (by omega))
    exact_mod_cast h0
  calc ω ^ toOrdinal b (Nat.log b v)
      = ω ^ toOrdinal b (Nat.log b v) * 1 := (mul_one _).symm
    _ ≤ ω ^ toOrdinal b (Nat.log b v) * (v / b ^ Nat.log b v : ℕ) := by gcongr
    _ ≤ ω ^ toOrdinal b (Nat.log b v) * (v / b ^ Nat.log b v : ℕ)
          + toOrdinal b (v % b ^ Nat.log b v) := le_self_add

/-- **From leading exponent to descent ordinal:** if the leading exponent `leadExp_i =
Nat.log (base i)(G_i)` is `≥ k` (and `k < base i`, so `k` reads as the ordinal `k`), then the
descent ordinal dominates `ω^k`: `ω^k ≤ (seqONote m i).repr`. Chains `opow_toOrdinal_log_le` with
`toOrdinal`-monotonicity of the exponent and `toOrdinal b k = k` for `k < b`. The general bridge
behind sub-fact (ii) at level `o = k` — combine with `leadExp_ge_sub`. -/
theorem opow_le_seqONote_repr {m i k : ℕ} (hk : k ≤ Nat.log (base i) (goodsteinSeq m i))
    (hv : goodsteinSeq m i ≠ 0) (hkb : k < base i) :
    (ω : Ordinal) ^ (k : Ordinal) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  rw [repr_seqONote]
  show (ω : Ordinal) ^ (k : Ordinal) ≤ toOrdinal (base i) (goodsteinSeq m i)
  have htk : toOrdinal (base i) k = (k : Ordinal) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · have hlog0 : Nat.log (base i) k = 0 := Nat.log_eq_zero_iff.2 (Or.inl hkb)
      rw [toOrdinal_pos (base i) k (by omega), hlog0]
      simp [pow_zero, Nat.div_one, Nat.mod_one, toOrdinal_zero]
  have hmono : toOrdinal (base i) k
      ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) := by
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt ((toOrdinal_mono_and_bound (base i) hb _).1 k h)
  calc (ω : Ordinal) ^ (k : Ordinal) = ω ^ toOrdinal (base i) k := by rw [htk]
    _ ≤ ω ^ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
        opow_le_opow_right omega0_pos hmono
    _ ≤ toOrdinal (base i) (goodsteinSeq m i) := opow_toOrdinal_log_le (base i) hb hv

/-- **The descent ordinal stays `≥ ω` for the first `m` steps.** For `m = n + 2` and any step
`j ≤ n`, the term value is `≥ m ≥ base j = j + 2`, so its ordinal `seqOrd m j` is `≥ ω`. This is
sub-fact (ii) at level `o = 1`: the Goodstein notation `seqONote m j` dominates `ω = ω^(repr 1)`. -/
theorem omega_le_seqONote_repr {n j : ℕ} (hj : j ≤ n) :
    (ω : Ordinal) ≤ (seqONote (n + 2) j).repr := by
  have hmono_le : ∀ p q : ℕ, p ≤ q → toOrdinal (j + 2) p ≤ toOrdinal (j + 2) q := by
    intro p q hpq
    rcases eq_or_lt_of_le hpq with h | h
    · rw [h]
    · exact le_of_lt ((toOrdinal_mono_and_bound (j + 2) (by omega) q).1 p h)
  have h1 : toOrdinal (j + 2) 1 = 1 := by
    have h := toOrdinal_pow (j + 2) (by omega) 0; simpa using h
  have hbeq : toOrdinal (j + 2) (j + 2) = ω := by
    have h := toOrdinal_pow (j + 2) (by omega) 1
    rw [pow_one, h1, opow_one] at h; exact h
  have hval : j + 2 ≤ goodsteinSeq (n + 2) j := by
    have h := goodsteinSeq_ge_init (n + 2) j (by omega); omega
  rw [repr_seqONote]
  show (ω : Ordinal) ≤ toOrdinal (j + 2) (goodsteinSeq (n + 2) j)
  rw [← hbeq]; exact hmono_le (j + 2) _ hval

/-- **Telescoped leading-exponent lower bound:** `Nat.log 2 m ≤ leadExp_i + i` for `i + 1 ≤ m`,
i.e. `leadExp_i ≥ (log₂ m) − i`. The leading exponent starts at `log₂ m` and drops by `≤ 1` per
step (`leadExp_drop_le_one`, applicable since the value stays `≥` base over `[0, m)`). So the
descent ordinal keeps a leading exponent `≥ 2` — hence `seqOrd m i ≥ ω²` — for the first
`~log₂ m` steps. (The genuine `≫ m`-step persistence needs the steps-between-drops recursion.) -/
theorem leadExp_ge_sub (m : ℕ) : ∀ i, i + 1 ≤ m →
    Nat.log 2 m ≤ Nat.log (base i) (goodsteinSeq m i) + i := by
  intro i
  induction i with
  | zero => intro _; show Nat.log 2 m ≤ Nat.log 2 m + 0; omega
  | succ i ih =>
    intro hi
    have hib : base i ≤ goodsteinSeq m i := by
      have := goodsteinSeq_ge_init m i (by omega)
      simp only [base]; omega
    have hdrop := leadExp_drop_le_one m i hib
    have hih := ih (by omega)
    omega

/-- **The descent ordinal reaches `ω^k` for the first `~log₂ m` steps.** Combining the telescoped
leading-exponent bound `leadExp_ge_sub` (`leadExp_i ≥ log₂ m − i`) with the bridge
`opow_le_seqONote_repr`: whenever `k + i ≤ log₂ m` (and `k < i + 2`), the Goodstein descent ordinal
satisfies `ω^k ≤ (seqONote m i).repr`. Generalizes `omega_le_seqONote_repr` (the `k = 1` case) to
every fixed level `k` — the ordinal stays `≥ ω^k` for the first `log₂ m − k` steps. (Reaching `ω^k`
for `≥ m` steps — the full sub-fact (ii) at `o = k` — needs the steps-between-drops recursion.) -/
theorem omega_opow_le_seqONote_repr {m i k : ℕ} (hi : i + 1 ≤ m)
    (hk : k + i ≤ Nat.log 2 m) (hkb : k < i + 2) :
    (ω : Ordinal) ^ (k : Ordinal) ≤ (seqONote m i).repr := by
  have hle := leadExp_ge_sub m i hi
  have hkle : k ≤ Nat.log (base i) (goodsteinSeq m i) := by omega
  have hv : goodsteinSeq m i ≠ 0 := by
    have := goodsteinSeq_ge_init m i hi; omega
  have hkb' : k < base i := by simp only [base]; omega
  exact opow_le_seqONote_repr hkle hv hkb'

/-- The Goodstein value drops by **at most one** per step (`bump b v ≥ v`, so
`goodsteinSeq m (j+1) = bump _ v − 1 ≥ v − 1`). Telescoped: `goodsteinSeq m j ≤
goodsteinSeq m (j + i) + i` — the value `i` steps later is at least `(value now) − i`. -/
theorem goodsteinSeq_sub_le (m j : ℕ) : ∀ i, goodsteinSeq m j ≤ goodsteinSeq m (j + i) + i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hstep : goodsteinSeq m (j + i) ≤ goodsteinSeq m (j + i + 1) + 1 := by
      have h := le_bump (base (j + i)) (Nat.le_add_left 2 (j + i)) (goodsteinSeq m (j + i))
      show goodsteinSeq m (j + i) ≤ bump (base (j + i)) (goodsteinSeq m (j + i)) - 1 + 1
      omega
    have hassoc : j + (i + 1) = j + i + 1 := by ring
    rw [hassoc]; omega

/-- **Goodstein length is at least `2m − 1`** (improving the linear `≥ m`). The value stays `≥ m`
through step `m − 1` (`goodsteinSeq_ge_init`), and thereafter decreases by at most one per step
(`goodsteinSeq_sub_le`), so it stays positive through step `2m − 2`; its first zero is at `≥ 2m−1`.
A super-linear-constant lower bound; it also re-derives `f_1`-domination elementarily
(`2m ≤ (2m−1) + 2`). -/
theorem two_mul_sub_one_le_goodsteinLength (n : ℕ) :
    2 * n + 3 ≤ goodsteinLength (n + 2) := by
  rw [goodsteinLength, Nat.le_find_iff]
  intro k hk
  by_cases hkle : k ≤ n + 1
  · have h := goodsteinSeq_ge_init (n + 2) k (by omega)
    omega
  · have hinit : n + 2 ≤ goodsteinSeq (n + 2) (n + 1) :=
      goodsteinSeq_ge_init (n + 2) (n + 1) (by omega)
    have hsub := goodsteinSeq_sub_le (n + 2) (n + 1) (k - (n + 1))
    rw [Nat.add_sub_cancel' (by omega : n + 1 ≤ k)] at hsub
    omega

/-! ### The CNF norm of a Goodstein notation is bounded by its step index

A Goodstein notation `seqONote m j = toONote (j+2) (goodsteinSeq m j)` is, by construction, a
base-`(j+2)` hereditary numeral: *every* coefficient appearing anywhere in its Cantor normal
form (digits and recursively the exponents) is a base-`(j+2)` digit, hence `< j+2`. So its CNF
norm is `≤ j+1`. The structural consequence: **the Hardy budget `norm ≤ argument` is always met
at the telescope step `j+2`** — the budget obstruction is automatic on the descent itself, and
`hardy_le_of_lt` can be applied in either comparison direction at every telescope step. -/

/-- Every coefficient of `toONote b n` is a base-`b` digit, so its CNF norm is `< b`
(for `b ≥ 2`). Strong induction mirroring `toONote`'s peeling recursion: the leading digit
`n / b^(log b n) < b`, and the exponent `toONote b (log b n)` and tail `toONote b (n % …)`
recurse on strictly smaller arguments. -/
theorem norm_toONote_lt (b : ℕ) (hb : 2 ≤ b) : ∀ n, norm (toONote b n) < b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [toONote_zero, norm_zero]; omega
    · have hb1 : 1 < b := by omega
      have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      rw [toONote, dif_neg hn, norm_oadd]
      have hcoeff : ((n / b ^ Nat.log b n).toPNat' : ℕ) = n / b ^ Nat.log b n :=
        PNat.toPNat'_coe hc_pos
      rw [hcoeff]
      have h1 := ih _ hlog
      have h2 := ih _ hr_lt_n
      omega

/-- **The Goodstein descent always meets the Hardy budget.** `norm (seqONote m j) ≤ j + 1`,
hence `≤ j + 2 =` the telescope argument. So `hardy_le_of_lt` is applicable at every telescope
step `j+2` (against any notation the budget reaches), with no further budget hypothesis. -/
theorem norm_seqONote_le (m j : ℕ) : norm (seqONote m j) ≤ j + 1 := by
  have h := norm_toONote_lt (j + 2) (by omega) (goodsteinSeq m j)
  show norm (toONote (j + 2) (goodsteinSeq m j)) ≤ j + 1
  omega

/-! ### The domination headline, reduced to the single index sub-fact (ii)

The full chain of the growth headline — `fastGrowing o m ≤ goodsteinLength m + 2` — is here
assembled and machine-checked, modulo exactly one deep input: that after `m` Goodstein steps the
descent notation `seqONote m m` still exceeds `ω^o = oadd o 1 0` (sub-fact (ii), the
"ordinal-stays-high" / super-exponential term bound). Everything else is banked:

* the Cichoń telescope `hardy_seqONote_telescope` at `j = m` (valid by the linear length bound
  `le_goodsteinLength`, sub-fact (i)) plus `hardy_seqONote_zero`, giving
  `goodsteinLength m + 2 = H_{seqONote m m}(m+2)`;
* the **budget-valid** index step `hardy_le_of_lt` (the norm budget `m+2 ≥ norm (oadd o 1 0)` now
  holds — this is why we evaluate at the high-budget step `m+2`, not at the fixed argument `2`);
* the Hardy↔fast-growing bridge `fastGrowing_le_hardy_pow` at matching argument `m+2`;
* argument-monotonicity `fastGrowing_monotone` to descend `m+2 ↦ m`.

This isolates the remaining mathematical content to `hidx` alone. -/

/-- **Domination, reduced to the index sub-fact (ii).** Given that the Goodstein descent stays
above `ω^o` for at least `m` steps (`hidx : oadd o 1 0 < seqONote m m`) and the budget is met
(`norm o ≤ m`), the Goodstein length dominates the fast-growing level `o` at the diagonal:
`fastGrowing o m ≤ goodsteinLength m + 2`. The whole Cichoń assembly is machine-checked here;
the only open input is `hidx`. -/
theorem goodstein_dominates_of_index {o : ONote} (ho : o.NF) {m : ℕ}
    (hnorm : norm o ≤ m) (hidx : oadd o 1 0 < seqONote m m) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m m).NF := seqONote_NF m m
  have hbudget : norm (oadd o 1 0) ≤ m + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  -- index step at the high-budget argument `m+2`
  have hindex : hardy (oadd o 1 0) (m + 2) ≤ hardy (seqONote m m) (m + 2) :=
    hardy_le_of_lt hNFidx hNFseq hidx hbudget
  -- telescope: the Hardy value is invariant; at `j = m` it equals `goodsteinLength m + 2`
  have htel : hardy (seqONote m 0) 2 = hardy (seqONote m m) (m + 2) :=
    hardy_seqONote_telescope m m (le_goodsteinLength m)
  have hz : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := hardy_seqONote_zero m
  calc fastGrowing o m
      ≤ fastGrowing o (m + 2) := fastGrowing_monotone o (by omega)
    _ ≤ hardy (oadd o 1 0) (m + 2) := fastGrowing_le_hardy_pow o ho (m + 2)
    _ ≤ hardy (seqONote m m) (m + 2) := hindex
    _ = hardy (seqONote m 0) 2 := htel.symm
    _ = goodsteinLength m + 2 := hz

/-- **The domination dichotomy (fully proved, unconditional).** For every fixed level `o`
(with budget `norm o ≤ m`), at the diagonal `m` exactly one of two structural alternatives
holds:

* **(A)** Goodstein dominates: `fastGrowing o m ≤ goodsteinLength m + 2`; or
* **(B)** the length is Hardy-bounded: `goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m + 2)`.

The proof needs no index hypothesis: because `norm (seqONote m m) ≤ m + 1` (the budget is
automatic on the descent, `norm_seqONote_le`), `hardy_le_of_lt` applies in *whichever*
direction the trichotomy `seqONote m m` vs `oadd o 1 0` falls. The whole headline thus reduces
to **ruling out branch (B) for large `m`** — i.e. to the deep fact that the descent stays above
`ω^o` for at least `m` steps (sub-fact (ii)); branch (B) says the descent has already dropped
below `ω^o` by step `m`, which is conjecturally impossible for large `m` but is exactly the
Cichoń lower-bound content not yet formalized. -/
theorem goodstein_dominates_or_hardy_bound {o : ONote} (ho : o.NF) {m : ℕ}
    (hnorm : norm o ≤ m) :
    fastGrowing o m ≤ goodsteinLength m + 2 ∨
      goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m + 2) := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m m).NF := seqONote_NF m m
  have hval : hardy (seqONote m m) (m + 2) = goodsteinLength m + 2 := by
    rw [← hardy_seqONote_telescope m m (le_goodsteinLength m), hardy_seqONote_zero]
  have hbseq : norm (seqONote m m) ≤ m + 2 := le_trans (norm_seqONote_le m m) (by omega)
  rcases lt_trichotomy (seqONote m m).repr (oadd o 1 0).repr with hlt | heq | hgt
  · -- descent already below `ω^o` at step `m` (strict): branch (B)
    right
    have hcmp : seqONote m m < oadd o 1 0 := lt_def.2 hlt
    have h := hardy_le_of_lt hNFseq hNFidx hcmp hbseq
    rwa [hval] at h
  · -- descent exactly at `ω^o`: branch (B), via equality
    right
    have heqo : seqONote m m = oadd o 1 0 := (@repr_inj (seqONote m m) (oadd o 1 0) hNFseq hNFidx).1 heq
    exact le_of_eq (by rw [← hval, heqo])
  · -- descent still above `ω^o`: branch (A), via the reduction lemma
    left
    exact goodstein_dominates_of_index ho hnorm (lt_def.2 hgt)

/-- **Domination, generalized reduction (any telescope step, `≤` index).** If at some step `j`
the budget reaches the diagonal (`m ≤ j + 2`, `norm o ≤ j + 2`) and the descent notation is at
least `ω^o` (`(oadd o 1 0).repr ≤ (seqONote m j).repr`, allowing equality), then `goodsteinLength`
dominates `fastGrowing o` at `m`. Generalizes `goodstein_dominates_of_index`: the telescope step is
free (any `j ≤ goodsteinLength m`), and the index hypothesis is non-strict — the equality case
`oadd o 1 0 = seqONote m j` collapses the Hardy comparison to a literal `rfl`, while the strict
case uses `hardy_le_of_lt` (budget met). This is what lets the `o = 1` level close from the
non-strict ordinal bound `omega_le_seqONote_repr`. -/
theorem goodstein_dominates_of_index_le {o : ONote} (ho : o.NF) {m j : ℕ}
    (hj : j ≤ goodsteinLength m) (hmj : m ≤ j + 2) (hnorm : norm o ≤ j + 2)
    (hidx : (oadd o 1 0).repr ≤ (seqONote m j).repr) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m j).NF := seqONote_NF m j
  have hbudget : norm (oadd o 1 0) ≤ j + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  have hindex : hardy (oadd o 1 0) (j + 2) ≤ hardy (seqONote m j) (j + 2) := by
    rcases eq_or_lt_of_le hidx with heq | hlt
    · have heqo : oadd o 1 0 = seqONote m j :=
        (@repr_inj (oadd o 1 0) (seqONote m j) hNFidx hNFseq).1 heq
      rw [heqo]
    · exact hardy_le_of_lt hNFidx hNFseq (lt_def.2 hlt) hbudget
  have htel : hardy (seqONote m 0) 2 = hardy (seqONote m j) (j + 2) :=
    hardy_seqONote_telescope m j hj
  have hz : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := hardy_seqONote_zero m
  calc fastGrowing o m
      ≤ fastGrowing o (j + 2) := fastGrowing_monotone o hmj
    _ ≤ hardy (oadd o 1 0) (j + 2) := fastGrowing_le_hardy_pow o ho (j + 2)
    _ ≤ hardy (seqONote m j) (j + 2) := hindex
    _ = hardy (seqONote m 0) 2 := htel.symm
    _ = goodsteinLength m + 2 := hz

/-- **Goodstein length dominates `f_1`, unconditionally (every `m ≥ 2`).** This is the first
member of the fast-growing hierarchy proven dominated by `goodsteinLength` through the full
Cichoń pipeline — *not* by `native_decide`. The deep input, sub-fact (ii) at `o = 1`, is supplied
by `omega_le_seqONote_repr`: at step `j = m − 2` the descent ordinal is still `≥ ω`, so the
generalized reduction `goodstein_dominates_of_index_le` (budget `j + 2 = m`) applies. Concretely
`f_1(m) = 2m ≤ goodsteinLength m + 2`. -/
theorem fastGrowing_one_le_goodsteinLength (n : ℕ) :
    fastGrowing 1 (n + 2) ≤ goodsteinLength (n + 2) + 2 := by
  have ho : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  have hlhs : (oadd (1 : ONote) 1 0).repr = ω := by simp [ONote.repr]
  refine goodstein_dominates_of_index_le (o := 1) (m := n + 2) (j := n) ho ?_ ?_ ?_ ?_
  · have := le_goodsteinLength (n + 2); omega
  · omega
  · have hn1 : norm (1 : ONote) = 1 := by decide
    omega
  · rw [hlhs]; exact omega_le_seqONote_repr (le_refl n)

/-- **Non-diagonal reduction (length lower bound).** Like `goodstein_dominates_of_index_le` but
without the budget constraint `m ≤ j + 2` — it concludes about `fastGrowing o (j + 2)` (the step's
own budget) instead of `fastGrowing o m`. Whenever the descent at step `j` is `≥ ω^o`, the Goodstein
length is bounded below by `f_o(j+2)`. This is what converts the early-step ordinal bounds (where
`j ≈ log₂ m ≪ m`) into a **super-linear lower bound on `goodsteinLength`** (it cannot reach the
diagonal `f_o(m)`, but it does beat every polynomial). -/
theorem fastGrowing_step_le_goodsteinLength {o : ONote} (ho : o.NF) {m j : ℕ}
    (hj : j ≤ goodsteinLength m) (hnorm : norm o ≤ j + 2)
    (hidx : (oadd o 1 0).repr ≤ (seqONote m j).repr) :
    fastGrowing o (j + 2) ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m j).NF := seqONote_NF m j
  have hbudget : norm (oadd o 1 0) ≤ j + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  have hindex : hardy (oadd o 1 0) (j + 2) ≤ hardy (seqONote m j) (j + 2) := by
    rcases eq_or_lt_of_le hidx with heq | hlt
    · have heqo : oadd o 1 0 = seqONote m j :=
        (@repr_inj (oadd o 1 0) (seqONote m j) hNFidx hNFseq).1 heq
      rw [heqo]
    · exact hardy_le_of_lt hNFidx hNFseq (lt_def.2 hlt) hbudget
  calc fastGrowing o (j + 2)
      ≤ hardy (oadd o 1 0) (j + 2) := fastGrowing_le_hardy_pow o ho (j + 2)
    _ ≤ hardy (seqONote m j) (j + 2) := hindex
    _ = hardy (seqONote m 0) 2 := (hardy_seqONote_telescope m j hj).symm
    _ = goodsteinLength m + 2 := hardy_seqONote_zero m

/-- **`goodsteinLength` is SUPER-LINEAR:** `fastGrowing 2 (Nat.log 2 m) ≤ goodsteinLength m + 2`
(for `Nat.log 2 m ≥ 3`, i.e. `m ≥ 8`). Since `fastGrowing 2 n = 2^n · n`, this reads
`goodsteinLength m ≳ 2^{log₂ m} · log₂ m = m · log₂ m` — a genuine super-linear (beats every linear)
lower bound, the first proof that `goodsteinLength` outgrows the polynomial regime. Assembly: at
the early step `j = log₂ m − 2` the descent ordinal is `≥ ω² = (oadd 2 1 0).repr`
(`omega_opow_le_seqONote_repr`, leading exponent still `≥ 2`); feed the non-diagonal reduction. The
budget here is only `log₂ m`, not `m` — closing the gap to `f_2(m)` needs the deeper recursion. -/
theorem fastGrowing_two_log_le_goodsteinLength {m : ℕ} (hm : 3 ≤ Nat.log 2 m) :
    fastGrowing 2 (Nat.log 2 m) ≤ goodsteinLength m + 2 := by
  set L := Nat.log 2 m with hL
  have hLm : L ≤ m := Nat.log_le_self 2 m
  have hglen : m ≤ goodsteinLength m := le_goodsteinLength m
  have ho : (2 : ONote).NF := by decide
  have hr2 : (oadd (2 : ONote) 1 0).repr = ω ^ (2 : Ordinal) := by
    rw [show (2 : ONote) = oadd 0 2 0 from rfl]; simp [ONote.repr]
  have hidx : (oadd (2 : ONote) 1 0).repr ≤ (seqONote m (L - 2)).repr := by
    rw [hr2]
    exact omega_opow_le_seqONote_repr (m := m) (i := L - 2) (k := 2)
      (by omega) (by omega) (by omega)
  have hnorm : norm (2 : ONote) ≤ (L - 2) + 2 := by
    have : norm (2 : ONote) = 2 := by decide
    omega
  have h := fastGrowing_step_le_goodsteinLength ho (m := m) (j := L - 2)
    (by omega) hnorm hidx
  rwa [show L - 2 + 2 = L from by omega] at h

/-- `norm (ofNat n) = n`: a finite notation `ofNat (k+1) = oadd 0 ⟨k+1⟩ 0` has CNF norm its single
coefficient. -/
theorem norm_ofNat (n : ℕ) : norm (ONote.ofNat n) = n := by
  cases n with
  | zero => rfl
  | succ k => rw [ONote.ofNat_succ, norm_oadd, norm_zero]; simp

/-- **`goodsteinLength` is NON-ELEMENTARY:** for every finite level `n`,
`fastGrowing (ofNat n) (log₂ m − n + 2) ≤ goodsteinLength m + 2` (for `1 ≤ m`, `2n ≤ log₂ m`).
Generalizes `fastGrowing_two_log_le_goodsteinLength` to all `n`: at the early step `i = log₂ m − n`
the leading exponent is still `≥ n` (`leadExp_ge_sub`), so the descent ordinal is `≥ ω^n =
(oadd (ofNat n) 1 0).repr` (`omega_opow_le_seqONote_repr`); feed the non-diagonal reduction. The
budget is `log₂ m − n` (not `m` — leadExp and budget trade off). Taking e.g. `n = log₂ m / 2` makes
the RHS exceed `f_{(log₂ m)/2}(…)` — a tower of exponentials of height `~log₂ m`, hence
`goodsteinLength` outgrows every elementary function. The diagonal `f_n(m)` (true domination, the
headline) still needs the steps-between-drops recursion. -/
theorem fastGrowing_ofNat_log_le_goodsteinLength (n : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (hn : 2 * n ≤ Nat.log 2 m) :
    fastGrowing (ONote.ofNat n) (Nat.log 2 m - n + 2) ≤ goodsteinLength m + 2 := by
  set L := Nat.log 2 m with hL
  have hLlt : L < m := Nat.log_lt_self 2 (by omega)
  have hglen : m ≤ goodsteinLength m := le_goodsteinLength m
  have ho : (ONote.ofNat n).NF := inferInstance
  have hrepr : (ONote.ofNat n).repr = (n : Ordinal) := ONote.repr_ofNat n
  have hidx : (oadd (ONote.ofNat n) 1 0).repr ≤ (seqONote m (L - n)).repr := by
    have hr : (oadd (ONote.ofNat n) 1 0).repr = ω ^ (n : Ordinal) := by
      simp [ONote.repr, hrepr]
    rw [hr]
    exact omega_opow_le_seqONote_repr (m := m) (i := L - n) (k := n)
      (by omega) (by omega) (by omega)
  have hnorm : norm (ONote.ofNat n) ≤ (L - n) + 2 := by rw [norm_ofNat]; omega
  exact fastGrowing_step_le_goodsteinLength ho (m := m) (j := L - n) (by omega) hnorm hidx

/-! ### Anti-vacuity anchors (off any headline axiom path). -/

example : hardy (oadd 1 2 (oadd 0 3 0)) 4 = hardy (oadd 1 2 0) (hardy (oadd 0 3 0) 4) := by
  native_decide
example : hardy (oadd 1 3 0) 3 = (hardy (oadd 1 1 0))^[3] 3 := by native_decide
example : fastGrowing 2 3 ≤ hardy (oadd 2 1 0) 3 := by native_decide

-- The domination inequality `fastGrowing o m ≤ goodsteinLength m + 2` holds concretely in the
-- computable regime (small `o`, where it already kicks in at small `m`). A *backwards* or
-- vacuous headline would fail these. (For `o ≥ 2` the inequality is asymptotic — it first holds
-- at `m = 4`, where `goodsteinLength` is already astronomically large and beyond `native_decide`.)
-- The growth engine, witnessed: one bump strictly grows a value above its base
-- (`bump_gt`: `4 + 1 ≤ bump 2 4 = 27`), and the term stays `≥ m` (`goodsteinSeq_ge_init`:
-- `G(4,2) = 41 ≥ 4`). A vacuous/backwards recursion would fail these.
example : 4 + 1 ≤ bump 2 4 := by native_decide
example : 4 ≤ goodsteinSeq 4 2 := by native_decide
-- `log_bump`: the leading exponent bumps itself. `bump 2 5 = 28`, `log_3 28 = 3 = bump 2 (log_2 5)`.
example : Nat.log 3 (bump 2 5) = bump 2 (Nat.log 2 5) := by native_decide
-- `log_le_log_pred_succ`: one decrement lowers a log by ≤ 1 (`log_3 9 = 2`, `log_3 8 = 1`).
example : Nat.log 3 9 ≤ Nat.log 3 8 + 1 := by native_decide
-- `leadExp_drop_le_one`: leading exponent drops by ≤ 1 per step. `G(4,2)=41` (`log_4 41 = 2`),
-- `G(4,3)=60` (`log_5 60 = 2`): `2 ≤ 2 + 1`.
example : Nat.log (base 2) (goodsteinSeq 4 2) ≤ Nat.log (base 3) (goodsteinSeq 4 3) + 1 := by
  native_decide
-- `log_bump_pred_of_not_pow`: NO drop at a non-pure-power step. `n=5` (`2²=4 < 5`, not a pure
-- power): `bump 2 5 = 28`, `28−1 = 27`, `log_3 27 = 3 = bump 2 (log_2 5) = bump 2 2 = 3`. No drop.
example : Nat.log 3 (bump 2 5 - 1) = bump 2 (Nat.log 2 5) := by native_decide
-- the hypothesis is LOAD-BEARING: at a pure power `n=4=2²` the leading exponent DOES drop.
-- `bump 2 4 = 27`, `27−1 = 26`, `log_3 26 = 2 ≠ 3 = bump 2 (log_2 4)` — a genuine "borrow".
example : Nat.log 3 (bump 2 4 - 1) ≠ bump 2 (Nat.log 2 4) := by native_decide
-- `log_bump_pred_of_pow`: at the pure power `n=4` the drop is by EXACTLY one:
-- `log_3 26 = 2 = bump 2 (log_2 4) − 1 = 3 − 1 = 2`.
example : Nat.log 3 (bump 2 4 - 1) = bump 2 (Nat.log 2 4) - 1 := by native_decide

-- the super-linear bound's interpretation, witnessed: `f_2(n) = 2^n·n` (`fastGrowing_two`), and the
-- step index `Nat.log 2 8 = 3` ⟹ the bound reads `f_2(3) = 24 ≤ goodsteinLength 8 + 2` (RHS huge).
example : fastGrowing 2 3 = 2 ^ 3 * 3 := by native_decide  -- = 24
example : Nat.log 2 8 = 3 := by native_decide

example : fastGrowing 0 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 3 ≤ 5
example : fastGrowing 1 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 4 ≤ 5
example : fastGrowing 0 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 4 ≤ 7
example : fastGrowing 1 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 6 ≤ 7

end LeanFormalizations.Logic.Goodstein
