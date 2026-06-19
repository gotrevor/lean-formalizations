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

/-! ### Anti-vacuity anchors (off any headline axiom path). -/

example : hardy (oadd 1 2 (oadd 0 3 0)) 4 = hardy (oadd 1 2 0) (hardy (oadd 0 3 0) 4) := by
  native_decide
example : hardy (oadd 1 3 0) 3 = (hardy (oadd 1 1 0))^[3] 3 := by native_decide
example : fastGrowing 2 3 ≤ hardy (oadd 2 1 0) 3 := by native_decide

end LeanFormalizations.Logic.Goodstein
