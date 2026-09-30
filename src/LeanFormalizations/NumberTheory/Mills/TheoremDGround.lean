/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.CoveringEngine

/-!
# Phase 44: groundwork for Theorems D and E (Lemmas 2–4 of `PROOF-THEOREM-D.md`)

The Lean-sized pieces of the Saito-1.7 partial answer (Theorem D) and of the transcendence of
`ξ(3^k + s)` (Theorem E/E+).  Everything here is elementary; the Galois-rigidity step is **not**
in this phase.

## Route
1. `not_stuck_twice` (Lemma 3, pure combinatorics): if `n` is stuck for period `j n` (`ε` flips at
   every `n + k·j n`, `k ≥ 1`) then `n + j n` is not stuck for period `j (n + j n)`.  Proof: take
   `k = j n` at `n′ = n + j n` and `k = 1 + j n′` at `n`.
2. `dvd_trace_sub_of_ord_dvd` (Lemma 2, abstract exponents): if `p` is prime, `p ∤ det C`, and
   `orderOf` of `C` in `GL_d(ZMod p)` divides `a − b` (with `b ≤ a`), then
   `p ∣ tr C^a − tr C^b`.  Reuse the `ZMod p` reduction in
   `SharedConjecture.exists_trace_pow_congr`.
3. `exists_pow_sub_one_of_lt_padicValNat_glCard` (Lemma 4): if `p ≠ c` are primes and
   `n < padicValNat c (glCard d p)`, then there is `1 ≤ i ≤ d` with
   `c ^ (n / d) ∣ p ^ i − 1`.  (`glCard d p = ∏ (p^d − p^i) = p^(…) ∏_(i=1..d) (p^i − 1)`; pigeonhole
   on the `c`-adic valuations.)

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.TheoremDGround

open LeanFormalizations.Mills.ThreeAdic Matrix

/-! ### Lemma 3: stuck indices are isolated -/

/-- **Lemma 3 (stuck indices are isolated).**  `ε` takes two values (`Bool`). -/
theorem not_stuck_twice (ε : ℕ → Bool) (j : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n) (n : ℕ)
    (hstuck : ∀ k, 1 ≤ k → ε (n + k * j n) ≠ ε n) :
    ¬ ∀ k, 1 ≤ k → ε (n + j n + k * j (n + j n)) ≠ ε (n + j n) := by
  intro hstuck'
  -- the common index: `n + j n + (j n) * j (n + j n)`
  have h1 : ε (n + 1 * j n) ≠ ε n := hstuck 1 le_rfl
  have hne : ε (n + j n) ≠ ε n := by simpa using h1
  -- from the `n'`-side, with `k = j n`
  have h2 := hstuck' (j n) (hj n)
  -- from the `n`-side, with `k = 1 + j (n + j n)`
  have h3 := hstuck (1 + j (n + j n)) (by omega)
  have hidx : n + (1 + j (n + j n)) * j n = n + j n + j n * j (n + j n) := by ring
  rw [hidx] at h3
  -- `Bool` has two elements
  revert h2 h3 hne
  cases ε (n + j n + j n * j (n + j n)) <;> cases ε (n + j n) <;> cases ε n <;> simp

/-! ### Lemma 2: abstract exponents -/

/-- **Lemma 2 (abstract exponents).** -/
theorem dvd_trace_sub_of_orderOf_dvd {d : ℕ} (C : Matrix (Fin d) (Fin d) ℤ) {p : ℕ}
    (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ C.det) {a b : ℕ} (hba : b ≤ a)
    (hord : ∀ D : GL (Fin d) (ZMod p), (D : Matrix (Fin d) (Fin d) (ZMod p)) =
      (Int.castRingHom (ZMod p)).mapMatrix C → orderOf D ∣ a - b) :
    (p : ℤ) ∣ (C ^ a).trace - (C ^ b).trace := by
  haveI : Fact p.Prime := ⟨hp⟩
  set f : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hf
  set D : Matrix (Fin d) (Fin d) (ZMod p) := f.mapMatrix C with hD
  have htr : ∀ N : ℕ, ((C ^ N).trace : ZMod p) = (D ^ N).trace := by
    intro N
    rw [hD, ← map_pow]
    simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply, Matrix.map_apply, hf]
  have hdetD : IsUnit D.det := by
    have hmd : D.det = f C.det := by rw [hD]; exact (RingHom.map_det f C).symm
    rw [hmd]
    refine Ne.isUnit ?_
    simpa [hf, ZMod.intCast_zmod_eq_zero_iff_dvd] using hdet
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det D).2 hdetD
  have hord' : orderOf u ∣ a - b := hord u hu
  have hu1 : u ^ (a - b) = 1 := orderOf_dvd_iff_pow_eq_one.1 hord'
  have hDeq : D ^ a = D ^ b := by
    have hab : a = b + (a - b) := by omega
    have : u ^ a = u ^ b := by rw [hab, pow_add, hu1, mul_one]
    have h2 := congrArg (fun v : GL (Fin d) (ZMod p) =>
      (v : Matrix (Fin d) (Fin d) (ZMod p))) this
    simpa [hu] using h2
  have hz : (((C ^ a).trace - (C ^ b).trace : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [htr, htr, hDeq]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz

/-! ### Lemma 4: the `GL_d` window -/

/-- The `i`-th factor of `glCard d p`, split off its `p`-power part. -/
lemma glCard_factor_eq {p d : ℕ} (hp : 2 ≤ p) {i : ℕ} (hi : i < d) :
    p ^ d - p ^ i = p ^ i * (p ^ (d - i) - 1) := by
  obtain ⟨s, hs⟩ : ∃ s, p ^ (d - i) = s + 1 :=
    ⟨p ^ (d - i) - 1, by have := Nat.one_le_pow (d - i) p (by omega); omega⟩
  have hpow : p ^ d = p ^ i * (s + 1) := by
    rw [← hs, ← pow_add]; congr 1; omega
  have hr : p ^ i * (s + 1) = p ^ i * s + p ^ i := by ring
  have hs' : p ^ (d - i) - 1 = s := by omega
  rw [hs', hpow, hr, Nat.add_sub_cancel]

/-- The `c`-adic valuation of `|GL_d(𝔽_p)|` is `∑_(i<d) v_c(p^(d−i) − 1)` for `p ≠ c` prime. -/
lemma padicValNat_glCard_eq_sum {c p d : ℕ} (hc : c.Prime) (hp : p.Prime) (hpc : p ≠ c) :
    padicValNat c (glCard d p) = ∑ i : Fin d, (p ^ (d - (i : ℕ)) - 1).factorization c := by
  have hp2 : 2 ≤ p := hp.two_le
  have hfp : p.factorization c = 0 := by
    rw [hp.factorization]; simp [hpc]
  have hne : ∀ i : Fin d, p ^ d - p ^ (i : ℕ) ≠ 0 := by
    intro i
    have h1 : p ^ (i : ℕ) < p ^ d := Nat.pow_lt_pow_right (by omega) i.isLt
    omega
  have hnz : glCard d p ≠ 0 := by
    rw [glCard]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hne i
  rw [← Nat.factorization_def _ hc, glCard,
    Nat.factorization_prod (fun i _ => hne i)]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : p ^ (d - (i : ℕ)) - 1 ≠ 0 := by
    have h1 : 1 < p ^ (d - (i : ℕ)) := by
      have : 0 < d - (i : ℕ) := by have := i.isLt; omega
      exact Nat.one_lt_pow (by omega) (by omega)
    omega
  rw [glCard_factor_eq hp2 i.isLt,
    Nat.factorization_mul (by positivity) hsub]
  simp [Nat.factorization_pow, hfp]

/-- **Lemma 4 (the window).** -/
theorem exists_pow_sub_one_of_lt_padicValNat_glCard {c p d n : ℕ} (hc : c.Prime) (hp : p.Prime)
    (hpc : p ≠ c) (hd : 1 ≤ d) (hn : n < padicValNat c (glCard d p)) :
    ∃ i, 1 ≤ i ∧ i ≤ d ∧ (c : ℤ) ^ (n / d) ∣ (p : ℤ) ^ i - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [padicValNat_glCard_eq_sum hc hp hpc] at hn
  -- pigeonhole: some term exceeds `n / d`
  have hex : ∃ i : Fin d, n / d < (p ^ (d - (i : ℕ)) - 1).factorization c := by
    by_contra hcon
    push_neg at hcon
    have hsum : ∑ i : Fin d, (p ^ (d - (i : ℕ)) - 1).factorization c ≤ n / d * d := by
      calc ∑ i : Fin d, (p ^ (d - (i : ℕ)) - 1).factorization c
          ≤ ∑ _i : Fin d, (n / d) := Finset.sum_le_sum fun i _ => hcon i
        _ = n / d * d := by simp [Finset.card_univ, mul_comm]
    have hle : n / d * d ≤ n := Nat.div_mul_le_self n d
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨d - (i : ℕ), ?_, ?_, ?_⟩
  · have := i.isLt; omega
  · omega
  · have hsub : p ^ (d - (i : ℕ)) - 1 ≠ 0 := by
      have h1 : 1 < p ^ (d - (i : ℕ)) := by
        have : 0 < d - (i : ℕ) := by have := i.isLt; omega
        exact Nat.one_lt_pow (by omega) (by omega)
      omega
    have hdvd : c ^ (n / d) ∣ p ^ (d - (i : ℕ)) - 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc hsub).2 (by omega)
    have h1 : 1 ≤ p ^ (d - (i : ℕ)) := Nat.one_le_pow _ _ (by omega)
    have hcast : ((p ^ (d - (i : ℕ)) - 1 : ℕ) : ℤ) = (p : ℤ) ^ (d - (i : ℕ)) - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [← hcast]
    exact_mod_cast Int.natCast_dvd_natCast.2 hdvd

end LeanFormalizations.Mills.TheoremDGround
