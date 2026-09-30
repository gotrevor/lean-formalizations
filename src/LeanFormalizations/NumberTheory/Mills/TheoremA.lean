/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.OrbitSum
import LeanFormalizations.NumberTheory.Mills.SaitoFibonacci
import LeanFormalizations.NumberTheory.Mills.TheoremDGround

/-!
# Phase 52: Theorem A: order-`d` recurrences at inert primes; Tribonacci `T(3^n) + h`

**Theorem A.**  Let `A ∈ M_d(ℤ)` with `χ_A` irreducible mod the prime `c`, `d` odd, and suppose
`μ_(≤d)(ℤ_c) = {±1}` (`c = 2`, or no `k ∈ [3, d]` divides `c − 1`).  Let `u(N) = (A^N)_(ij)` with
`i ≠ j`, growing in absolute value along `c^n`, and suppose `c ∤ u(c^r)` for **some** `r < d`.  Then
`u(c^n) + h` is composite (not prime in `ℤ`) for infinitely many `n`, for **every** `h ∈ ℤ`.

Corollary: **`T(3^n) + h` and `T(5^n) + h` are composite i.o. for every `h`** (Tribonacci,
`T 0 = T 1 = 0`, `T 2 = 1`).  `X³ − X² − X − 1` is irreducible mod 3 and mod 5, and
`T 3 = 1`, `T 5 = 4`.  (Also mod 23, not stated.)

## Route (phase 32's survivor argument, order `d`)
Assume `p_n := u(c^n) + h` is prime for all `n ≥ n₀`.
1. **Filter** (`SaitoFibonacci.exists_entry_pow_congr` / `TheoremDGround`): for large `n`, either
   `p_n` divides some later `p_m` (`m > n`), which is impossible once `|u|` grows (`p_m` prime and
   `|p_m| > |p_n|`), or `p_n^i ≡ 1 (mod c^(e_n))` for some `1 ≤ i ≤ d`, with `e_n → ∞`
   (`TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard`, `e_n ≈ n/d − v_c(d!) − 1`).
2. **Window:** with `μ_(≤d)(ℤ_c) = {±1}`, `p_n^i ≡ 1 (mod c^e)` with `i ≤ d` forces
   `p_n ≡ ±1 (mod c^(e − O(1)))`.  (`c` odd: the order of `p_n` mod `c` divides `gcd(i, c − 1)`,
   which is `1` or `2`; lift by the `ℤ/c^e` cyclic structure, or `pow_sub_one`-factor
   `p^i − 1 = (p − 1)(…)`/`(p² − 1)(…)` and count valuations.  `c = 2`: `p` odd, `p ≡ ±1 mod 4`
   plus LTE.)
3. **Orbit sum** (phase 51, `OrbitSum.orbit_sum_entry_congr`): `Σ_(k<d) u(c^(n+k)) ≡ 0 (mod c^(n+1))`.
   With `s_k := p_(n+k) ∈ {±1} + c^e ℤ`, get `Σ_(k<d) s_k ≡ d·h (mod c^(min(e, n+1)))`.  For `n` large
   both sides are small integers (`|Σ ±1| ≤ d`, `h` fixed), so `Σ_(k<d) ε_k = d·h` exactly with
   `ε_k ∈ {±1}`.  `d` is odd, so `|d·h| ≤ d` forces `h = ±1` and every `ε_k = h`.
4. Then `u(c^(n+k)) ≡ 0 (mod c^e)` for every `k < d`.  But by the period (phase 51,
   `OrbitSum.pow_prime_pow_add_card_congr`), `u(c^m) ≡ u(c^(m mod d)) (mod c)`, and the residues
   `n, …, n+d−1` cover `r`: contradiction with `c ∤ u(c^r)`.

Frozen: the three statements below and the def `trib`; all earlier statements; `Literature/`.
No `private`.  Helpers public; add as many as needed.
-/

namespace LeanFormalizations.Mills.TheoremA

open Matrix Filter

/-! ### Step 2: the window — `p^i ≡ 1 (mod c^e)` with `i ≤ d` forces `p ≡ ±1` -/

/-- If `c ∤ m` and `c ∣ z − 1`, then `c^e ∣ z^m − 1` already forces `c^e ∣ z − 1`:
the geometric factor `1 + z + ⋯ + z^(m−1) ≡ m` is a unit mod `c`. -/
theorem dvd_sub_one_of_coprime_exp {c : ℕ} (hc : c.Prime) {z : ℤ} {m e : ℕ}
    (hm : ¬ c ∣ m) (h1 : (c : ℤ) ∣ z - 1) (h : (c : ℤ) ^ e ∣ z ^ m - 1) :
    (c : ℤ) ^ e ∣ z - 1 := by
  have hcp : Prime (c : ℤ) := Nat.prime_iff_prime_int.1 hc
  have hz : ¬ (c : ℤ) ∣ z := by
    intro hd
    have h1' : (c : ℤ) ∣ 1 := by simpa using dvd_sub hd h1
    have hle := Int.le_of_dvd one_pos h1'
    have := hc.two_le
    have : (2 : ℤ) ≤ (c : ℤ) := by exact_mod_cast this
    omega
  have hmi : ¬ (c : ℤ) ∣ ((m : ℕ) : ℤ) := by
    intro hd
    exact hm (Int.ofNat_dvd.1 (by exact_mod_cast hd))
  have hgs : ¬ (c : ℤ) ∣ ∑ i ∈ Finset.range m, z ^ i * (1 : ℤ) ^ (m - 1 - i) :=
    not_dvd_geom_sum₂ hcp (by simpa using h1) hz hmi
  have hid : (∑ i ∈ Finset.range m, z ^ i * (1 : ℤ) ^ (m - 1 - i)) * (z - 1) = z ^ m - 1 := by
    simpa using geom_sum₂_mul z (1 : ℤ) m
  rw [← hid] at h
  exact hcp.pow_dvd_of_dvd_mul_left e hgs h

/-- `c ∣ z^(c^a) − 1 → c ∣ z − 1` (iterated Frobenius). -/
theorem dvd_sub_one_of_dvd_pow_pow {c : ℕ} (hc : c.Prime) {z : ℤ} {a : ℕ}
    (h : (c : ℤ) ∣ z ^ (c ^ a) - 1) : (c : ℤ) ∣ z - 1 := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hz : ((z : ZMod c)) ^ (c ^ a) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (z ^ (c ^ a) - 1) c).2 h
    push_cast at this
    linear_combination this
  have hfrob : ∀ k : ℕ, ((z : ZMod c)) ^ (c ^ k) = (z : ZMod c) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  rw [hfrob a] at hz
  have : ((z - 1 : ℤ) : ZMod c) = 0 := by push_cast; rw [hz]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this

/-- **LTE descent at an odd prime:** `c^(f+a) ∣ z^(c^a) − 1` forces `c^f ∣ z − 1`. -/
theorem dvd_sub_one_of_pow_pow_odd {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {z : ℤ} {f a : ℕ}
    (h : (c : ℤ) ^ (f + a) ∣ z ^ (c ^ a) - 1) : (c : ℤ) ^ f ∣ z - 1 := by
  rcases Nat.eq_zero_or_pos (f + a) with h0 | hpos
  · have : f = 0 := by omega
    simp [this]
  have hcp : Prime (c : ℤ) := Nat.prime_iff_prime_int.1 hc
  have h1 : (c : ℤ) ∣ z ^ (c ^ a) - 1 :=
    dvd_trans (dvd_pow_self _ (by omega)) h
  have hzz : (c : ℤ) ∣ z - 1 := dvd_sub_one_of_dvd_pow_pow hc h1
  have hx : ¬ (c : ℤ) ∣ z := by
    intro hd
    have h1' : (c : ℤ) ∣ 1 := by simpa using dvd_sub hd hzz
    have hle := Int.le_of_dvd one_pos h1'
    have h2 := hc.two_le
    have : (2 : ℤ) ≤ (c : ℤ) := by exact_mod_cast h2
    omega
  have hodd : Odd c := hc.odd_of_ne_two hc2
  have hkey := emultiplicity_pow_prime_pow_sub_pow_prime_pow (R := ℤ) (p := c) (x := z) (y := 1)
    hcp hodd (by simpa using hzz) hx a
  simp only [one_pow] at hkey
  have hle : ((f + a : ℕ) : ℕ∞) ≤ emultiplicity (c : ℤ) (z ^ (c ^ a) - 1) :=
    le_emultiplicity_of_pow_dvd h
  rw [hkey] at hle
  push_cast at hle
  have hfin : ((a : ℕ) : ℕ∞) ≠ ⊤ := by simp
  have hle' : ((f : ℕ∞)) ≤ emultiplicity (c : ℤ) (z - 1) :=
    (WithTop.add_le_add_iff_right hfin).1 hle
  exact pow_dvd_of_le_emultiplicity hle'

/-- One squaring descent at `2`: `2^(f+1) ∣ z² − 1` forces `2^f ∣ z ∓ 1`. -/
theorem two_descend {z : ℤ} (hz : Odd z) {f : ℕ}
    (h : (2 : ℤ) ^ (f + 1) ∣ z ^ 2 - 1) : (2 : ℤ) ^ f ∣ z - 1 ∨ (2 : ℤ) ^ f ∣ z + 1 := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · exact Or.inl (by simp)
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨u, hu⟩ := hz
  have hfac : z ^ 2 - 1 = 4 * (u * (u + 1)) := by rw [hu]; ring
  rw [hfac] at h
  have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
  rw [h4] at h
  have hg : (2 : ℤ) ^ g ∣ u * (u + 1) := by
    have h' : (2 : ℤ) ^ 2 * (2 : ℤ) ^ g ∣ (2 : ℤ) ^ 2 * (u * (u + 1)) := by
      rw [← pow_add]
      convert h using 2
      omega
    exact (mul_dvd_mul_iff_left (a := (2 : ℤ) ^ 2) (by norm_num)).1 h'
  have hp2 : Prime (2 : ℤ) := Int.prime_two
  rcases Int.even_or_odd u with he | ho
  · -- `u` even, `u + 1` odd: `2^g ∣ u`
    have hodd : ¬ (2 : ℤ) ∣ (u + 1) := by
      rcases he with ⟨v, hv⟩
      intro hd
      obtain ⟨w, hw⟩ := hd
      omega
    have : (2 : ℤ) ^ g ∣ u := hp2.pow_dvd_of_dvd_mul_right g hodd hg
    refine Or.inl ?_
    have : (2 : ℤ) ^ (g + 1) ∣ 2 * u := by
      rw [pow_succ, mul_comm ((2:ℤ)^g) 2]
      exact mul_dvd_mul_left 2 this
    simpa [hu] using this
  · have hodd : ¬ (2 : ℤ) ∣ u := by
      rcases ho with ⟨v, hv⟩
      intro hd
      obtain ⟨w, hw⟩ := hd
      omega
    have : (2 : ℤ) ^ g ∣ (u + 1) := hp2.pow_dvd_of_dvd_mul_left g hodd hg
    refine Or.inr ?_
    have h2 : (2 : ℤ) ^ (g + 1) ∣ 2 * (u + 1) := by
      rw [pow_succ, mul_comm ((2:ℤ)^g) 2]
      exact mul_dvd_mul_left 2 this
    have : z + 1 = 2 * (u + 1) := by rw [hu]; ring
    rw [this]; exact h2

/-- **Descent at `2`:** `2^e ∣ z^(2^a) − 1` forces `2^(e−a) ∣ z ∓ 1`. -/
theorem two_pow_descend {z : ℤ} (hz : Odd z) {e a : ℕ}
    (h : (2 : ℤ) ^ e ∣ z ^ (2 ^ a) - 1) :
    (2 : ℤ) ^ (e - a) ∣ z - 1 ∨ (2 : ℤ) ^ (e - a) ∣ z + 1 := by
  induction a generalizing e with
  | zero => simpa using Or.inl (by simpa using h)
  | succ a ih =>
    rcases Nat.eq_zero_or_pos e with rfl | hepos
    · exact Or.inl (by simp)
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    set Z : ℤ := z ^ (2 ^ a) with hZ
    have hZodd : Odd Z := hz.pow
    have hsq : Z ^ 2 = z ^ (2 ^ (a + 1)) := by
      rw [hZ, ← pow_mul, pow_succ]
    have hd := two_descend hZodd (f := e') (by rw [hsq]; exact h)
    rcases hd with hl | hr
    · have := ih (e := e') hl
      simpa [show e' + 1 - (a + 1) = e' - a by omega] using this
    · rcases Nat.eq_zero_or_pos (e' - a) with h0 | hpos
      · exact Or.inl (by simp [show e' + 1 - (a + 1) = e' - a by omega, h0])
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · refine Or.inr ?_
        have hZz : Z = z := by rw [hZ]; simp
        rw [hZz] at hr
        simpa [show e' + 1 - (0 + 1) = e' by omega] using hr
      · -- `Z` is an odd square, so `Z ≡ 1 (mod 8)` and `4 ∤ Z + 1`
        exfalso
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        have h8 : (8 : ℤ) ∣ Z - 1 := by
          have : Z = (z ^ (2 ^ b)) ^ 2 := by rw [hZ, ← pow_mul, pow_succ]
          rw [this]
          exact Int.eight_dvd_sq_sub_one_of_odd hz.pow
        have he2 : 2 ≤ e' := by omega
        have h4 : (4 : ℤ) ∣ Z + 1 := by
          refine dvd_trans ?_ hr
          have : (4 : ℤ) = 2 ^ 2 := by norm_num
          rw [this]; exact pow_dvd_pow 2 he2
        have h4' : (4 : ℤ) ∣ Z - 1 := dvd_trans (by norm_num) h8
        have : (4 : ℤ) ∣ 2 := by simpa using dvd_sub h4 h4'
        omega

/-- **Theorem A.** -/
theorem entry_prime_pow_add_not_prime {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ}
    (hc : c.Prime) (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c))))
    (hodd : Odd d) (hmu : c = 2 ∨ ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) {i j : Fin d} (hij : i ≠ j)
    (hnz : ∃ r < d, ¬ (c : ℤ) ∣ (A ^ (c ^ r)) i j)
    (hgrow : Tendsto (fun n => |(A ^ (c ^ n)) i j|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((A ^ (c ^ n)) i j + h) := by
  sorry

/-- Tribonacci: `T 0 = T 1 = 0`, `T 2 = 1`, `T (n+3) = T (n+2) + T (n+1) + T n`. -/
def trib : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => trib (n + 2) + trib (n + 1) + trib n

/-- **`T(3^n) + h` is composite for infinitely many `n`, for every `h`.** -/
theorem trib_three_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (trib (3 ^ n) + h) := by
  sorry

/-- **`T(5^n) + h` is composite for infinitely many `n`, for every `h`.** -/
theorem trib_five_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (trib (5 ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.TheoremA
