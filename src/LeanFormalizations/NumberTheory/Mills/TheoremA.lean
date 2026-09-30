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

open LeanFormalizations.Mills.ThreeAdic Matrix Filter

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

/-- With `μ_(≤d)(ℤ_c) = {±1}`, an exponent `i ≤ d` with `c ∣ z^i − 1` forces `c ∣ z² − 1`. -/
theorem sq_congr_one_of_mu {c d i : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hmu : ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) (hi1 : 1 ≤ i) (hid : i ≤ d) {z : ℤ}
    (hz : ¬ (c : ℤ) ∣ z) (h : (c : ℤ) ∣ z ^ i - 1) : (c : ℤ) ∣ z ^ 2 - 1 := by
  haveI : Fact c.Prime := ⟨hc⟩
  set w : ZMod c := (z : ZMod c) with hw
  have hwne : w ≠ 0 := by
    rw [hw]
    intro hd
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hd)
  have hwi : w ^ i = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (z ^ i - 1) c).2 h
    push_cast at this
    rw [hw]
    linear_combination this
  have hfin : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.2 ⟨i, by omega, hwi⟩
  have hgpos : 0 < orderOf w := orderOf_pos_iff.2 hfin
  have hgi : orderOf w ∣ i := orderOf_dvd_of_pow_eq_one hwi
  have hgc : orderOf w ∣ c - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hwne)
  have hgle : orderOf w ≤ i := Nat.le_of_dvd (by omega) hgi
  have hg2 : orderOf w ∣ 2 := by
    rcases Nat.lt_or_ge (orderOf w) 3 with hlt | hge
    · interval_cases h : orderOf w <;> simp_all
    · exact absurd hgc (hmu _ hge (by omega))
  have hw2 : w ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hg2
  have : ((z ^ 2 - 1 : ℤ) : ZMod c) = 0 := by push_cast; rw [← hw, hw2]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this

/-- `(-1 : ZMod c) ≠ 1` for an odd prime `c`. -/
theorem neg_one_ne_one_zmod {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) :
    (-1 : ZMod c) ≠ 1 := by
  intro hh
  have h2 : ((2 : ℤ) : ZMod c) = 0 := by push_cast; linear_combination -hh
  have hd : (c : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
  have hle := Int.le_of_dvd (by norm_num) hd
  have h2c := hc.two_le
  have : (2 : ℤ) ≤ (c : ℤ) := by exact_mod_cast h2c
  have : c = 2 := by omega
  exact hc2 this

/-- **The window at an odd prime.**  `c^e ∣ z^i − 1` with `1 ≤ i ≤ d` and `μ_(≤d) = {±1}`
gives `c^e ∣ z − σ` for a sign `σ`, provided `c ∤ z`. -/
theorem exists_sign_dvd_sub_odd {c d i e : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hmu : ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) (hi1 : 1 ≤ i) (hid : i ≤ d) (he : 1 ≤ e)
    {z : ℤ} (hz : ¬ (c : ℤ) ∣ z) (hdvd : (c : ℤ) ^ e ∣ z ^ i - 1) (hci : ¬ c ∣ i) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ (c : ℤ) ^ e ∣ z - σ := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hcp : Prime (c : ℤ) := Nat.prime_iff_prime_int.1 hc
  have h1 : (c : ℤ) ∣ z ^ i - 1 := dvd_trans (dvd_pow_self _ (by omega)) hdvd
  have hz2 : (c : ℤ) ∣ z ^ 2 - 1 := sq_congr_one_of_mu hc hc2 hmu hi1 hid hz h1
  by_cases hd1 : (c : ℤ) ∣ z - 1
  · exact ⟨1, Or.inl rfl, dvd_sub_one_of_coprime_exp hc hci hd1 hdvd⟩
  · -- `c ∣ z + 1`
    have hd2 : (c : ℤ) ∣ z + 1 := by
      have hfac : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
      rw [hfac] at hz2
      exact (hcp.dvd_or_dvd hz2).resolve_left hd1
    -- `i` is even
    have hzw : ((z : ZMod c)) = -1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (z + 1) c).2 hd2
      push_cast at this
      linear_combination this
    have hwi : ((z : ZMod c)) ^ i = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (z ^ i - 1) c).2 h1
      push_cast at this
      linear_combination this
    rw [hzw] at hwi
    have hieven : Even i := (neg_one_pow_eq_one_iff_even (neg_one_ne_one_zmod hc hc2)).1 hwi
    obtain ⟨m, hm⟩ := hieven
    have hm2 : i = 2 * m := by omega
    have hcm : ¬ c ∣ m := fun hd => hci (hm2 ▸ Dvd.dvd.mul_left hd 2)
    have hstep : (c : ℤ) ^ e ∣ (z ^ 2) ^ m - 1 := by
      rw [← pow_mul, show 2 * m = i by omega]; exact hdvd
    have hze : (c : ℤ) ^ e ∣ z ^ 2 - 1 := dvd_sub_one_of_coprime_exp hc hcm hz2 hstep
    refine ⟨-1, Or.inr rfl, ?_⟩
    have hfac : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
    rw [hfac] at hze
    have := hcp.pow_dvd_of_dvd_mul_left e hd1 hze
    simpa using this

/-- **Step 2 (the window).**  If `p^i ≡ 1 (mod c^e)` for some `1 ≤ i ≤ d` and
`μ_(≤d)(ℤ_c) = {±1}`, then `p ≡ ±1 (mod c^(e−d))`. -/
theorem exists_sign_dvd_sub {c p d i e : ℕ} (hc : c.Prime) (hp : p.Prime) (hpc : p ≠ c)
    (hmu : c = 2 ∨ ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) (hi1 : 1 ≤ i) (hid : i ≤ d) (he : 1 ≤ e)
    (hdvd : (c : ℤ) ^ e ∣ (p : ℤ) ^ i - 1) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (c : ℤ) ^ (e - d) ∣ (p : ℤ) - s := by
  have hcp : Prime (c : ℤ) := Nat.prime_iff_prime_int.1 hc
  have hine : i ≠ 0 := by omega
  set a : ℕ := i.factorization c with hadef
  set i₀ : ℕ := i / c ^ a with hi0def
  have hsplit : c ^ a * i₀ = i := Nat.ordProj_mul_ordCompl_eq_self i c
  have hci0 : ¬ c ∣ i₀ := Nat.not_dvd_ordCompl hc hine
  have hi0dvd : i₀ ∣ i := ⟨c ^ a, by rw [← hsplit]; ring⟩
  have hi0pos : 1 ≤ i₀ := by
    rcases Nat.eq_zero_or_pos i₀ with h0 | h; · rw [h0, mul_zero] at hsplit; omega
    exact h
  have hi0d : i₀ ≤ d := le_trans (Nat.le_of_dvd (by omega) hi0dvd) hid
  have hcad : c ^ a ≤ d := by
    have h1 : c ^ a ∣ i := Nat.ordProj_dvd i c
    exact le_trans (Nat.le_of_dvd (by omega) h1) hid
  have had : a ≤ d := by
    have h1 : (2 : ℕ) ^ a ≤ c ^ a := Nat.pow_le_pow_left hc.two_le a
    have h2 : a < 2 ^ a := Nat.lt_two_pow_self
    omega
  have hcpn : ¬ (c : ℤ) ∣ (p : ℤ) := by
    intro hd
    have : c ∣ p := Int.ofNat_dvd.1 (by exact_mod_cast hd)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp c this) with hh | hh
    · have := hc.two_le; omega
    · exact hpc hh.symm
  have hpow : ((p : ℤ) ^ (c ^ a)) ^ i₀ = (p : ℤ) ^ i := by
    rw [← pow_mul, hsplit]
  by_cases hc2 : c = 2
  · -- `c = 2`
    subst hc2
    have hpodd : Odd (p : ℤ) := by
      rcases Int.even_or_odd (p : ℤ) with hev | ho
      · exact absurd (hev.two_dvd) (by simpa using hcpn)
      · exact ho
    have hz1 : (2 : ℤ) ∣ (p : ℤ) ^ (2 ^ a) - 1 := by
      have : Odd ((p : ℤ) ^ (2 ^ a)) := hpodd.pow
      obtain ⟨u, hu⟩ := this
      exact ⟨u, by rw [hu]; ring⟩
    have hstep : (2 : ℤ) ^ e ∣ ((p : ℤ) ^ (2 ^ a)) ^ i₀ - 1 := by
      rw [hpow]; exact_mod_cast hdvd
    have hze : (2 : ℤ) ^ e ∣ (p : ℤ) ^ (2 ^ a) - 1 :=
      dvd_sub_one_of_coprime_exp Nat.prime_two hci0 hz1 hstep
    have hmono : (2 : ℤ) ^ (e - d) ∣ (2 : ℤ) ^ (e - a) := pow_dvd_pow 2 (by omega)
    rcases two_pow_descend hpodd hze with hl | hr
    · exact ⟨1, Or.inl rfl, by exact_mod_cast dvd_trans hmono hl⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have := dvd_trans hmono hr
      have hrw : (p : ℤ) - -1 = (p : ℤ) + 1 := by ring
      rw [hrw]; exact_mod_cast this
  · -- `c` odd
    have hmu : ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1 := hmu.resolve_left hc2
    have hz : ¬ (c : ℤ) ∣ (p : ℤ) ^ (c ^ a) := fun hd => hcpn (hcp.dvd_of_dvd_pow hd)
    have hstep : (c : ℤ) ^ e ∣ ((p : ℤ) ^ (c ^ a)) ^ i₀ - 1 := by rw [hpow]; exact hdvd
    obtain ⟨σ, hσ, hσd⟩ :=
      exists_sign_dvd_sub_odd hc hc2 hmu hi0pos hi0d he hz hstep hci0
    have hcaodd : Odd (c ^ a) := (hc.odd_of_ne_two hc2).pow
    have hy : (σ * (p : ℤ)) ^ (c ^ a) - 1 = σ * ((p : ℤ) ^ (c ^ a) - σ) := by
      rcases hσ with rfl | rfl
      · simp
      · rw [mul_pow, hcaodd.neg_one_pow]
        ring
    have hyd : (c : ℤ) ^ e ∣ (σ * (p : ℤ)) ^ (c ^ a) - 1 := by
      rw [hy]; exact Dvd.dvd.mul_left hσd σ
    rcases Nat.lt_or_ge a e with hae | hae
    · have hf : (e - a) + a = e := by omega
      rw [← hf] at hyd
      have hres := dvd_sub_one_of_pow_pow_odd hc hc2 hyd
      refine ⟨σ, hσ, ?_⟩
      have hmono : (c : ℤ) ^ (e - d) ∣ (c : ℤ) ^ (e - a) := pow_dvd_pow _ (by omega)
      have hfin : (c : ℤ) ^ (e - a) ∣ (p : ℤ) - σ := by
        have hid2 : (p : ℤ) - σ = σ * (σ * (p : ℤ) - 1) := by
          rcases hσ with rfl | rfl <;> ring
        rw [hid2]
        exact Dvd.dvd.mul_left hres σ
      exact dvd_trans hmono hfin
    · refine ⟨1, Or.inl rfl, ?_⟩
      have : e - d = 0 := by omega
      simp [this]

/-! ### Structural inputs: the determinant is a unit mod `c`, and the period -/

/-- Irreducibility of `χ̄_A` (in dimension `≥ 2`) makes `det A` a unit mod `c`. -/
theorem not_dvd_det_of_irreducible {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (hd : 2 ≤ d) :
    ¬ (c : ℤ) ∣ A.det := by
  haveI : Fact c.Prime := ⟨hc⟩
  intro hdvd
  have hdet := Matrix.det_eq_sign_charpoly_coeff A
  rw [Fintype.card_fin] at hdet
  have hsq : ((-1 : ℤ) ^ d) * ((-1 : ℤ) ^ d) = 1 := by
    rw [← pow_add, show d + d = 2 * d by ring, pow_mul]; norm_num
  have hc0 : (c : ℤ) ∣ A.charpoly.coeff 0 := by
    have : A.charpoly.coeff 0 = ((-1 : ℤ) ^ d) * A.det := by
      rw [hdet]; rw [← mul_assoc, hsq, one_mul]
    rw [this]
    exact Dvd.dvd.mul_left hdvd _
  have hzero : (A.charpoly.map (Int.castRingHom (ZMod c))).coeff 0 = 0 := by
    rw [Polynomial.coeff_map]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).2 hc0
  obtain ⟨g, hg⟩ := (Polynomial.X_dvd_iff).2 hzero
  have hdeg : (A.charpoly.map (Int.castRingHom (ZMod c))).natDegree = d :=
    OrbitSum.charpolyBar_natDegree A c
  rcases hirr.isUnit_or_isUnit hg with hu | hu
  · have := Polynomial.natDegree_eq_zero_of_isUnit hu
    simp at this
  · have hg0 : g.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hne : (A.charpoly.map (Int.castRingHom (ZMod c))) ≠ 0 := hirr.ne_zero
    have hgne : g ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hg; exact hne hg
    have : (A.charpoly.map (Int.castRingHom (ZMod c))).natDegree = 1 + 0 := by
      rw [hg, Polynomial.natDegree_mul Polynomial.X_ne_zero hgne, Polynomial.natDegree_X, hg0]
    omega

/-- **Period mod `c`:** `(A^(c^(m + q·d))) i j ≡ (A^(c^m)) i j (mod c)`. -/
theorem entry_period {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (m q : ℕ) (i j : Fin d) :
    (c : ℤ) ∣ (A ^ (c ^ (m + q * d))) i j - (A ^ (c ^ m)) i j := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hstep : (c : ℤ) ∣ (A ^ (c ^ (m + q * d + d))) i j - (A ^ (c ^ (m + q * d))) i j :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero _))
        (OrbitSum.pow_prime_pow_add_card_congr A hc hirr (m + q * d) i j)
    have := dvd_add hstep ih
    simpa [show m + (q + 1) * d = m + q * d + d by ring] using this

/-- **Theorem A.** -/
theorem entry_prime_pow_add_not_prime {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ}
    (hc : c.Prime) (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c))))
    (hodd : Odd d) (hmu : c = 2 ∨ ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) {i j : Fin d} (hij : i ≠ j)
    (hnz : ∃ r < d, ¬ (c : ℤ) ∣ (A ^ (c ^ r)) i j)
    (hgrow : Tendsto (fun n => |(A ^ (c ^ n)) i j|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((A ^ (c ^ n)) i j + h) := by
  haveI : Fact c.Prime := ⟨hc⟩
  obtain ⟨r, hrd, hr⟩ := hnz
  have hd2 : 2 ≤ d := by
    have h1 := i.isLt
    have h2 := j.isLt
    have h3 : (i : ℕ) ≠ (j : ℕ) := fun hh => hij (Fin.ext hh)
    omega
  set u : ℕ → ℤ := fun n => (A ^ (c ^ n)) i j with hudef
  set t : ℕ → ℤ := fun n => u n + h with htdef
  have hcle : 2 ≤ c := hc.two_le
  have hdet : ¬ (c : ℤ) ∣ A.det := not_dvd_det_of_irreducible A hc hirr hd2
  have hdet0 : A.det ≠ 0 := fun h0 => hdet (by rw [h0]; exact dvd_zero _)
  have hgr : ∀ B : ℤ, ∃ N : ℕ, ∀ n ≥ N, B ≤ |u n| := by
    intro B
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hgrow B)
    exact ⟨N, hN⟩
  have hlow : ∀ n : ℕ, |u n| - |h| ≤ |t n| := fun n => LucasInert.abs_sub_abs_le_abs_add'
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  set H : ℕ := h.natAbs with hH
  have hHabs : |h| = (H : ℤ) := Int.abs_eq_natAbs h
  obtain ⟨N₁, hN₁⟩ := hgr (|h| + |A.det| + (c : ℤ) + 3)
  set N : ℕ := max (max n₀ N₁) d with hNdef
  have hprime : ∀ n ≥ N, Prime (t n) := fun n hn => hn₀ n (by omega)
  have hpabs : ∀ n : ℕ, ((t n).natAbs : ℤ) = |t n| := fun n => (Int.abs_eq_natAbs _).symm
  have hbig : ∀ n ≥ N, |A.det| + (c : ℤ) + 3 ≤ |t n| := by
    intro n hn
    have h1 := hN₁ n (by omega)
    have h2 := hlow n
    linarith
  have hpn : ∀ n ≥ N, (t n).natAbs.Prime := fun n hn =>
    Int.prime_iff_natAbs_prime.1 (hprime n hn)
  have hpnec : ∀ n ≥ N, (t n).natAbs ≠ c := by
    intro n hn hEq
    have h1 := hbig n hn
    have h2 := hpabs n
    rw [hEq] at h2
    have h3 := abs_nonneg A.det
    omega
  have hpdvdD : ∀ n ≥ N, ¬ ((t n).natAbs : ℤ) ∣ A.det := by
    intro n hn hd
    have h1 : ((t n).natAbs : ℤ) ≤ |A.det| :=
      Int.le_of_dvd (abs_pos.2 hdet0) ((dvd_abs _ _).2 hd)
    have h2 := hbig n hn
    rw [hpabs n] at h1
    have h3 : (0 : ℤ) ≤ (c : ℤ) := by positivity
    omega
  -- **Step 1 (the return step).**
  have hstep : ∀ n ≥ N, padicValNat c (glCard d (t n).natAbs) ≤ n →
      ∃ q, 1 ≤ q ∧ (t (n + q)).natAbs = (t n).natAbs := by
    intro n hn hv
    obtain ⟨q, hq1, hq⟩ := SaitoFibonacci.exists_entry_pow_congr A (hpn n hn) hc
      (hpdvdD n hn) hv
    have hent : ((t n).natAbs : ℤ) ∣ u (n + q) - u n := hq i j
    have hdvd : ((t n).natAbs : ℤ) ∣ t (n + q) := by
      have hA : ((t n).natAbs : ℤ) ∣ t n := Int.natAbs_dvd.2 dvd_rfl
      have hre : t (n + q) = (u (n + q) - u n) + t n := by simp only [htdef]; ring
      rw [hre]
      exact dvd_add hent hA
    have hqp := hpn (n + q) (by omega)
    have hdq : (t n).natAbs ∣ (t (n + q)).natAbs :=
      Int.natAbs_dvd_natAbs.2 (Int.natAbs_dvd.1 hdvd)
    rcases hqp.eq_one_or_self_of_dvd _ hdq with hh | hh
    · exact absurd hh (hpn n hn).ne_one
    · exact ⟨q, hq1, hh.symm⟩
  have hstep2 : ∀ n ≥ N, n < padicValNat c (glCard d (t n).natAbs) := by
    intro n hn
    by_contra hle
    push_neg at hle
    have chain : ∀ k : ℕ, ∃ n' : ℕ, n + k ≤ n' ∧ (t n').natAbs = (t n).natAbs ∧
        padicValNat c (glCard d (t n').natAbs) ≤ n' := by
      intro k
      induction k with
      | zero => exact ⟨n, by omega, rfl, hle⟩
      | succ k ih =>
        obtain ⟨n', hn'1, hn'2, hn'3⟩ := ih
        obtain ⟨q, hq1, hq⟩ := hstep n' (by omega) hn'3
        refine ⟨n' + q, by omega, ?_, ?_⟩
        · rw [hq]; exact hn'2
        · rw [hq]; omega
    obtain ⟨Nb, hNb⟩ := hgr (|t n| + |h| + 1)
    obtain ⟨n', hc1, hc2', _⟩ := chain (Nb + n)
    have h1 : |t n'| = |t n| := by rw [← hpabs n', ← hpabs n, hc2']
    have h2 := hNb n' (by omega)
    have h3 := hlow n'
    linarith
  -- **Step 2 (the window).**
  have hstep3 : ∀ n ≥ N, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (c : ℤ) ^ (n / d - d) ∣ t n - s := by
    intro n hn
    have hnd : 1 ≤ n / d := Nat.one_le_div_iff (by omega) |>.2 (by omega)
    obtain ⟨i', hi'1, hi'd, hi'⟩ := TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard
      hc (hpn n hn) (hpnec n hn) (by omega) (hstep2 n hn)
    obtain ⟨s0, hs0, hd0⟩ := exists_sign_dvd_sub hc (hpn n hn) (hpnec n hn) hmu hi'1 hi'd hnd hi'
    rcases Int.natAbs_eq (t n) with he | he
    · exact ⟨s0, hs0, by rw [he]; exact hd0⟩
    · refine ⟨-s0, ?_, ?_⟩
      · rcases hs0 with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by norm_num)
      · have hrw : t n - -s0 = -(((t n).natAbs : ℤ) - s0) := by omega
        rw [hrw]
        exact dvd_neg.2 hd0
  -- **Steps 3–4: the orbit sum pins every sign to `h`, and the period contradicts `c ∤ u r`.**
  set M₀ : ℕ := d * H + d + 1 with hM₀
  set Q : ℕ := M₀ + d + N + 1 with hQ
  set n : ℕ := d * Q + r with hn
  have hdiv : n / d = Q := by
    rw [hn, Nat.mul_add_div (by omega : 0 < d), Nat.div_eq_of_lt hrd]
  have hnN : N ≤ n := by
    have : Q ≤ d * Q := Nat.le_mul_of_pos_left Q (by omega)
    omega
  have hE : M₀ ≤ n / d - d := by rw [hdiv]; omega
  set E : ℕ := n / d - d with hEdef
  have hQle : Q ≤ n := by
    have : Q ≤ d * Q := Nat.le_mul_of_pos_left Q (by omega)
    omega
  have hall : ∀ k : ℕ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (c : ℤ) ^ E ∣ t (n + k) - s := by
    intro k
    obtain ⟨s, hs, hsd⟩ := hstep3 (n + k) (by omega)
    refine ⟨s, hs, dvd_trans (pow_dvd_pow _ ?_) hsd⟩
    rw [hEdef]
    have : n / d ≤ (n + k) / d := Nat.div_le_div_right (by omega)
    omega
  choose S hS1 hS2 using hall
  -- the modulus we actually use
  set m : ℕ := min E (n + 1) with hm
  have hmM₀ : M₀ ≤ m := by rw [hm]; omega
  have hbnd : (d * (H : ℤ) + d : ℤ) < (c : ℤ) ^ m := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ m ≤ c ^ m := Nat.pow_le_pow_left hcle m
    have h0 : d * H + d < M₀ := by rw [hM₀]; omega
    have h3 : d * H + d < c ^ m :=
      lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0 hmM₀) (le_of_lt h1)) h2
    exact_mod_cast h3
  have horb : (c : ℤ) ^ (n + 1) ∣ ∑ k ∈ Finset.range d, u (n + k) :=
    OrbitSum.orbit_sum_entry_congr A hc hirr n hij
  have hsum1 : (c : ℤ) ^ m ∣ ∑ k ∈ Finset.range d, (t (n + k) - S k) := by
    refine Finset.dvd_sum fun k _ => dvd_trans (pow_dvd_pow _ ?_) (hS2 k)
    omega
  have hsum2 : (c : ℤ) ^ m ∣ ∑ k ∈ Finset.range d, u (n + k) :=
    dvd_trans (pow_dvd_pow _ (by omega)) horb
  have hsplit : ∑ k ∈ Finset.range d, (t (n + k) - S k)
      = (∑ k ∈ Finset.range d, u (n + k)) + (d * h - ∑ k ∈ Finset.range d, S k) := by
    simp only [htdef, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range]
    ring
  have hkey : (c : ℤ) ^ m ∣ d * h - ∑ k ∈ Finset.range d, S k := by
    rw [hsplit] at hsum1
    simpa using (dvd_sub hsum1 hsum2)
  have habsS : |∑ k ∈ Finset.range d, S k| ≤ (d : ℤ) := by
    have heq : ∀ k ∈ Finset.range d, |S k| = (1 : ℤ) := by
      intro k _; rcases hS1 k with hh | hh <;> simp [hh]
    have hb := Finset.abs_sum_le_sum_abs S (Finset.range d)
    rw [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_range] at hb
    simpa using hb
  have hzero : (d : ℤ) * h - ∑ k ∈ Finset.range d, S k = 0 := by
    by_contra hne
    have hle := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hkey)
    have hb : |(d : ℤ) * h - ∑ k ∈ Finset.range d, S k| ≤ d * (H : ℤ) + d := by
      have h1 : |(d : ℤ) * h| = d * (H : ℤ) := by
        rw [abs_mul, hHabs, abs_of_nonneg (by positivity : (0:ℤ) ≤ (d:ℤ))]
      have := abs_sub (((d : ℤ)) * h) (∑ k ∈ Finset.range d, S k)
      calc |(d : ℤ) * h - ∑ k ∈ Finset.range d, S k|
          ≤ |(d : ℤ) * h| + |∑ k ∈ Finset.range d, S k| := abs_sub _ _
        _ ≤ d * (H : ℤ) + d := by rw [h1]; linarith
    omega
  -- `d` odd forces `h ≠ 0`, and then `|h| ≤ 1`
  have hpar : (2 : ℤ) ∣ (∑ k ∈ Finset.range d, S k) - d := by
    have : (∑ k ∈ Finset.range d, S k) - d = ∑ k ∈ Finset.range d, (S k - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    refine Finset.dvd_sum fun k _ => ?_
    rcases hS1 k with hh | hh <;> rw [hh] <;> norm_num
  have hh1 : h = 1 ∨ h = -1 := by
    have hsum : ∑ k ∈ Finset.range d, S k = (d : ℤ) * h := by linarith [hzero]
    rcases eq_or_ne h 0 with rfl | h0
    · rw [hsum] at hpar
      simp only [mul_zero, zero_sub, dvd_neg] at hpar
      obtain ⟨k, hk⟩ := hodd
      have : (2 : ℤ) ∣ (d : ℤ) := hpar
      have hd' : (d : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      omega
    · have hdpos : (0 : ℤ) < d := by positivity
      have h2 : |(d : ℤ) * h| ≤ (d : ℤ) := by rw [← hsum]; exact habsS
      rw [abs_mul, abs_of_nonneg hdpos.le, hHabs] at h2
      have : (H : ℤ) ≤ 1 := by
        rcases le_or_gt (H : ℤ) 1 with hle | hlt
        · exact hle
        · nlinarith
      have hH1 : H = 1 := by
        have hH0 : H ≠ 0 := by simpa [hH, Int.natAbs_eq_zero] using h0
        have : H ≤ 1 := by exact_mod_cast this
        omega
      rw [hH] at hH1
      omega
  -- every sign equals `h`
  have hhsq : h * h = 1 := by rcases hh1 with rfl | rfl <;> norm_num
  have hprodsum : ∑ k ∈ Finset.range d, (1 - h * S k) = 0 := by
    have hsum : ∑ k ∈ Finset.range d, S k = (d : ℤ) * h := by linarith [hzero]
    have : ∑ k ∈ Finset.range d, (1 - h * S k)
        = (d : ℤ) - h * ∑ k ∈ Finset.range d, S k := by
      rw [Finset.mul_sum]
      simp [Finset.sum_sub_distrib]
    rw [this, hsum]
    have : h * ((d : ℤ) * h) = (d : ℤ) * (h * h) := by ring
    rw [this, hhsq, mul_one]
    ring
  have hS0 : S 0 = h := by
    have hnn : ∀ k ∈ Finset.range d, (0 : ℤ) ≤ 1 - h * S k := by
      intro k _
      rcases hh1 with rfl | rfl <;> rcases hS1 k with hh | hh <;> rw [hh] <;> norm_num
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hprodsum 0 (Finset.mem_range.2 (by omega))
    have hz : h * S 0 = 1 := by linarith
    rcases hS1 0 with hh | hh
    · rcases hh1 with h1 | h1
      · rw [hh, h1]
      · rw [hh, h1] at hz; norm_num at hz
    · rcases hh1 with h1 | h1
      · rw [hh, h1] at hz; norm_num at hz
      · rw [hh, h1]
  -- so `c ∣ u n`, and the period carries this back to `u r`
  have hEpos : 1 ≤ E := by omega
  have hun : (c : ℤ) ∣ u n := by
    have := hS2 0
    rw [hS0] at this
    have hre : t (n + 0) - h = u n := by simp [htdef]
    rw [hre] at this
    exact dvd_trans (dvd_pow_self _ (by omega : E ≠ 0)) this
  have hper : (c : ℤ) ∣ u (r + Q * d) - u r := entry_period A hc hirr r Q i j
  have hnr : n = r + Q * d := by rw [hn]; ring
  rw [← hnr] at hper
  exact hr (by have := dvd_sub hun hper; simpa using this)

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
