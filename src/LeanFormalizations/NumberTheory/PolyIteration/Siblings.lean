/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The siblings of A003095: Sylvester's sequence, A003096, A002065, A004019


Elementary facts recorded on the OEIS entries (checked 2026-09-28), plus Bala's general
divisibility properties of polynomial iterations (A000058 formula section, Jul 19 2026).  The
growth constants of these sequences are transcendental: `NumberTheory/Transcendence/Dubickas.lean`.

All statements were checked numerically before freezing.  Two OEIS texts needed care:

* A000058, Murthy (2003): "a(2n+6) == 443 (mod 1000) and a(2n+7) == 807 (mod 1000)".  With the
  entry's current offset 0 (`a(0) = 2`) the residues are the other way round: `a(4) = 1807`,
  `a(5) = 3263443`.  Stated below in the offset-0 form (`a(2n+4) ≡ 807`, `a(2n+5) ≡ 443`).
* A000058, the "reduced modulo 864" comment is stated as `a(n+2) ≡ 7 + 36n (mod 864)`.

Sources: Bala 2026 (`papers/bala-2026-sylvester-strong-divisibility.txt`); Mohanty's coprime
recursions and the `−3` quadratic-residue fact are quoted on A000058 (Pollack, *Not Always
Buried Deep*, exercise 1.2.3c).
-/
import LeanFormalizations.NumberTheory.PolyIteration.A003095

namespace LeanFormalizations.PolyIteration

open Polynomial

/-! ## Bala's divisibility properties, for any `u (n+1) = P(u n)` -/

section General
variable (P : ℤ[X]) (u : ℕ → ℤ) (hu : ∀ n, u (n + 1) = P.eval (u n))
include hu

/-- `u(n+k) − u(n) ∣ u(n+k+j) − u(n+j)`; so modulo `u(n+k) − u(n)` the sequence has period `k`
from index `n`. -/
theorem sub_dvd_sub_add (n k j : ℕ) : u (n + k) - u n ∣ u (n + k + j) - u (n + j) :=
  sub_dvd_sub_shift P u hu (n + k) n j

/-- The workhorse behind Bala's linear-index divisibilities: modulo `u n − u k` the index may be
advanced by a multiple of `n` or of `k` interchangeably. -/
theorem sub_dvd_sub_addMul (n k : ℕ) : ∀ d B : ℕ, u n - u k ∣ u (B + d * n) - u (B + d * k) := by
  intro d
  induction d with
  | zero => intro B; simp
  | succ d ih =>
      intro B
      have e1 : B + (d + 1) * n = (B + d * n) + n := by ring
      have e2 : B + (d + 1) * k = (B + d * k) + k := by ring
      have h1 : u n - u k ∣ u ((B + d * n) + n) - u ((B + d * k) + n) :=
        dvd_trans (ih B) (sub_dvd_sub_shift P u hu _ _ n)
      have h2 : u n - u k ∣ u ((B + d * k) + n) - u ((B + d * k) + k) := by
        have := sub_dvd_sub_shift P u hu n k (B + d * k)
        rwa [Nat.add_comm n (B + d * k), Nat.add_comm k (B + d * k)] at this
      rw [e1, e2]
      have := dvd_add h1 h2
      simpa using this

/-- `u(n) − u(k) ∣ u(r n + s k) − u(s n + r k)`. -/
theorem sub_dvd_sub_lin (n k r s : ℕ) :
    u n - u k ∣ u (r * n + s * k) - u (s * n + r * k) := by
  rcases le_total s r with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, r = s + d := ⟨r - s, by omega⟩
    have e1 : (s + d) * n + s * k = s * (n + k) + d * n := by ring
    have e2 : s * n + (s + d) * k = s * (n + k) + d * k := by ring
    rw [e1, e2]
    exact sub_dvd_sub_addMul P u hu n k d _
  · obtain ⟨d, rfl⟩ : ∃ d, s = r + d := ⟨s - r, by omega⟩
    have e1 : r * n + (r + d) * k = r * (n + k) + d * k := by ring
    have e2 : (r + d) * n + r * k = r * (n + k) + d * n := by ring
    rw [e1, e2]
    have := (sub_dvd_sub_addMul P u hu n k d (r * (n + k))).neg_right
    simpa using this

/-- `u(n) − u(k) ∣ u(m n) − u(m k)` (Bala's `u(n) ≠ u(k)` proviso is not needed). -/
theorem sub_dvd_sub_mul (n k m : ℕ) : u n - u k ∣ u (m * n) - u (m * k) := by
  have := sub_dvd_sub_addMul P u hu n k m 0
  simpa using this

/-- `u(n) − u(k) ∣ u(r n) u(s k) − u(r k) u(s n)`. -/
theorem sub_dvd_det (n k r s : ℕ) :
    u n - u k ∣ u (r * n) * u (s * k) - u (r * k) * u (s * n) := by
  have h1 : u n - u k ∣ u (r * n) - u (r * k) := sub_dvd_sub_mul P u hu n k r
  have h2 : u n - u k ∣ u (s * n) - u (s * k) := sub_dvd_sub_mul P u hu n k s
  have := dvd_sub (h1.mul_left (u (s * k))) (h2.mul_left (u (r * k)))
  have e : u (s * k) * (u (r * n) - u (r * k)) - u (r * k) * (u (s * n) - u (s * k))
      = u (r * n) * u (s * k) - u (r * k) * u (s * n) := by ring
  rwa [e] at this

end General

/-! ## A000058, Sylvester's sequence -/

/-- **A000058**: `2, 3, 7, 43, 1807, …`, `a(n+1) = a(n)² − a(n) + 1`. -/
def sylvesterSeq : ℕ → ℤ
  | 0 => 2
  | n + 1 => sylvesterSeq n ^ 2 - sylvesterSeq n + 1

theorem sylvesterSeq_succ (n : ℕ) :
    sylvesterSeq (n + 1) = sylvesterSeq n ^ 2 - sylvesterSeq n + 1 := rfl

/-- The defining polynomial `X² − X + 1`. -/
private noncomputable def Ps : ℤ[X] := X ^ 2 - X + C 1

private theorem sylvesterSeq_iter (n : ℕ) : sylvesterSeq (n + 1) = Ps.eval (sylvesterSeq n) := by
  simp [Ps, sylvesterSeq_succ]

/-- Every term is at least `n + 2`; in particular at least `2`. -/
theorem sylvesterSeq_ge (n : ℕ) : (n : ℤ) + 2 ≤ sylvesterSeq n := by
  induction n with
  | zero => norm_num [sylvesterSeq]
  | succ n ih =>
      have h2 : (2 : ℤ) ≤ sylvesterSeq n := by
        have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
        linarith
      rw [sylvesterSeq_succ]
      push_cast
      nlinarith

theorem sylvesterSeq_two_le (n : ℕ) : (2 : ℤ) ≤ sylvesterSeq n := by
  have := sylvesterSeq_ge n
  have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  linarith [sylvesterSeq_ge n]

/-- Euclid numbers: `a(n) = 1 + a(0) a(1) ⋯ a(n−1)`. -/
theorem sylvesterSeq_eq_prod_add_one (n : ℕ) :
    sylvesterSeq n = (∏ i ∈ Finset.range n, sylvesterSeq i) + 1 := by
  induction n with
  | zero => simp [sylvesterSeq]
  | succ n ih =>
      rw [Finset.prod_range_succ, sylvesterSeq_succ, ih]
      ring

/-- The terms are pairwise coprime. -/
theorem sylvesterSeq_coprime {i j : ℕ} (hij : i ≠ j) :
    IsCoprime (sylvesterSeq i) (sylvesterSeq j) := by
  have key : ∀ a b : ℕ, a < b → IsCoprime (sylvesterSeq a) (sylvesterSeq b) := by
    intro a b hab
    obtain ⟨c, hc⟩ : sylvesterSeq a ∣ ∏ i ∈ Finset.range b, sylvesterSeq i :=
      Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hab)
    refine ⟨-c, 1, ?_⟩
    rw [sylvesterSeq_eq_prod_add_one b, hc]
    ring
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- The greedy Egyptian fraction, finite form: `Σ_{i<n} 1/a(i) = 1 − 1/(a(n) − 1)`. -/
theorem sylvesterSeq_sum_inv (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℚ) / sylvesterSeq i = 1 - 1 / (sylvesterSeq n - 1) := by
  induction n with
  | zero => norm_num [sylvesterSeq]
  | succ n ih =>
      have h2 : (2 : ℤ) ≤ sylvesterSeq n := sylvesterSeq_two_le n
      have hq : (2 : ℚ) ≤ (sylvesterSeq n : ℚ) := by exact_mod_cast h2
      have h0 : (sylvesterSeq n : ℚ) ≠ 0 := by linarith
      have h1 : (sylvesterSeq n : ℚ) - 1 ≠ 0 := by linarith
      rw [Finset.sum_range_succ, ih, sylvesterSeq_succ]
      push_cast
      field_simp
      ring

/-- The same identity over `ℝ`. -/
theorem sylvesterSeq_sum_inv_real (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / sylvesterSeq i = 1 - 1 / (sylvesterSeq n - 1) := by
  induction n with
  | zero => norm_num [sylvesterSeq]
  | succ n ih =>
      have h2 : (2 : ℤ) ≤ sylvesterSeq n := sylvesterSeq_two_le n
      have hq : (2 : ℝ) ≤ (sylvesterSeq n : ℝ) := by exact_mod_cast h2
      have h0 : (sylvesterSeq n : ℝ) ≠ 0 := by linarith
      have h1 : (sylvesterSeq n : ℝ) - 1 ≠ 0 := by linarith
      rw [Finset.sum_range_succ, ih, sylvesterSeq_succ]
      push_cast
      field_simp
      ring

/-- `1 = 1/2 + 1/3 + 1/7 + 1/43 + ⋯`. -/
theorem sylvesterSeq_hasSum_inv : HasSum (fun i ↦ (1 : ℝ) / sylvesterSeq i) 1 := by
  have hpos : ∀ i : ℕ, (2 : ℝ) ≤ (sylvesterSeq i : ℝ) := by
    intro i; exact_mod_cast sylvesterSeq_two_le i
  have hnn : ∀ i : ℕ, 0 ≤ (1 : ℝ) / sylvesterSeq i := by
    intro i
    have := hpos i
    positivity
  have hsummable : Summable (fun i ↦ (1 : ℝ) / sylvesterSeq i) := by
    refine summable_of_sum_range_le hnn (c := 1) ?_
    intro n
    rw [sylvesterSeq_sum_inv_real n]
    have h := hpos n
    have : 0 < (sylvesterSeq n : ℝ) - 1 := by linarith
    have : 0 < 1 / ((sylvesterSeq n : ℝ) - 1) := by positivity
    linarith
  have hlim : Filter.Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, (1 : ℝ) / sylvesterSeq i)
      Filter.atTop (nhds 1) := by
    have hz : Filter.Tendsto (fun n : ℕ ↦ 1 / ((sylvesterSeq n : ℝ) - 1))
        Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      · have h := hpos n
        have : 0 < (sylvesterSeq n : ℝ) - 1 := by linarith
        positivity
      · have hge : ((n : ℤ) : ℝ) + 2 ≤ (sylvesterSeq n : ℝ) := by
          exact_mod_cast sylvesterSeq_ge n
        have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have h2 : (n : ℝ) + 1 ≤ (sylvesterSeq n : ℝ) - 1 := by push_cast at hge ⊢; linarith
        exact one_div_le_one_div_of_le h1 h2
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ))).sub hz
    simp only [sub_zero] at this
    exact (Filter.tendsto_congr (fun n ↦ sylvesterSeq_sum_inv_real n)).mpr this
  have hs2 := hsummable.hasSum
  have heq : ∑' i, (1 : ℝ) / sylvesterSeq i = 1 :=
    tendsto_nhds_unique hs2.tendsto_sum_nat hlim
  rwa [heq] at hs2

/-- No term is a perfect square. -/
theorem sylvesterSeq_mod_four (n : ℕ) : sylvesterSeq n % 4 = 2 ∨ sylvesterSeq n % 4 = 3 := by
  induction n with
  | zero => norm_num [sylvesterSeq]
  | succ n ih =>
      rcases ih with h | h
      · obtain ⟨q, hq⟩ : ∃ q, sylvesterSeq n = 4 * q + 2 := ⟨sylvesterSeq n / 4, by omega⟩
        right
        have : sylvesterSeq (n + 1) = 4 * (4 * q ^ 2 + 3 * q) + 3 := by
          rw [sylvesterSeq_succ, hq]; ring
        omega
      · obtain ⟨q, hq⟩ : ∃ q, sylvesterSeq n = 4 * q + 3 := ⟨sylvesterSeq n / 4, by omega⟩
        right
        have : sylvesterSeq (n + 1) = 4 * (4 * q ^ 2 + 5 * q + 1) + 3 := by
          rw [sylvesterSeq_succ, hq]; ring
        omega

theorem sylvesterSeq_not_isSquare (n : ℕ) : ¬ IsSquare (sylvesterSeq n) := by
  rintro ⟨r, hr⟩
  have h4 : ∀ x : ZMod 4, x * x ≠ 2 ∧ x * x ≠ 3 := by decide
  rcases sylvesterSeq_mod_four n with h | h
  · obtain ⟨q, hq⟩ : ∃ q, sylvesterSeq n = 4 * q + 2 := ⟨sylvesterSeq n / 4, by omega⟩
    have : ((4 * q + 2 : ℤ) : ZMod 4) = ((r * r : ℤ) : ZMod 4) := by rw [← hq, hr]
    push_cast at this
    have h40 : (4 : ZMod 4) = 0 := by decide
    rw [h40] at this
    exact (h4 ((r : ZMod 4))).1 (by simpa using this.symm)
  · obtain ⟨q, hq⟩ : ∃ q, sylvesterSeq n = 4 * q + 3 := ⟨sylvesterSeq n / 4, by omega⟩
    have : ((4 * q + 3 : ℤ) : ZMod 4) = ((r * r : ℤ) : ZMod 4) := by rw [← hq, hr]
    push_cast at this
    have h40 : (4 : ZMod 4) = 0 := by decide
    rw [h40] at this
    exact (h4 ((r : ZMod 4))).2 (by simpa using this.symm)

private theorem neg_three_isSquare_two : IsSquare (-3 : ZMod 2) := ⟨1, by decide⟩

/-- Every prime factor has `−3` as a quadratic residue. -/
theorem sylvesterSeq_neg_three_isSquare {p : ℕ} [Fact p.Prime] {n : ℕ}
    (hp : (p : ℤ) ∣ sylvesterSeq n) : IsSquare (-3 : ZMod p) := by
  cases n with
  | zero =>
      have h2 : p ∣ 2 := by
        have : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by simpa [sylvesterSeq] using hp
        exact_mod_cast this
      have hp2 : p = 2 := ((Nat.prime_two).eq_one_or_self_of_dvd p h2).resolve_left
        (Fact.out (p := p.Prime)).one_lt.ne'
      subst hp2
      exact neg_three_isSquare_two
  | succ m =>
      refine ⟨((2 * sylvesterSeq m - 1 : ℤ) : ZMod p), ?_⟩
      have key : (4 : ℤ) * sylvesterSeq (m + 1) = (2 * sylvesterSeq m - 1) ^ 2 + 3 := by
        rw [sylvesterSeq_succ]; ring
      have hz : ((sylvesterSeq (m + 1) : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp
      have h4 : (((4 : ℤ) * sylvesterSeq (m + 1) : ℤ) : ZMod p) = 0 := by
        push_cast; rw [hz]; ring
      rw [key] at h4
      push_cast at h4
      push_cast
      linear_combination -h4

/-- Wilson (2004): `a(k)² + 1 ∣ a(k+1)² + 1`. -/
theorem sylvesterSeq_sq_add_one_dvd (k : ℕ) :
    sylvesterSeq k ^ 2 + 1 ∣ sylvesterSeq (k + 1) ^ 2 + 1 :=
  ⟨sylvesterSeq k ^ 2 - 2 * sylvesterSeq k + 2, by rw [sylvesterSeq_succ]; ring⟩

/-- `a(n) + a(n+1) ∣ a(n) a(n+1) − 1`. -/
theorem sylvesterSeq_add_dvd (n : ℕ) :
    sylvesterSeq n + sylvesterSeq (n + 1) ∣ sylvesterSeq n * sylvesterSeq (n + 1) - 1 :=
  ⟨sylvesterSeq n - 1, by rw [sylvesterSeq_succ]; ring⟩

/-- Bala (2026): `a(n+2) − a(n+1) = a(n)² (a(n+1) − a(n))`. -/
theorem sylvesterSeq_sub_succ (n : ℕ) :
    sylvesterSeq (n + 2) - sylvesterSeq (n + 1) =
      sylvesterSeq n ^ 2 * (sylvesterSeq (n + 1) - sylvesterSeq n) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, sylvesterSeq_succ, sylvesterSeq_succ]
  ring

private theorem syl_modEq_step {m x y : ℤ} (h : x ≡ y [ZMOD m]) :
    x ^ 2 - x + 1 ≡ y ^ 2 - y + 1 [ZMOD m] :=
  ((h.pow 2).sub h).add_right 1

/-- Israel (2015): for `n ≥ 4`, `a(n) mod 3000` alternates `1807, 2443`. -/
theorem sylvesterSeq_mod_3000 (n : ℕ) :
    sylvesterSeq (2 * n + 4) % 3000 = 1807 ∧ sylvesterSeq (2 * n + 5) % 3000 = 2443 := by
  have key : ∀ n : ℕ, sylvesterSeq (2 * n + 4) ≡ 1807 [ZMOD 3000] ∧
      sylvesterSeq (2 * n + 5) ≡ 2443 [ZMOD 3000] := by
    intro n
    induction n with
    | zero => constructor <;> decide
    | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        have e1 : 2 * (n + 1) + 4 = (2 * n + 5) + 1 := by ring
        have e2 : 2 * (n + 1) + 5 = (2 * (n + 1) + 4) + 1 := by ring
        have s1 : sylvesterSeq (2 * (n + 1) + 4) ≡ 1807 [ZMOD 3000] := by
          rw [e1, sylvesterSeq_succ]
          exact (syl_modEq_step h2).trans (by decide)
        refine ⟨s1, ?_⟩
        rw [e2, sylvesterSeq_succ]
        exact (syl_modEq_step s1).trans (by decide)
  obtain ⟨h1, h2⟩ := key n
  exact ⟨h1, h2⟩

/-- Murthy (2003), in offset-0 form: `a(2n+4) ≡ 807`, `a(2n+5) ≡ 443 (mod 1000)`. -/
theorem sylvesterSeq_mod_1000 (n : ℕ) :
    sylvesterSeq (2 * n + 4) % 1000 = 807 ∧ sylvesterSeq (2 * n + 5) % 1000 = 443 := by
  obtain ⟨h1, h2⟩ := sylvesterSeq_mod_3000 n
  have d : (1000 : ℤ) ∣ 3000 := ⟨3, by norm_num⟩
  constructor
  · have := Int.emod_emod_of_dvd (sylvesterSeq (2 * n + 4)) d
    rw [h1] at this; omega
  · have := Int.emod_emod_of_dvd (sylvesterSeq (2 * n + 5)) d
    rw [h2] at this; omega

/-- The 24-term progression modulo 864: `a(n+2) ≡ 7 + 36 n`. -/
theorem sylvesterSeq_mod_864 (n : ℕ) :
    sylvesterSeq (n + 2) % 864 = (7 + 36 * n) % 864 := by
  have key : ∀ n : ℕ, sylvesterSeq (n + 2) ≡ 7 + 36 * (n : ℤ) [ZMOD 864] := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        have e : n + 1 + 2 = (n + 2) + 1 := by ring
        rw [e, sylvesterSeq_succ]
        refine (syl_modEq_step ih).trans ?_
        have hdvd : (864 : ℤ) ∣ ((7 + 36 * (n : ℤ)) ^ 2 - (7 + 36 * (n : ℤ)) + 1)
            - (7 + 36 * ((n : ℤ) + 1)) := by
          have e2 : ((7 + 36 * (n : ℤ)) ^ 2 - (7 + 36 * (n : ℤ)) + 1)
              - (7 + 36 * ((n : ℤ) + 1)) = 432 * ((n : ℤ) * (1 + 3 * (n : ℤ))) := by ring
          rw [e2]
          rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
          · refine ⟨(k : ℤ) * (1 + 6 * (k : ℤ)), ?_⟩
            subst hk; push_cast; ring
          · refine ⟨(2 * (k : ℤ) + 1) * (3 * (k : ℤ) + 2), ?_⟩
            subst hk; push_cast; ring
        have hmod : ((7 + 36 * (n : ℤ)) ^ 2 - (7 + 36 * (n : ℤ)) + 1)
            ≡ 7 + 36 * ((n : ℤ) + 1) [ZMOD 864] :=
          Int.ModEq.symm (Int.modEq_iff_dvd.mpr hdvd)
        push_cast
        exact hmod
  have := key n
  simpa [Int.ModEq] using this

/-- Bala (2026): `n ↦ a(n+k) − a(k)` is a strong divisibility sequence. -/
theorem sylvesterSeq_sub_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ sylvesterSeq (n + k) - sylvesterSeq k) :=
  isStrongDivSeq_sub Ps sylvesterSeq sylvesterSeq_iter k

/-- **Mohanty**: `b(n+1) = b(n)² − m b(n) + m` with `m > 0` coprime to `b(0)` is pairwise
coprime.  (Sylvester's sequence is `m = 1`, `b(0) = 2`.) -/
theorem mohanty_coprime (m : ℤ) (hm : 0 < m) (b : ℕ → ℤ) (hb0 : IsCoprime m (b 0))
    (hb : ∀ n, b (n + 1) = b n ^ 2 - m * b n + m) {i j : ℕ} (hij : i ≠ j) :
    IsCoprime (b i) (b j) := by
  have copm : ∀ n, IsCoprime m (b n) := by
    intro n
    induction n with
    | zero => exact hb0
    | succ n ih =>
        have h := (ih.pow_right (n := 2)).add_mul_left_right (1 - b n)
        have e : b n ^ 2 - m * b n + m = b n ^ 2 + m * (1 - b n) := by ring
        rw [hb n, e]
        exact h
  have bdvd : ∀ i j : ℕ, i < j → b i ∣ b j - m := by
    intro i j hij
    obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
    induction d with
    | zero => exact ⟨b i - m, by rw [hb i]; ring⟩
    | succ d ih =>
        have e : i + 1 + (d + 1) = (i + 1 + d) + 1 := by ring
        rw [e, hb (i + 1 + d)]
        have : b (i + 1 + d) ^ 2 - m * b (i + 1 + d) + m - m
            = b (i + 1 + d) * (b (i + 1 + d) - m) := by ring
        rw [this]
        exact (ih (by omega)).mul_left _
  have key : ∀ a c : ℕ, a < c → IsCoprime (b a) (b c) := by
    intro a c hac
    rw [Int.isCoprime_iff_gcd_eq_one]
    rw [intGcd_congr_of_dvd_sub (bdvd a c hac)]
    rw [Int.gcd_comm]
    exact (Int.isCoprime_iff_gcd_eq_one.mp (copm a))
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-! ## A003096: `a(n) = a(n−1)² − 1`, `a(0) = 2` -/

/-- **A003096**: `2, 3, 8, 63, 3968, …` -/
def a003096 : ℕ → ℤ
  | 0 => 2
  | n + 1 => a003096 n ^ 2 - 1

theorem a003096_succ (n : ℕ) : a003096 (n + 1) = a003096 n ^ 2 - 1 := rfl

theorem a003096_three_le (n : ℕ) : 3 ≤ a003096 (n + 1) := by
  induction n with
  | zero => norm_num [a003096]
  | succ n ih => rw [a003096_succ]; nlinarith

/-- Vos Post (2008): no term after `a(1)` is prime. -/
theorem a003096_not_prime (n : ℕ) (hn : 2 ≤ n) : ¬ Prime (a003096 n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro h
  have hge : 3 ≤ a003096 (m + 1) := a003096_three_le m
  have hfac : a003096 (m + 2) = (a003096 (m + 1) - 1) * (a003096 (m + 1) + 1) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, a003096_succ]; ring
  rcases h.irreducible.isUnit_or_isUnit hfac with hu | hu <;>
    rw [Int.isUnit_iff] at hu <;> omega

/-- Each term is coprime to its successor. -/
theorem a003096_coprime_succ (n : ℕ) : IsCoprime (a003096 n) (a003096 (n + 1)) :=
  ⟨a003096 n, -1, by rw [a003096_succ]; ring⟩

/-! ## A002065: `a(n+1) = a(n)² + a(n) + 1`, `a(0) = 0` -/

/-- **A002065**: `0, 1, 3, 13, 183, …` -/
def a002065 : ℕ → ℤ
  | 0 => 0
  | n + 1 => a002065 n ^ 2 + a002065 n + 1

private noncomputable def Pb : ℤ[X] := X ^ 2 + X + C 1

private theorem a002065_iter (n : ℕ) : a002065 (n + 1) = Pb.eval (a002065 n) := by
  simp [Pb, a002065]

/-- A002065 is a strong divisibility sequence (the entry says divisibility sequence). -/
theorem a002065_isStrongDivSeq : IsStrongDivSeq a002065 :=
  isStrongDivSeq_of_iterate Pb a002065 rfl a002065_iter

/-! ## A004019: `a(n) = (a(n−1) + 1)²`, `a(0) = 0` -/

/-- **A004019**: `0, 1, 4, 25, 676, …` -/
def a004019 : ℕ → ℤ
  | 0 => 0
  | n + 1 => (a004019 n + 1) ^ 2

private noncomputable def Pc : ℤ[X] := (X + C 1) ^ 2

private theorem a004019_iter (n : ℕ) : a004019 (n + 1) = Pc.eval (a004019 n) := by
  simp [Pc, a004019]

/-- `a(n) = A003095(n)²`. -/
theorem a004019_eq_sq (n : ℕ) : a004019 n = a003095 n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (a004019 n + 1) ^ 2 = a003095 (n + 1) ^ 2
      rw [ih, show a003095 (n + 1) = a003095 n ^ 2 + 1 from rfl]

/-- `a(n) = A003095(n+1) − 1`. -/
theorem a004019_eq_sub_one (n : ℕ) : a004019 n = a003095 (n + 1) - 1 := by
  rw [a004019_eq_sq, show a003095 (n + 1) = a003095 n ^ 2 + 1 from rfl]
  ring

/-- Bala (2026): A004019 is a strong divisibility sequence. -/
theorem a004019_isStrongDivSeq : IsStrongDivSeq a004019 :=
  isStrongDivSeq_of_iterate Pc a004019 rfl a004019_iter

/-- Bala (2026): `n ↦ a(n+k) − a(k)` is a strong divisibility sequence. -/
theorem a004019_sub_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ a004019 (n + k) - a004019 k) :=
  isStrongDivSeq_sub Pc a004019 a004019_iter k

end LeanFormalizations.PolyIteration
