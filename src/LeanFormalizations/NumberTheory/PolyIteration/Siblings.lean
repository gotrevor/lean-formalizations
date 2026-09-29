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
theorem sub_dvd_sub_add (n k j : ℕ) : u (n + k) - u n ∣ u (n + k + j) - u (n + j) := by
  sorry

/-- `u(n) − u(k) ∣ u(r n + s k) − u(s n + r k)`. -/
theorem sub_dvd_sub_lin (n k r s : ℕ) :
    u n - u k ∣ u (r * n + s * k) - u (s * n + r * k) := by
  sorry

/-- `u(n) − u(k) ∣ u(m n) − u(m k)` (Bala's `u(n) ≠ u(k)` proviso is not needed). -/
theorem sub_dvd_sub_mul (n k m : ℕ) : u n - u k ∣ u (m * n) - u (m * k) := by
  sorry

/-- `u(n) − u(k) ∣ u(r n) u(s k) − u(r k) u(s n)`. -/
theorem sub_dvd_det (n k r s : ℕ) :
    u n - u k ∣ u (r * n) * u (s * k) - u (r * k) * u (s * n) := by
  sorry

end General

/-! ## A000058, Sylvester's sequence -/

/-- **A000058**: `2, 3, 7, 43, 1807, …`, `a(n+1) = a(n)² − a(n) + 1`. -/
def sylvesterSeq : ℕ → ℤ
  | 0 => 2
  | n + 1 => sylvesterSeq n ^ 2 - sylvesterSeq n + 1

/-- Euclid numbers: `a(n) = 1 + a(0) a(1) ⋯ a(n−1)`. -/
theorem sylvesterSeq_eq_prod_add_one (n : ℕ) :
    sylvesterSeq n = (∏ i ∈ Finset.range n, sylvesterSeq i) + 1 := by
  sorry

/-- The terms are pairwise coprime. -/
theorem sylvesterSeq_coprime {i j : ℕ} (hij : i ≠ j) :
    IsCoprime (sylvesterSeq i) (sylvesterSeq j) := by
  sorry

/-- The greedy Egyptian fraction, finite form: `Σ_{i<n} 1/a(i) = 1 − 1/(a(n) − 1)`. -/
theorem sylvesterSeq_sum_inv (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℚ) / sylvesterSeq i = 1 - 1 / (sylvesterSeq n - 1) := by
  sorry

/-- `1 = 1/2 + 1/3 + 1/7 + 1/43 + ⋯`. -/
theorem sylvesterSeq_hasSum_inv : HasSum (fun i ↦ (1 : ℝ) / sylvesterSeq i) 1 := by
  sorry

/-- No term is a perfect square. -/
theorem sylvesterSeq_not_isSquare (n : ℕ) : ¬ IsSquare (sylvesterSeq n) := by
  sorry

/-- Every prime factor has `−3` as a quadratic residue. -/
theorem sylvesterSeq_neg_three_isSquare {p : ℕ} [Fact p.Prime] {n : ℕ}
    (hp : (p : ℤ) ∣ sylvesterSeq n) : IsSquare (-3 : ZMod p) := by
  sorry

/-- Wilson (2004): `a(k)² + 1 ∣ a(k+1)² + 1`. -/
theorem sylvesterSeq_sq_add_one_dvd (k : ℕ) :
    sylvesterSeq k ^ 2 + 1 ∣ sylvesterSeq (k + 1) ^ 2 + 1 := by
  sorry

/-- `a(n) + a(n+1) ∣ a(n) a(n+1) − 1`. -/
theorem sylvesterSeq_add_dvd (n : ℕ) :
    sylvesterSeq n + sylvesterSeq (n + 1) ∣ sylvesterSeq n * sylvesterSeq (n + 1) - 1 := by
  sorry

/-- Bala (2026): `a(n+2) − a(n+1) = a(n)² (a(n+1) − a(n))`. -/
theorem sylvesterSeq_sub_succ (n : ℕ) :
    sylvesterSeq (n + 2) - sylvesterSeq (n + 1) =
      sylvesterSeq n ^ 2 * (sylvesterSeq (n + 1) - sylvesterSeq n) := by
  sorry

/-- Israel (2015): for `n ≥ 4`, `a(n) mod 3000` alternates `1807, 2443`. -/
theorem sylvesterSeq_mod_3000 (n : ℕ) :
    sylvesterSeq (2 * n + 4) % 3000 = 1807 ∧ sylvesterSeq (2 * n + 5) % 3000 = 2443 := by
  sorry

/-- Murthy (2003), in offset-0 form: `a(2n+4) ≡ 807`, `a(2n+5) ≡ 443 (mod 1000)`. -/
theorem sylvesterSeq_mod_1000 (n : ℕ) :
    sylvesterSeq (2 * n + 4) % 1000 = 807 ∧ sylvesterSeq (2 * n + 5) % 1000 = 443 := by
  sorry

/-- The 24-term progression modulo 864: `a(n+2) ≡ 7 + 36 n`. -/
theorem sylvesterSeq_mod_864 (n : ℕ) :
    sylvesterSeq (n + 2) % 864 = (7 + 36 * n) % 864 := by
  sorry

/-- Bala (2026): `n ↦ a(n+k) − a(k)` is a strong divisibility sequence. -/
theorem sylvesterSeq_sub_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ sylvesterSeq (n + k) - sylvesterSeq k) := by
  sorry

/-- **Mohanty**: `b(n+1) = b(n)² − m b(n) + m` with `m > 0` coprime to `b(0)` is pairwise
coprime.  (Sylvester's sequence is `m = 1`, `b(0) = 2`.) -/
theorem mohanty_coprime (m : ℤ) (hm : 0 < m) (b : ℕ → ℤ) (hb0 : IsCoprime m (b 0))
    (hb : ∀ n, b (n + 1) = b n ^ 2 - m * b n + m) {i j : ℕ} (hij : i ≠ j) :
    IsCoprime (b i) (b j) := by
  sorry

/-! ## A003096: `a(n) = a(n−1)² − 1`, `a(0) = 2` -/

/-- **A003096**: `2, 3, 8, 63, 3968, …` -/
def a003096 : ℕ → ℤ
  | 0 => 2
  | n + 1 => a003096 n ^ 2 - 1

/-- Vos Post (2008): no term after `a(1)` is prime. -/
theorem a003096_not_prime (n : ℕ) (hn : 2 ≤ n) : ¬ Prime (a003096 n) := by
  sorry

/-- Each term is coprime to its successor. -/
theorem a003096_coprime_succ (n : ℕ) : IsCoprime (a003096 n) (a003096 (n + 1)) := by
  sorry

/-! ## A002065: `a(n+1) = a(n)² + a(n) + 1`, `a(0) = 0` -/

/-- **A002065**: `0, 1, 3, 13, 183, …` -/
def a002065 : ℕ → ℤ
  | 0 => 0
  | n + 1 => a002065 n ^ 2 + a002065 n + 1

/-- A002065 is a strong divisibility sequence (the entry says divisibility sequence). -/
theorem a002065_isStrongDivSeq : IsStrongDivSeq a002065 := by
  sorry

/-! ## A004019: `a(n) = (a(n−1) + 1)²`, `a(0) = 0` -/

/-- **A004019**: `0, 1, 4, 25, 676, …` -/
def a004019 : ℕ → ℤ
  | 0 => 0
  | n + 1 => (a004019 n + 1) ^ 2

/-- `a(n) = A003095(n)²`. -/
theorem a004019_eq_sq (n : ℕ) : a004019 n = a003095 n ^ 2 := by
  sorry

/-- `a(n) = A003095(n+1) − 1`. -/
theorem a004019_eq_sub_one (n : ℕ) : a004019 n = a003095 (n + 1) - 1 := by
  sorry

/-- Bala (2026): A004019 is a strong divisibility sequence. -/
theorem a004019_isStrongDivSeq : IsStrongDivSeq a004019 := by
  sorry

/-- Bala (2026): `n ↦ a(n+k) − a(k)` is a strong divisibility sequence. -/
theorem a004019_sub_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ a004019 (n + k) - a004019 k) := by
  sorry

end LeanFormalizations.PolyIteration
