/-
# Saito §3 for a general exponent `c`: the Matomäki richness machinery

The `c`-general analogue of the `Rich` / `saito_lemma38` section of `Mills/Irrational.lean`.

`RichC c d₁ q` says the window `[qᶜ, qᶜ + q^(c−1)]` above the `c`-th power of `q` is prime-rich.
`saito_lemma38C` is Saito's Lemma 3.8: a prime-rich window `[X, X + X^η]` contains a prime `q`
whose own window is again rich.  That is exactly the inductive step of the chain in Lemma 3.6.

Two exponents appear and must not be confused:

* the **inner** exponent `γ = 1 − 1/c`, which is what Matomäki's theorem is instantiated at
  (`(qᶜ)^γ = q^(c−1)`), and for which `2/3 − γ ≤ 0` as soon as `c ≥ 3` — this is why the
  Matomäki count collapses to the bare constant `D`;
* the **outer** exponent `η ∈ [1/2, 1 − 1/c]`, free, taken to be `21/40` when the window is
  supplied by Baker–Harman–Pintz and `1 − 1/c` when it is supplied by a previous chain step.

At `c = 3` the two coincide (`γ = 2/3`), which is why `Irrational.lean` could use a single `2/3`.
-/
import Mathlib
import LeanFormalizations.NumberTheory.Mills.Schoenfeld
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-! ### Elementary `(x+1)ᶜ` expansions -/

/-- `(x+1)^(d+2) ≥ x^(d+2) + 2x^(d+1) + x^d` for `x ≥ 0`: the two leading binomial terms plus
one more, obtained without the binomial theorem by splitting off `(x+1)²`. -/
theorem pow_add_two_ge_real {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    x ^ (d + 2) + 2 * x ^ (d + 1) + x ^ d ≤ (x + 1) ^ (d + 2) := by
  have h1 : x ^ d ≤ (x + 1) ^ d := pow_le_pow_left₀ hx (by linarith) d
  have h2 : (0:ℝ) ≤ (x + 1) ^ 2 := by positivity
  have h3 : x ^ d * (x + 1) ^ 2 ≤ (x + 1) ^ d * (x + 1) ^ 2 := by
    exact mul_le_mul_of_nonneg_right h1 h2
  calc x ^ (d + 2) + 2 * x ^ (d + 1) + x ^ d = x ^ d * (x + 1) ^ 2 := by ring
    _ ≤ (x + 1) ^ d * (x + 1) ^ 2 := h3
    _ = (x + 1) ^ (d + 2) := by ring

/-- The `ℕ` form of `pow_add_two_ge_real`. -/
theorem pow_add_two_ge_nat (u d : ℕ) :
    u ^ (d + 2) + 2 * u ^ (d + 1) + u ^ d ≤ (u + 1) ^ (d + 2) := by
  have h : ((u ^ (d + 2) + 2 * u ^ (d + 1) + u ^ d : ℕ) : ℝ) ≤ (((u + 1) ^ (d + 2) : ℕ) : ℝ) := by
    push_cast
    exact pow_add_two_ge_real (by positivity) d
  exact_mod_cast h

/-! ### The inner exponent -/

/-- Saito's inner exponent `γ = 1 − 1/c`. -/
noncomputable def etaC (c : ℕ) : ℝ := 1 - 1 / (c : ℝ)

theorem etaC_mem_Icc {c : ℕ} (hc : 3 ≤ c) : etaC c ∈ Set.Icc (1/2 : ℝ) 1 := by
  have hc3 : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  have hcpos : (0:ℝ) < (c:ℝ) := by linarith
  constructor
  · have h : 1/(c:ℝ) ≤ 1/3 := by
      rw [div_le_div_iff₀ hcpos (by norm_num)]; linarith
    rw [etaC]; linarith
  · rw [etaC]; have : (0:ℝ) < 1 / (c:ℝ) := by positivity
    linarith

theorem etaC_le_one {c : ℕ} (hc : 3 ≤ c) : etaC c ≤ 1 := (etaC_mem_Icc hc).2

theorem two_thirds_sub_etaC_nonpos {c : ℕ} (hc : 3 ≤ c) : (2:ℝ)/3 - etaC c ≤ 0 := by
  have hc3 : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  have hcpos : (0:ℝ) < (c:ℝ) := by linarith
  have h : 1 / (c:ℝ) ≤ 1/3 := by
    rw [div_le_div_iff₀ hcpos (by norm_num)]; linarith
  rw [etaC]; linarith

/-- `(qᶜ)^γ = q^(c−1)` with `γ = 1 − 1/c`, the identity that makes Matomäki's window the same
window as `RichC`'s. -/
theorem rpow_pow_etaC {c : ℕ} (hc : 3 ≤ c) {q : ℝ} (hq : 0 < q) :
    (q ^ c) ^ etaC c = q ^ ((c:ℝ) - 1) := by
  have hcpos : (0:ℝ) < (c:ℝ) := by
    have : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    linarith
  rw [← Real.rpow_natCast q c, ← Real.rpow_mul hq.le, etaC]
  congr 1
  field_simp

/-- `q^((c:ℝ) − 1) = q^(c − 1 : ℕ)`: the bridge from the analytic to the arithmetic side. -/
theorem rpow_sub_one_eq_pow {c : ℕ} (hc : 1 ≤ c) {q : ℝ} (_hq : 0 < q) :
    q ^ ((c:ℝ) - 1) = q ^ (c - 1) := by
  rw [← Real.rpow_natCast q (c - 1)]
  congr 1
  have : ((c - 1 : ℕ) : ℝ) = (c:ℝ) - 1 := by
    have := Nat.cast_sub (R := ℝ) hc
    simpa using this
  rw [this]

/-! ### Richness -/

/-- Matomäki's richness condition at a prime `q` for exponent `c` (Saito (3.14)): the interval
`[qᶜ, qᶜ + q^(c−1)]` contains at least `d₁ q^(c−1) / log qᶜ` primes. -/
def RichC (c : ℕ) (d₁ : ℝ) (q : ℕ) : Prop :=
  d₁ * (q:ℝ) ^ ((c:ℝ) - 1) / Real.log ((q:ℝ) ^ c) ≤
    (primesIn ((q:ℝ) ^ c) ((q:ℝ) ^ c + (q:ℝ) ^ ((c:ℝ) - 1)) : ℝ)

/-! ### `(1 + 1/(2c))ᶜ ≤ 17/10` -/

theorem exp_half_lt : Real.exp (1/2) < 17/10 := by
  have hsq : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp (1/2) := Real.exp_pos _
  nlinarith [hsq, h1, hpos]

theorem one_add_pow_le {c : ℕ} (hc : 3 ≤ c) :
    (1 + 1/(2*(c:ℝ))) ^ c ≤ 17/10 := by
  have hc3 : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  have hcpos : (0:ℝ) < (c:ℝ) := by linarith
  have hb : (1 + 1/(2*(c:ℝ))) ≤ Real.exp (1/(2*(c:ℝ))) := by
    have := Real.add_one_le_exp (1/(2*(c:ℝ)))
    linarith
  have hnn : (0:ℝ) ≤ 1 + 1/(2*(c:ℝ)) := by positivity
  have h1 : (1 + 1/(2*(c:ℝ))) ^ c ≤ (Real.exp (1/(2*(c:ℝ)))) ^ c :=
    pow_le_pow_left₀ hnn hb c
  have h2 : (Real.exp (1/(2*(c:ℝ)))) ^ c = Real.exp (1/2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [h2] at h1
  exact le_trans h1 exp_half_lt.le

/-! ### Saito Lemma 3.8 for exponent `c` -/

/-- **Saito Lemma 3.8** for a general exponent `c ≥ 3`, `E = c`, `ε = 1/4`.  A prime-rich window
`[X, X + X^η]` with `η ∈ [1/2, 1 − 1/c]` contains a prime `q` whose own window
`[qᶜ, qᶜ + q^(c−1)]` is itself prime-rich.

Proof (Saito §3): if every prime `q` of the window had few primes in `[qᶜ, qᶜ + q^(c−1)]`, those
windows — pairwise disjoint, since `q' ≥ q + 1` forces `q'ᶜ ≥ qᶜ + 2q^(c−1) + q^(c−2)` — would be
more than the `D (Xᶜ)^(2/3 − γ) ≤ D` that Matomäki's Theorem 3.7 allows inside `[Xᶜ, 2Xᶜ]`,
because `d₂ X^η / log X > D` for large `X`. -/
theorem saito_lemma38C (hM : Matomaki2007) {c : ℕ} (hc : 3 ≤ c) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ d₁ < 1 ∧ ∀ d₂ > (0:ℝ), ∃ X₀ : ℝ, ∀ X ≥ X₀,
      ∀ η ∈ Set.Icc (1/2 : ℝ) (etaC c),
        d₂ * X ^ η / Real.log X ≤ (primesIn X (X + X ^ η) : ℝ) →
        ∃ q : ℕ, q.Prime ∧ X ≤ (q:ℝ) ∧ (q:ℝ) ≤ X + X ^ η ∧ RichC c d₁ q := by
  obtain ⟨d₁, D, hd₁0, hd₁1, hD, Xm, hmat⟩ := hM
  refine ⟨d₁, hd₁0, hd₁1, fun d₂ hd₂ => ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, c = d + 2 := ⟨c - 2, by omega⟩
  have hc3 : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  have hcpos : (0:ℝ) < (c:ℝ) := by linarith
  refine ⟨max ((2*(c:ℝ)) ^ c) (max ((10:ℝ) ^ (4:ℕ)) (max Xm ((2 * D / d₂) ^ (4:ℕ) + 1))),
    fun X hX η hη hcount => ?_⟩
  have hXc2 : ((2*(c:ℝ)) ^ c) ≤ X := le_trans (le_max_left _ _) hX
  have hX4 : (10:ℝ) ^ (4:ℕ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX10000 : (10000:ℝ) ≤ X := by norm_num at hX4; linarith
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hXpos : (0:ℝ) < X := by linarith
  have hXm : Xm ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hXcc : (2 * D / d₂) ^ (4:ℕ) < X := by
    have := le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hX
    linarith
  by_contra hcon
  push Not at hcon
  -- the window sits inside `[X, (1 + 1/(2c)) X]`
  have hρ : (1:ℝ) + 1/(2*(c:ℝ)) ≤ 17/10 := by
    have : (0:ℝ) < 1/(2*(c:ℝ)) := by positivity
    have h2 : 1/(2*(c:ℝ)) ≤ 1/6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hXcroot : 2*(c:ℝ) ≤ X ^ (1/(c:ℝ)) := by
    have h1 : ((2*(c:ℝ)) ^ c) ^ (1/(c:ℝ)) = 2*(c:ℝ) := by
      rw [← Real.rpow_natCast (2*(c:ℝ)) c, ← Real.rpow_mul (by positivity)]
      rw [mul_one_div, div_self (by exact_mod_cast hcpos.ne'), Real.rpow_one]
    calc 2*(c:ℝ) = ((2*(c:ℝ)) ^ c) ^ (1/(c:ℝ)) := h1.symm
      _ ≤ X ^ (1/(c:ℝ)) := Real.rpow_le_rpow (by positivity) hXc2 (by positivity)
  have hηle : X ^ η ≤ X ^ (etaC c) := Real.rpow_le_rpow_of_exponent_le hX1 hη.2
  have hsplitc : X ^ (etaC c) * X ^ (1/(c:ℝ)) = X := by
    rw [← Real.rpow_add hXpos, etaC]; norm_num
  have hetapos : (0:ℝ) < X ^ (etaC c) := Real.rpow_pos_of_pos hXpos _
  have hXeta : X ^ (etaC c) ≤ X / (2*(c:ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    calc X ^ (etaC c) * (2*(c:ℝ)) ≤ X ^ (etaC c) * X ^ (1/(c:ℝ)) := by
          exact mul_le_mul_of_nonneg_left hXcroot hetapos.le
      _ = X := hsplitc
  have hXeta1 : X ^ η ≤ X / (2*(c:ℝ)) := le_trans hηle hXeta
  have hwin : X + X ^ η ≤ (1 + 1/(2*(c:ℝ))) * X := by
    have : X / (2*(c:ℝ)) = 1/(2*(c:ℝ)) * X := by field_simp
    rw [this] at hXeta1; linarith
  -- the primes in the window
  set R : Finset ℕ := (Finset.Icc ⌈X⌉₊ ⌊X + X ^ η⌋₊).filter Nat.Prime with hR
  have hRcard : (R.card : ℝ) = (primesIn X (X + X ^ η) : ℝ) := by rw [hR, primesIn]
  have hmem : ∀ q ∈ R, q.Prime ∧ X ≤ (q:ℝ) ∧ (q:ℝ) ≤ X + X ^ η := by
    intro q hq
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, hp⟩ := hq
    refine ⟨hp, le_trans (Nat.le_ceil X) (by exact_mod_cast h1),
      le_trans (by exact_mod_cast h2) (Nat.floor_le (by positivity))⟩
  -- transport to a `Finset ℝ` of `c`-th powers
  set S : Finset ℝ := R.image (fun q : ℕ => (q:ℝ) ^ c) with hS
  have hinj : Set.InjOn (fun q : ℕ => (q:ℝ) ^ c) R := by
    intro q _ q' _ h
    simp only at h
    have hn : q ^ c = q' ^ c := by
      have : ((q ^ c : ℕ) : ℝ) = ((q' ^ c : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact Nat.pow_left_injective (by omega) hn
  have hScard : S.card = R.card := Finset.card_image_of_injOn hinj
  have hSmem : ∀ n ∈ S, ∃ q ∈ R, (q:ℝ) ^ c = n := by
    intro n hn
    rw [hS, Finset.mem_image] at hn
    obtain ⟨q, hqR, hqn⟩ := hn
    exact ⟨q, hqR, hqn⟩
  -- Matomäki's three hypotheses at `x = Xᶜ`, `γ = 1 − 1/c`
  have hbound : ∀ n ∈ S, X ^ c ≤ n ∧ n + n ^ (etaC c) ≤ 2 * X ^ c := by
    intro n hn
    obtain ⟨q, hqR, rfl⟩ := hSmem n hn
    obtain ⟨hp, hXq, hqX⟩ := hmem q hqR
    have hq0 : (0:ℝ) < (q:ℝ) := by linarith
    have hqX20 : (20:ℝ) ≤ (q:ℝ) := by linarith
    rw [rpow_pow_etaC hc hq0]
    refine ⟨pow_le_pow_left₀ (by linarith) hXq c, ?_⟩
    -- `qᶜ ≤ (17/10) Xᶜ`
    have hqρ : (q:ℝ) ≤ (1 + 1/(2*(c:ℝ))) * X := le_trans hqX hwin
    have hXcpos : (0:ℝ) < X ^ c := by positivity
    have hq17 : (q:ℝ) ^ c ≤ 17/10 * X ^ c := by
      calc (q:ℝ) ^ c ≤ ((1 + 1/(2*(c:ℝ))) * X) ^ c := pow_le_pow_left₀ hq0.le hqρ c
        _ = (1 + 1/(2*(c:ℝ))) ^ c * X ^ c := by rw [mul_pow]
        _ ≤ 17/10 * X ^ c := by
            exact mul_le_mul_of_nonneg_right (one_add_pow_le hc) hXcpos.le
    -- `q^(c−1) = qᶜ / q ≤ (17/10) Xᶜ / 20`
    have hqdiv : (q:ℝ) ^ ((c:ℝ) - 1) = (q:ℝ) ^ c / (q:ℝ) := by
      rw [Real.rpow_sub hq0, Real.rpow_one, Real.rpow_natCast]
    rw [hqdiv]
    have hsmall : (q:ℝ) ^ c / (q:ℝ) ≤ (17/10 * X ^ c) / 20 := by
      have hXcnn : (0:ℝ) ≤ 17/10 * X ^ c := by positivity
      rw [div_le_div_iff₀ hq0 (by norm_num)]
      nlinarith [hq17, hqX20, hXcnn]
    linarith
  have hdisj : (S : Set ℝ).PairwiseDisjoint (fun n => Set.Icc n (n + n ^ (etaC c))) := by
    have key : ∀ u v : ℕ, u ∈ R → v ∈ R → u < v →
        Disjoint (Set.Icc ((u:ℝ) ^ c) ((u:ℝ) ^ c + ((u:ℝ) ^ c) ^ (etaC c)))
          (Set.Icc ((v:ℝ) ^ c) ((v:ℝ) ^ c + ((v:ℝ) ^ c) ^ (etaC c))) := by
      intro u v huR hvR huv
      obtain ⟨hup, hXu, _⟩ := hmem u huR
      obtain ⟨hvp, hXv, _⟩ := hmem v hvR
      have hu0 : (0:ℝ) < (u:ℝ) := by linarith
      have hv0 : (0:ℝ) < (v:ℝ) := by linarith
      rw [rpow_pow_etaC hc hu0, rpow_pow_etaC hc hv0,
        rpow_sub_one_eq_pow (by omega) hu0, Set.disjoint_left]
      intro x hx hx'
      have huv1 : (u:ℝ) + 1 ≤ (v:ℝ) := by exact_mod_cast (by omega : u + 1 ≤ v)
      have hgap : (u:ℝ) ^ c + (u:ℝ) ^ (c - 1) < (v:ℝ) ^ c := by
        have h1 : ((u:ℝ) + 1) ^ c ≤ (v:ℝ) ^ c := pow_le_pow_left₀ (by linarith) huv1 c
        have h2 := pow_add_two_ge_real (x := (u:ℝ)) hu0.le d
        rw [← hd] at h2
        have hd1 : c - 1 = d + 1 := by omega
        have hd0 : (0:ℝ) < (u:ℝ) ^ d := by positivity
        have hd1' : (0:ℝ) < (u:ℝ) ^ (d+1) := by positivity
        rw [hd1]
        linarith
      linarith [hx.2, hx'.1]
    intro a ha b hb hab
    rw [hS] at ha hb
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨u, huR, rfl⟩ := ha
    obtain ⟨v, hvR, rfl⟩ := hb
    have hne : u ≠ v := by
      intro h; rw [h] at hab; exact hab rfl
    rcases lt_or_gt_of_ne hne with h | h
    · exact key u v huR hvR h
    · exact (key v u hvR huR h).symm
  have hpoorS : ∀ n ∈ S,
      (primesIn n (n + n ^ (etaC c)) : ℝ) ≤ d₁ * n ^ (etaC c) / Real.log n := by
    intro n hn
    obtain ⟨q, hqR, rfl⟩ := hSmem n hn
    obtain ⟨hp, hXq, hqX⟩ := hmem q hqR
    have hq0 : (0:ℝ) < (q:ℝ) := by linarith
    rw [rpow_pow_etaC hc hq0]
    have hnr := hcon q hp hXq hqX
    unfold RichC at hnr
    exact le_of_lt (not_le.1 hnr)
  -- Matomäki caps the count by `D`
  have hXcube : Xm ≤ X ^ c := by
    refine le_trans hXm ?_
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ c := pow_le_pow_right₀ hX1 (by omega)
  have hfin := hmat (X ^ c) hXcube (etaC c) (etaC_mem_Icc hc) S hbound hdisj hpoorS
  have hXcone : (1:ℝ) ≤ X ^ c := one_le_pow₀ hX1
  have hcap : (X ^ c) ^ ((2:ℝ)/3 - etaC c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hXcone (two_thirds_sub_etaC_nonpos hc)
  have hfin' : (S.card : ℝ) ≤ D := by
    refine le_trans hfin ?_
    calc D * (X ^ c) ^ ((2:ℝ)/3 - etaC c) ≤ D * 1 :=
          mul_le_mul_of_nonneg_left hcap hD.le
      _ = D := by ring
  rw [hScard] at hfin'
  -- but the hypothesis forces the count above `D`
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog : Real.log X < 2 * X ^ ((1:ℝ)/4) := log_lt_two_rpow hX1
  have hηge : X ^ ((1:ℝ)/2) ≤ X ^ η := Real.rpow_le_rpow_of_exponent_le hX1 hη.1
  have hsplit2 : X ^ ((1:ℝ)/2) = X ^ ((1:ℝ)/4) * X ^ ((1:ℝ)/4) := by
    rw [← Real.rpow_add hXpos]; norm_num
  have hc0 : (0:ℝ) < 2 * D / d₂ := by positivity
  have hc4 : 2 * D / d₂ < X ^ ((1:ℝ)/4) := by
    have h1 : ((2 * D / d₂) ^ (4:ℕ)) ^ ((1:ℝ)/4) = 2 * D / d₂ := by
      rw [← Real.rpow_natCast (2 * D / d₂) 4, ← Real.rpow_mul hc0.le]
      norm_num
    calc 2 * D / d₂ = ((2 * D / d₂) ^ (4:ℕ)) ^ ((1:ℝ)/4) := h1.symm
      _ < X ^ ((1:ℝ)/4) := Real.rpow_lt_rpow (by positivity) hXcc (by norm_num)
  have h14pos : (0:ℝ) < X ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hXpos _
  have h2D : 2 * D ≤ d₂ * X ^ ((1:ℝ)/4) := by
    rw [div_lt_iff₀ hd₂] at hc4
    linarith
  have hbig : D < d₂ * X ^ η / Real.log X := by
    rw [lt_div_iff₀ hlogpos]
    calc D * Real.log X < D * (2 * X ^ ((1:ℝ)/4)) := mul_lt_mul_of_pos_left hlog hD
      _ ≤ d₂ * X ^ ((1:ℝ)/2) := by rw [hsplit2]; nlinarith [h2D, h14pos]
      _ ≤ d₂ * X ^ η := mul_le_mul_of_nonneg_left hηge hd₂.le
  rw [← hRcard] at hcount
  linarith [hcount, hfin', hbig]

end LeanFormalizations.Mills
