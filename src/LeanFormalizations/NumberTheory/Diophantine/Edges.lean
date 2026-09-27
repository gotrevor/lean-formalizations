/-
# Wiring edges between the Diophantine literature inputs

Each theorem derives one literature `Prop` from another, so the bedrock shrinks to fewer,
deeper assumptions.  Sources (local-only, gitignored): `papers/mahler-1957-fractional-parts-ii`,
`papers/ridout-1957-rational-approximations`, `papers/ridout-1958-p-adic-roth` (`.pdf`/`.txt`).

## `mahler_of_ridout1957` — Mahler (1957), §3, verbatim route

Let `α = u/v` in lowest terms, `u > v ≥ 2`; put `λ = log v / log u ∈ (0, 1)`, so `v = u^λ`.
Take `P` = prime factors of `v`, `Q` = prime factors of `u`, `ϑ = 1` (Ridout's `α`),
`μ = 1 − λ`, `ν = 0`, `c = 2`, and `κ = 1 − λ + ε'` for a small `ε' > 0` tied to `ε`
(Mahler's `κ` makes `(u/v)^n · u^(−κ n) = e^(−ε n)`, i.e. `κ = 1 − λ + ε / log u`).
For each `n` let `p* = round((u/v)^n)` (Mahler's "integer nearest to `ϑ(u/v)^n`"),
`p = p* vⁿ`, `q = uⁿ` (`q* = 1`).  For large `n`: `0 < p* < 2 (u/v)ⁿ = 2 v^(n(1−λ)/λ)`…
Mahler concludes `0 < p* ≤ c p^μ` (condition (4)).  `(u/v)ⁿ` is not an integer (`v ≥ 2`, coprime),
so `p/q ≠ 1`; Ridout's finiteness then says `|1 − p/q| ≥ q^(−κ)` for all but finitely many `n`,
i.e. `|(u/v)ⁿ − p*| ≥ (u/v)ⁿ u^(−κn) = e^(−εn)`.  ⚠️ Check Mahler's exponent bookkeeping in
the PDF (`papers/mahler-1957-fractional-parts-ii.pdf`, p. 123–124) rather than this sketch; the
text extraction dropped his displayed formulas, so render the page if needed.  Distinct `n`
give distinct `q = uⁿ`, so finitely many `(p, q)` means finitely many `n`.

## `ridoutSUnitDen_of_ridout1957`
`μ = 1`, `ν = 0`, `P = ∅`: `p* = p`, `q* = 1`, `q` an `S`-unit; exponent `1 + δ > 1`.  Reduce
the lowest-terms rational to a pair.  (`α` irrational ⇒ `α − p/q ≠ 0`.)

## `roth_of_ridout1958`
`t = 0` (no primes); `f` = the minimal polynomial of `α` scaled to `ℤ[X]` (degree `≥ 2` since `α`
is irrational).  For bounded `α`, `max(|h|, q) ≤ (|α| + 1) q` once `|α − h/q| < 1`, so
`|α − h/q| < q^(−(2+δ))` implies Ridout's inequality with `κ = 2 + δ/2` for large `q`.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Diophantine

open LeanFormalizations.Literature

/-- **Mahler (1957) from Ridout (1957)**, as in Mahler's §3.

Ridout is applied to the algebraic number `ϑ = 1` with `P` = the primes of `v`, `Q` = the primes
of `u`, `c = 2`, `ν = 0`, `μ = 1 − λ` and `κ = μ + ε/(2 log u)`, where `λ = log v / log u`.  The
approximation attached to a bad exponent `n` is `p = p* vⁿ`, `q = uⁿ` with `p* = round(αⁿ)`:

* `|1 − p/q| = (vⁿ/uⁿ)|αⁿ − p*| ≤ (v/u)ⁿ e^(−εn) < q^(−κ)`, because `vⁿ = u^(λn)` and
  `lu·κ = lu − lv + ε/2`, so the exponent inequality reduces to `−εn < −εn/2`;
* condition (4), `p* ≤ c p^μ`, reduces after taking logarithms to `λ log p* ≤ log 2 + (1−λ) n lv`,
  which follows from `p* ≤ 2αⁿ` and `λ lu = lv`;
* `p/q ≠ 1` because `vⁿ ∤ uⁿ` (`v ≥ 2`, `gcd(u,v) = 1`).

Distinct `n` give distinct `q = uⁿ`, so Ridout's finiteness bounds the set of bad `n`. -/
theorem mahler_of_ridout1957 (h : Ridout1957) : Mahler1957 := by
  intro α hα1 hden ε hε
  -- ### Setup: `α = u / v` in lowest terms, `u > v ≥ 2`.
  have hden0 : 0 < α.den := α.pos
  have hv2 : 2 ≤ α.den := by omega
  have hαR : (1:ℝ) < (α:ℝ) := by exact_mod_cast hα1
  have hnum : 0 < α.num := Rat.num_pos.mpr (lt_trans zero_lt_one hα1)
  set v : ℕ := α.den with hv_def
  set u : ℕ := α.num.natAbs with hu_def
  have hu : (u : ℤ) = α.num := Int.natAbs_of_nonneg hnum.le
  have hV0 : (0:ℝ) < (v:ℝ) := by exact_mod_cast hden0
  have hαuv : (α:ℝ) = (u:ℝ) / (v:ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast hu.symm
  have hUV : (v:ℝ) < (u:ℝ) := by
    rw [hαuv] at hαR
    exact (one_lt_div hV0).mp hαR
  have hu2 : 2 ≤ u := by
    have : (2:ℝ) ≤ (v:ℝ) := by exact_mod_cast hv2
    have : (2:ℝ) < (u:ℝ) := lt_of_le_of_lt this hUV
    have : (2:ℕ) < u := by exact_mod_cast this
    omega
  have hcop : Nat.Coprime u v := α.reduced
  have hU0 : (0:ℝ) < (u:ℝ) := by positivity
  -- logs
  -- `lu`, `lv`, `μ`, `κ` are introduced as *opaque* locals (not `set` bodies): with let-values
  -- in scope, `linarith`/`nlinarith` blow the `isDefEq` heartbeat budget unfolding them.
  obtain ⟨lu, hlu_def⟩ : ∃ x : ℝ, x = Real.log u := ⟨_, rfl⟩
  obtain ⟨lv, hlv_def⟩ : ∃ x : ℝ, x = Real.log v := ⟨_, rfl⟩
  have hlu : 0 < lu := by rw [hlu_def]; exact Real.log_pos (by exact_mod_cast hu2)
  have hlv : 0 < lv := by rw [hlv_def]; exact Real.log_pos (by exact_mod_cast hv2)
  have hlvu : lv < lu := by rw [hlu_def, hlv_def]; exact Real.log_lt_log hV0 hUV
  obtain ⟨μ, hμ_def⟩ : ∃ x : ℝ, x = 1 - lv / lu := ⟨_, rfl⟩
  obtain ⟨κ, hκ_def⟩ : ∃ x : ℝ, x = μ + ε / (2 * lu) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lv / lu := div_nonneg hlv.le hlu.le
  have hlam1 : lv / lu ≤ 1 := (div_le_one hlu).mpr hlvu.le
  have hμ0 : 0 ≤ μ := by rw [hμ_def]; linarith
  have hμ1 : μ ≤ 1 := by rw [hμ_def]; linarith
  have hεlu : 0 < ε / (2 * lu) := div_pos hε (by linarith)
  have hμκ : μ + 0 < κ := by rw [hκ_def]; linarith
  have hluκ : lu * κ = lu - lv + ε / 2 := by
    rw [hκ_def, hμ_def]; field_simp
  -- ### Ridout, applied with `ϑ = 1`
  have hfin := h 1 isAlgebraic_one one_ne_zero v.primeFactors u.primeFactors
    (fun r hr => Nat.prime_of_mem_primeFactors hr)
    (fun r hr => Nat.prime_of_mem_primeFactors hr)
    (Nat.Coprime.disjoint_primeFactors hcop.symm)
    μ 0 2 κ hμ0 hμ1 le_rfl zero_le_one two_pos hμκ
  set S := {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧
      (∃ ps a : ℕ, x.1 = ps * a ∧ (∀ r ∈ a.primeFactors, r ∈ v.primeFactors) ∧
        0 < ps ∧ (ps : ℝ) ≤ 2 * (x.1 : ℝ) ^ μ) ∧
      (∃ qs b : ℕ, x.2 = qs * b ∧ (∀ r ∈ b.primeFactors, r ∈ u.primeFactors) ∧
        0 < qs ∧ (qs : ℝ) ≤ 2 * (x.2 : ℝ) ^ (0:ℝ)) ∧
      0 < |(1:ℝ) - (x.1 : ℝ) / x.2| ∧ |(1:ℝ) - (x.1 : ℝ) / x.2| < 1 / (x.2 : ℝ) ^ κ} with hS_def
  have hSfin : S.Finite := hfin
  -- ### The map `n ↦ (p* vⁿ, uⁿ)`
  set f : ℕ → ℕ × ℕ :=
    fun n => ((round ((α:ℝ)^n)).toNat * v ^ n, u ^ n) with hf_def
  have hinj : Function.Injective f := by
    intro a b hab
    exact Nat.pow_right_injective hu2 (congrArg Prod.snd hab)
  set T : Set ℕ := {n : ℕ | 1 ≤ n ∧
      |(α:ℝ)^n - (round ((α:ℝ)^n) : ℝ)| ≤ Real.exp (-(ε * n))} with hT_def
  have hsub : T ⊆ f ⁻¹' S := by
    intro n hn
    obtain ⟨hn1, hnd⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    set A : ℝ := (α:ℝ) ^ n with hA_def
    have hA1 : 1 < A := one_lt_pow₀ hαR hn0
    have hA0 : 0 < A := by linarith
    have hAeq : A = (u:ℝ) ^ n / (v:ℝ) ^ n := by
      rw [hA_def, hαuv, div_pow]
    have hlogA : Real.log A = n * lu - n * lv := by
      rw [hlu_def, hlv_def, hA_def, Real.log_pow, hαuv,
        Real.log_div (by positivity) (by positivity)]
      ring
    set r : ℤ := round A with hr_def
    have habs : |A - (r:ℝ)| ≤ 1/2 := abs_sub_round A
    have habs' := abs_le.mp habs
    have hrR : (1:ℝ) ≤ (r:ℝ) := by
      by_contra hc
      push Not at hc
      have : (r:ℝ) ≤ 0 := by
        have : r < 1 := by exact_mod_cast hc
        have : r ≤ 0 := by omega
        exact_mod_cast this
      linarith [habs'.1]
    set P : ℕ := r.toNat with hP_def
    have hPz : (P : ℤ) = r := Int.toNat_of_nonneg (by exact_mod_cast le_trans zero_le_one hrR)
    have hPR : (P : ℝ) = (r:ℝ) := by exact_mod_cast hPz
    have hP1 : (1:ℝ) ≤ (P:ℝ) := by rw [hPR]; exact hrR
    have hP0 : 0 < P := by
      have : (0:ℝ) < (P:ℝ) := by linarith
      exact_mod_cast this
    -- `p* ≤ 2 A`
    have hP2A : (P:ℝ) ≤ 2 * A := by rw [hPR]; linarith [habs'.2]
    have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg hP1
    have hlogP : Real.log P ≤ Real.log 2 + (n * lu - n * lv) := by
      have := Real.log_le_log (by linarith) hP2A
      rwa [Real.log_mul two_ne_zero hA0.ne', hlogA] at this
    -- membership
    refine ⟨by positivity, by positivity, ⟨P, v ^ n, rfl, ?_, hP0, ?_⟩,
      ⟨1, u ^ n, (one_mul _).symm, ?_, one_pos, ?_⟩, ?_, ?_⟩
    · intro s hs
      rwa [Nat.primeFactors_pow _ hn0] at hs
    · -- `p* ≤ 2 (p* vⁿ)^μ`
      have hlogpv : Real.log ((P * v ^ n : ℕ) : ℝ) = Real.log P + n * lv := by
        rw [hlv_def]
        push_cast
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hgoal : Real.log P ≤ Real.log 2 + (Real.log P + (n:ℝ) * lv) * μ := by
        have f1 : lv / lu * Real.log P ≤ lv / lu * (Real.log 2 + ((n:ℝ) * lu - (n:ℝ) * lv)) :=
          mul_le_mul_of_nonneg_left hlogP hlam0
        have f2 : lv / lu * ((n:ℝ) * lu) = (n:ℝ) * lv := by
          field_simp [hlu.ne']
        have f3 : lv / lu * Real.log 2 ≤ Real.log 2 :=
          mul_le_of_le_one_left hlog2.le hlam1
        rw [hμ_def]
        nlinarith [f1, f2, f3]
      calc (P:ℝ) = Real.exp (Real.log P) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (Real.log 2 + (Real.log P + (n:ℝ) * lv) * μ) := Real.exp_le_exp.mpr hgoal
        _ = 2 * Real.exp ((Real.log P + (n:ℝ) * lv) * μ) := by
            rw [Real.exp_add, Real.exp_log two_pos]
        _ = 2 * ((P * v ^ n : ℕ) : ℝ) ^ μ := by
            rw [Real.rpow_def_of_pos (by positivity), hlogpv]
    · intro s hs
      rwa [Nat.primeFactors_pow _ hn0] at hs
    · rw [Real.rpow_zero]; norm_num
    · -- nonvanishing
      have hne : u ^ n ≠ P * v ^ n := by
        intro he
        have hdvd : v ^ n ∣ u ^ n := ⟨P, by rw [he]; ring⟩
        have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow n n hcop.symm) hdvd
        have hv1 : v = 1 := by
          rcases Nat.pow_eq_one.mp this with h1 | h1
          · exact h1
          · omega
        omega
      rw [abs_pos, sub_ne_zero]
      intro he
      have hq : ((u ^ n : ℕ) : ℝ) ≠ 0 := by positivity
      rw [eq_div_iff hq, one_mul] at he
      exact hne (by exact_mod_cast he)
    · -- the Ridout inequality
      have hsplit : (1:ℝ) - ((P * v ^ n : ℕ) : ℝ) / ((u ^ n : ℕ) : ℝ)
          = ((v:ℝ) ^ n / (u:ℝ) ^ n) * (A - (P:ℝ)) := by
        push_cast
        rw [hAeq]
        field_simp
      have hvu0 : (0:ℝ) < (v:ℝ) ^ n / (u:ℝ) ^ n := by positivity
      rw [hsplit, abs_mul, abs_of_pos hvu0]
      have hd : |A - (P:ℝ)| ≤ Real.exp (-(ε * n)) := by rw [hPR]; exact hnd
      have hstep1 : (v:ℝ) ^ n / (u:ℝ) ^ n * |A - (P:ℝ)|
          ≤ (v:ℝ) ^ n / (u:ℝ) ^ n * Real.exp (-(ε * n)) :=
        mul_le_mul_of_nonneg_left hd hvu0.le
      refine lt_of_le_of_lt hstep1 ?_
      -- rewrite everything as exponentials
      have hvn : (v:ℝ) ^ n = Real.exp (n * lv) := by
        rw [hlv_def, ← Real.log_pow, Real.exp_log (by positivity)]
      have hun : (u:ℝ) ^ n = Real.exp (n * lu) := by
        rw [hlu_def, ← Real.log_pow, Real.exp_log (by positivity)]
      have hrhs : ((u ^ n : ℕ) : ℝ) ^ κ = Real.exp (n * lu * κ) := by
        rw [hlu_def]
        push_cast
        rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
      rw [hrhs, hvn, hun, ← Real.exp_sub, ← Real.exp_add, one_div, ← Real.exp_neg,
        Real.exp_lt_exp]
      have hnκ : (n:ℝ) * lu * κ = (n:ℝ) * lu - (n:ℝ) * lv + (n:ℝ) * ε / 2 := by
        rw [mul_assoc, hluκ]; ring
      have hnpos : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le zero_lt_one hnR
      linarith only [hnκ, mul_pos hε hnpos]
  have hTfin : T.Finite := Set.Finite.subset (Set.Finite.preimage hinj.injOn hSfin) hsub
  obtain ⟨B, hB⟩ := hTfin.bddAbove
  refine ⟨B + 1, ?_⟩
  intro n hn
  by_contra hc
  push Not at hc
  have : n ∈ T := ⟨by omega, hc⟩
  have := hB this
  omega


/-- Ridout (1957) at `P = ∅`, `μ = 1`, `ν = 0`, `c = 1`, `κ = 1 + δ`, restricted to rationals
with positive numerator (Ridout's solutions are pairs of positive naturals).

`P = ∅` forces the numerator's restricted part to be `1`, so the numerator is unrestricted with
`p* = p ≤ 1 · p¹`; the denominator is an `S`-unit with `q* = 1 ≤ 1 · q⁰`.  `0 < |β − p/q|` is
irrationality of `β`. -/
private lemma sunit_pos (h : Ridout1957) (β : ℝ) (hb : IsAlgebraic ℚ β) (hirr : Irrational β)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (δ : ℝ) (hδ : 0 < δ) :
    {r : ℚ | 0 < r.num ∧ (∀ p ∈ r.den.primeFactors, p ∈ S) ∧
      |β - (r:ℝ)| < 1 / (r.den : ℝ) ^ (1 + δ)}.Finite := by
  have hβ0 : β ≠ 0 := fun h0 => hirr ⟨0, by simp [h0]⟩
  have hfin := h β hb hβ0 ∅ S (by simp) hS (Finset.disjoint_empty_left _)
    1 0 1 (1 + δ) zero_le_one le_rfl le_rfl zero_le_one one_pos (by linarith)
  refine Set.Finite.subset
    (Set.Finite.preimage (f := fun r : ℚ => (r.num.toNat, r.den)) ?_ hfin) ?_
  · intro r hr r' hr' hgg
    have h1 : 0 < r.num.toNat := hr.1
    have h2 : 0 < r'.num.toNat := hr'.1
    have hn : r.num.toNat = r'.num.toNat := congrArg Prod.fst hgg
    have hd : r.den = r'.den := congrArg Prod.snd hgg
    exact Rat.ext (by omega) hd
  · intro r hr
    obtain ⟨hpos, hSr, hlt⟩ := hr
    have hden0 : 0 < r.den := r.pos
    have hnum : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hpos.le
    have hcast : (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by
      rw [Rat.cast_def]; congr 1; exact_mod_cast hnum.symm
    refine ⟨Int.pos_iff_toNat_pos.mp hpos, hden0, ⟨r.num.toNat, 1, (mul_one _).symm, by simp,
        Int.pos_iff_toNat_pos.mp hpos, ?_⟩,
      ⟨1, r.den, (one_mul _).symm, hSr, one_pos, ?_⟩, ?_, ?_⟩
    · rw [Real.rpow_one]; linarith
    · rw [Real.rpow_zero]; norm_num
    · rw [abs_pos, sub_ne_zero, ← hcast]
      exact fun he => hirr ⟨r, he.symm⟩
    · rw [← hcast]; exact hlt

/-- The `S`-unit-denominator corollary from Ridout's 1957 theorem.  A rational with negative
numerator is handled by negating both `α` and `r` (`(-r).den = r.den`), and `r = 0` separately. -/
theorem ridoutSUnitDen_of_ridout1957 (h : Ridout1957) : Ridout1957SUnitDen := by
  intro α hα hirr S hS δ hδ
  have h1 := sunit_pos h α hα hirr S hS δ hδ
  have h2 := sunit_pos h (-α) hα.neg hirr.neg S hS δ hδ
  refine Set.Finite.subset ((h1.union (h2.image (fun r : ℚ => -r))).union
    (Set.finite_singleton (0 : ℚ))) ?_
  intro r hr
  obtain ⟨hSr, hlt⟩ := hr
  rcases lt_trichotomy r.num 0 with hn | hn | hn
  · refine Or.inl (Or.inr ⟨-r, ⟨?_, ?_, ?_⟩, by ring⟩)
    · rw [Rat.neg_num]; omega
    · exact hSr
    · have hrw : |(-α) - ((-r : ℚ) : ℝ)| = |α - (r : ℝ)| := by
        push_cast
        rw [← abs_neg]
        ring_nf
      rw [hrw]
      exact hlt
  · exact Or.inr (by simp [Rat.zero_iff_num_zero.mpr hn])
  · exact Or.inl (Or.inl ⟨hn, hSr, hlt⟩)


/-- Roth's theorem is the `t = 0` case of Ridout's `p`-adic theorem. -/
theorem roth_of_ridout1958 (h : Ridout1958) : Roth1955 := by
  sorry

end LeanFormalizations.Diophantine
