/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Pisot

/-!
# Literature input: Saito 2025, Type B + Proposition 3.1(iv)

K. Saito, *Transcendency of variants of Mills' constant*, arXiv:2508.16068 (2025); Ramanujan J. **70**
(2026), no. 4, Art. 69, doi:10.1007/s11139-026-01443-0 (accepted 2026-07-23), Theorem 2.3
("Type B", first conclusion) combined with Proposition 3.1(ii),(iv) (with `θ = 21/40`, Baker–Harman–Pintz).
Local text: `papers/saito-2025-transcendency-variants-mills.txt` (Theorem 2.3 at line ~224,
Proposition 3.1 at line ~416).  Rules as in `Literature/Primes.lean`: faithful or weaker, cited,
never an `axiom`.

**Faithful-or-weaker check** (Ren, 2026-09-30):
* Hypotheses are *stronger* than Saito's:
  - `(B1)` `C₁ ≥ 1`;
  - `(B2)` `C_(k+1) ≥ 2 C_k` for all `k ≥ 1`;
  - "ratio `≥ 29/10` infinitely often" implies `(B3)` `lim sup c_(k+1) > 40/19`;
  - `(B4)` `C_k ∈ ℕ` (by typing).
  - Our `(B5′)` asks for `k > m` with `C_m ∣ C_k` **and** `C_(k+1) ≥ (29/10) C_k`.  So `k` lies in Saito's `I = {k : c_(k+1) ≥ 40/19 + ε}` for every `ε ≤ 29/10 − 40/19`, which gives `(B5)`.
* Conclusion is *weaker*: Saito gives `ξ` transcendental or `ξ^g = β` Pisot of degree
  `3 ≤ ℓ ≤ 1 + (19/40 · lim sup c_(k+1) − 1)⁻¹`.  With `lim sup ≥ 29/10` the bound is `< 4`, so `ℓ = 3`.
  - Also `g ∣ C_k` for all large `k ∈ I`.
  - Prop 3.1(iv): `Tr(β^(C_k/g)) = ⌊ξ^(C_k)⌋` for all large `k ∈ I`.
  - We state only these, for `k` large **and** in `I₂₉/₁₀ := {k : C_(k+1) ≥ (29/10) C_k}`, which is contained in Saito's `I` for small `ε`.
* Prop 3.1 also assumes `(3.1)`, `ξ^(C_m) ∉ ℕ` for every `m`.  Saito's proof of Theorem 2.3 (Section 8,
  first paragraph) derives it from `(B5)`: an integer `ξ^(C_m)` would make `ξ^(C_k)` composite for the
  `k > m` with `C_m ∣ C_k`, yet it equals the prime `⌊ξ^(C_k)⌋`.  Our `(B5′)` supplies that `k`, so no
  extra hypothesis is needed.
* The combination of Theorem 2.3 with Prop 3.1(iv) rests on the *proof* of Theorem 2.3 in Section 8
  (which verifies Prop 3.1's hypotheses with the same `g`), not on its statement.  Audited against arXiv
  v3 (2025-12-07); the journal text has not been compared.  Audit: `docs/notes/saito-2025-faithfulness-audit.md`.
-/

namespace LeanFormalizations.Literature

/-- The trace `Σ z^N` over the complex roots of the minimal polynomial of `β` (Saito's `Tr(β^N)`). -/
noncomputable def powTrace (β : ℝ) (N : ℕ) : ℂ :=
  (((minpoly ℚ β).aroots ℂ).map (· ^ N)).sum

/-- **Saito (2025), Theorem 2.3 + Proposition 3.1(ii),(iv), specialized to `lim sup c_(k+1) ≥ 29/10`.** -/
def Saito2025TypeBTrace : Prop :=
  ∀ C : ℕ → ℕ,
    1 ≤ C 1 →
    (∀ k ≥ 1, 2 * C k ≤ C (k + 1)) →
    (∀ K : ℕ, ∃ k ≥ K, (29 : ℝ) / 10 * C k ≤ C (k + 1)) →
    (∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1)) →
    ∃ ξ : ℝ, IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ C k⌋₊).Prime} ξ ∧
      (Transcendental ℚ ξ ∨
        ∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g) ∧ (minpoly ℚ (ξ ^ g)).natDegree = 3 ∧
          ∃ K : ℕ, ∀ k ≥ K, (29 : ℝ) / 10 * C k ≤ C (k + 1) →
            g ∣ C k ∧ powTrace (ξ ^ g) (C k / g) = (⌊ξ ^ C k⌋₊ : ℂ))

end LeanFormalizations.Literature
