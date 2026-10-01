/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.Kronecker

/-!
# The paired-root lemma (the Mills hard core, 2026-10-01)

Write-up: `PROBE-MILLS-RESIDUAL.md` §7; numerics: `scripts/mills-residual-probe.py`
(`pair-control`, `tau-plus`, `hard-core`).

**Status: both statements are believed true and are NOT proved here (`sorry`).**  Trevor,
2026-10-01: "Fine to leave the lemma's proof as unformalized", and "if it's not in lean, it
doesn't exist."  So the statements live here, frozen, with the English proof and the evidence
below.  A later lap may discharge the `sorry`s.

Phase 60 (`Kronecker.lean`) gave the τ = −1 residual classes a finite Jacobi certificate.  The
τ = +1 classes looked immune, because there the Frobenius types allowed at a late Mills prime
(split and (1)(2)) surject onto `Gal^ab = C₂`.  This file removes type (1)(2) whenever the 3-adic
rate is `c = 1` and `det C` is a cube.  So unit cubics with `c = 1` get the Jacobi certificate as
well.

## English proof of `dvd_trace_of_pair_mod` (confidence 97%)

Write `D = C̄` over `𝔽_p`, `p ≡ 1 (mod 3)`, and `s = v₃(p − 1)`.  A root together with a non-square
discriminant means type (1)(2): roots `r ∈ 𝔽_p` and `ρ, ρ^p ∈ 𝔽_(p²) \ 𝔽_p`, all distinct.

1. `𝔽_p[X]/χ ≅ 𝔽_p × 𝔽_(p²)`, and the projective group `(𝔽_p × 𝔽_(p²))^× / 𝔽_p^×` is isomorphic
   to `𝔽_(p²)^×` via `(a, z) ↦ z / a`.  So the order of `D` modulo scalars is the order of
   `z = ρ / r` in `𝔽_(p²)^×`.
2. Since `3 ∤ p + 1`, the 3-part of `z` has the same order as the 3-part of
   `N(z) = z^(p+1) = ρ ρ^p / r² = det D / r³`.
3. `det D` is a cube by hypothesis, so `N(z)` is a cube in `𝔽_p^×`.  Its 3-part therefore has
   order dividing `3^(s−1)`, and `s − 1 ≤ j`.
4. So `D^(3^j)` has projective order `L` prime to 3.  Take `J = ord_L(3) ≥ 1`.  Then
   `D^(3^(j+J)) = λ · D^(3^j)` for a scalar `λ ∈ 𝔽_p^×`, and taking traces gives
   `T_(j+J) = λ T_j ≡ 0 (mod p)`. ∎

In words: a Frobenius-conjugate pair of roots has a single cube class, because
`ρ^p = ρ · ρ^(p−1)` and `p ≡ 1 (mod 3)`.  The norm then drags the third root into the same class.

## Evidence

- `pair-control` (all classes, `|c₂|, |c₁| ≤ 30`, unit, `j = 1, 2`, `p < 10⁷`): **48 of 48** type
  (1)(2) primes `T_j` with `v₃(T_j − 1) = j + 1` recur.  Each `p ∣ T_(j+J)` was checked by a direct
  matrix power mod `p`.  **Control:** with `v₃(T_j − 1) ≥ j + 2` (no prediction), 6 of 24 recur.
- `tau-plus`: the resulting Jacobi filter alone kills 436 of 442 unit τ = +1 S3 cubics with
  `c = 1` in a box.

## Lean route (for a later lap)

- Step 1 is the hard part in Lean.  An alternative avoids `𝔽_(p²)`: `D^(p²−1) = 1`, since `D` is
  semisimple with eigenvalues in `𝔽_(p²)`.  Then work with `M = D^((p²−1)/3^s)`.
- Steps 2–4 then mirror `Kronecker.trace_pow_periodic_of_splits`.
- `isSquare_charDisc_mod_eventually_of_rate_one` combines `dvd_trace_of_pair_mod` with
  `Projective.not_irreducible_mod_eventually`, following the skeleton of
  `Kronecker.not_isSquare_charDisc_mod_eventually`.
-/

namespace LeanFormalizations.Mills.PairedRoot

open LeanFormalizations.Mills Kronecker Matrix Filter Polynomial

/-- **Paired-root lemma.**  Suppose that at a prime `p ≡ 1 (mod 3)` the integer cubic matrix `C`
has type (1)(2) (a root, but a non-square discriminant), and that `det C` is a nonzero cube
mod `p`.  If `p ∣ tr C^(3^j)` and `v₃(p − 1) ≤ j + 1`, then `p` divides a later term
`tr C^(3^(j+J))`.  Believed true (97%); the English proof is in the module docstring. -/
theorem dvd_trace_of_pair_mod (C : Matrix (Fin 3) (Fin 3) ℤ) {p j : ℕ} [Fact p.Prime]
    (hp3 : p % 3 = 1) (hdet : ¬ (p : ℤ) ∣ C.det)
    (hcube : ∃ m : ZMod p, ((C.det : ℤ) : ZMod p) = m ^ 3)
    (hroot : ∃ r : ZMod p, (C.map (Int.castRingHom (ZMod p))).charpoly.IsRoot r)
    (hdisc : ¬ IsSquare ((charDisc C : ℤ) : ZMod p))
    (hs : padicValNat 3 (p - 1) ≤ j + 1)
    (hdiv : (p : ℤ) ∣ (C ^ (3 ^ j)).trace) :
    ∃ J, 1 ≤ J ∧ (p : ℤ) ∣ (C ^ (3 ^ (j + J))).trace := by
  sorry

/-- **The τ = +1 Jacobi certificate's input.**  Suppose the traces `t_k = tr C^(3^k)` are prime
and increasing, and `det C` is a nonzero cube (for example `±1`).  Then for every large `k` at
which the 3-adic rate is one (`v₃(t_k − 1) = k + 1`), the discriminant is a square mod `t_k`:
`t_k` splits completely.  Inert is excluded by phase 31, and (1)(2) by `dvd_trace_of_pair_mod`.
Believed true (97%). -/
theorem isSquare_charDisc_mod_eventually_of_rate_one (C : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : C.det ≠ 0) (hcube : ∃ m : ℤ, C.det = m ^ 3) (hD : charDisc C ≠ 0) {k₀ : ℕ}
    (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∀ᶠ k in atTop, padicValNat 3 ((C ^ (3 ^ k)).trace.toNat - 1) = k + 1 →
      IsSquare ((charDisc C : ℤ) : ZMod (C ^ (3 ^ k)).trace.toNat) := by
  sorry

/-! ## Other conclusions of `PROBE-MILLS-RESIDUAL.md`, stated -/

/-- **The 3-adic rate, class `(x−1)²(x+1)`, unit case.**  Here `det C = −1`.  The rate is `c ≥ 2`,
i.e. `3^(k+2) ∣ tr C^(3^k) − 1` for all large `k`, iff `9 ∣ f(−1)`.  Equivalently, the 3-adic root
near `−1` is a 3-adic cube.

Believed true (85%).
- Numerics: `tau-plus` with `|c₂|, |c₁| ≤ 40` (box 40), 676 of 676 unit cases.
- Heuristic: `T_k − 1 = −2 · 3^k log(−γ₃) + O(3^(2k))`, where `γ₃ ∈ ℤ₃` is the root `≡ −1`.
- Not proved: making the `O(3^(2k))` term precise, and the case `v(log) ≥ 2`. -/
theorem rate_ge_two_iff_of_minus_one (C : Matrix (Fin 3) (Fin 3) ℤ) (hdet : C.det = -1)
    (hirr : Irreducible (C.map (Int.castRingHom ℚ)).charpoly)
    (hcls : (C.map (Int.castRingHom (ZMod 3))).charpoly = (X - 1) ^ 2 * (X + 1)) :
    (∀ᶠ k in atTop, (3 : ℤ) ^ (k + 2) ∣ (C ^ (3 ^ k)).trace - 1) ↔
      (9 : ℤ) ∣ C.charpoly.eval (-1) := by
  sorry

/-- **Conjecture LC (local certificates), `PROBE-MILLS-RESIDUAL.md` §5a.**  Every irreducible
integer cubic whose cube-power traces lie in a residual class (`t_k ≡ ±1 mod 3^(k+1)`, phase 29)
and grow has a local certificate.  Either some prime `q ≠ 3` divides `t_k` infinitely often, or
`Tr C ≡ 2 (mod 3)` and the Jacobi symbol `(disc / t_k)` differs from `−1` infinitely often.

With the paired-root certificate added (τ = +1, unit, `c = 1`), LC restricted to totally real Pisot
cubics with Saito's (1.3) would make Mills' constant transcendental.

Status: open, Artin-type, no mechanism.  Evidence: every explicit residual cubic tested has a
certificate (`saito`, `tau-minus`), and the Fermat sibling has none structurally, so it does not
refute LC.  This is a node, not a belief we can price above about 60%. -/
def LocalCertificates : Prop :=
  ∀ C : Matrix (Fin 3) (Fin 3) ℤ, Irreducible (C.map (Int.castRingHom ℚ)).charpoly →
    (∀ k, (3 : ℤ) ^ (k + 1) ∣ (C ^ (3 ^ k)).trace - 1 ∨
      (3 : ℤ) ^ (k + 1) ∣ (C ^ (3 ^ k)).trace + 1) →
    Tendsto (fun k => (C ^ (3 ^ k)).trace) atTop atTop →
    (∃ q : ℕ, q.Prime ∧ q ≠ 3 ∧ ∃ᶠ k in atTop, (q : ℤ) ∣ (C ^ (3 ^ k)).trace) ∨
      (C.trace % 3 = 2 ∧
        ∃ᶠ k in atTop, jacobiSym (charDisc C) (C ^ (3 ^ k)).trace.toNat ≠ -1)

end LeanFormalizations.Mills.PairedRoot
