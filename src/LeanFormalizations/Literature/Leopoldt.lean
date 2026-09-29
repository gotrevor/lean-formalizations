/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Leopoldt's conjecture (1962): statement

Open in general.  Proved for abelian extensions of `ℚ` and of imaginary quadratic fields (Ax 1965
reduced it to the p-adic Baker theorem, proved by Brumer 1967).  Mihăilescu announced a proof for
CM fields (2009/2011); it is not accepted.  Waldschmidt 2023 §2.  Trevor, 2026-09-29: *"This is
math worth having in the world."*

## Formulation (avoids the p-adic logarithm, which mathlib at our pin lacks)

The classical statement (Washington, *Cyclotomic Fields*, §5.5) is: the `ℤ_p`-rank of the closure
of the global units in `∏_{v | p} U_v` equals their `ℤ`-rank.  Equivalently, the map
`ℤ_p ⊗ E → ∏_{v|p} K_v^×` is injective.  We phrase injectivity through **integer exponent
sequences**.  For multiplicatively independent units `ε₁, …, ε_r`, if integer vectors `m⁽ⁿ⁾`
converge `p`-adically to `a ∈ ℤ_p^r` and `∏ εᵢ^{mᵢ⁽ⁿ⁾} → 1` in every completion `K_v` with
`v | p`, then `a = 0`.

Why this is faithful (Ren's argument, about 75%; the stress tests in
`NumberTheory/Leopoldt/` are there to catch a mistake):
- Let `N` be prime to `p` with every `εᵢ^N` a principal unit at every `v | p`; `N` is the order of
  the residue-field unit groups.  Pass to a subsequence with `m⁽ⁿ⁾ ≡ c (mod N)` constant.  Then
  `ε^{m⁽ⁿ⁾} = ε^c·(ε^N)^{(m⁽ⁿ⁾−c)/N} → ε^c·(ε^N)^b` with `b = (a−c)/N ∈ ℤ_p^r`, which is the image of
  `a ⊗ ε` under the classical map.
- So the hypothesis says `a` lies in the kernel, and the conclusion `a = 0` is injectivity.
- Independent families suffice.  `ℤ_p` is flat, so injectivity for a basis of `E`/torsion gives
  injectivity for every independent subfamily, and conversely a basis is one.
-/
import Mathlib

namespace LeanFormalizations.Literature

open NumberField IsDedekindDomain Filter Topology

/-- **Leopoldt's conjecture** for the number field `K` at the prime `p`. -/
def LeopoldtConjecture (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (r : ℕ) (ε : Fin r → (𝓞 K)ˣ),
    (∀ m : Fin r → ℤ, ∏ i, ε i ^ m i = 1 → m = 0) →
    ∀ (a : Fin r → ℤ_[p]) (m : ℕ → Fin r → ℤ),
      (∀ i, Tendsto (fun n ↦ ((m n i : ℤ) : ℤ_[p])) atTop (𝓝 (a i))) →
      (∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal →
        Tendsto (fun n ↦ algebraMap K (v.adicCompletion K)
          (∏ i, (((ε i : 𝓞 K) : K)) ^ (m n i))) atTop (𝓝 1)) →
      a = 0

/-- Leopoldt's conjecture for every number field and every prime. -/
def LeopoldtConjectureAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime], LeopoldtConjecture K p

end LeanFormalizations.Literature
