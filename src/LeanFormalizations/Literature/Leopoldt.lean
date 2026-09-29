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
of the global units in `∏_{v | p} U_v⁽¹⁾` equals their `ℤ`-rank.  Equivalently, the map
`ℤ_p ⊗ E → ∏_{v|p} U_v⁽¹⁾` is injective, after projecting each local unit to its principal part
(`π : U_v → U_v⁽¹⁾`, killing prime-to-`p` torsion; `U_v⁽¹⁾` is pro-`p`).  We phrase injectivity through
**integer exponent sequences**.  For multiplicatively independent units `ε₁, …, ε_r`, if integer
vectors `m⁽ⁿ⁾` converge `p`-adically to `a ∈ ℤ_p^r` and `∏ εᵢ^{mᵢ⁽ⁿ⁾} → 1` in every completion `K_v`
with `v | p`, then `a = 0`.

**Peer formalization.**  William Coram's formal-conjectures PR #5497 (opened 2026-09-10; branch `WilliamCoram/formal-conjectures@Leopoldts` proves the equivalences) states Leopoldt in five forms: Wikipedia's closure rank, the p-adic regulator, `padicRelation`, `elementary`, and Mihăilescu's defect.  Ours is closest to his `padicRelation`.  Found only after this file was written.  His is the public statement; ours is the fact-graph node.

**Faithfulness.**  Ren's argument; an independent adversarial review on 2026-09-29 judged it faithful
at 88% and supplied the converse direction.
- *Classical ⇒ Lean.*  Let `N` be the lcm of `q_v − 1` over `v | p`, where `q_v` is the residue field
  size.  `N` is prime to `p` (true also for ramified `v` and for `p = 2`), and every `εᵢ^N` is
  principal.  Some residue class `c mod N` occurs infinitely often among the `m⁽ⁿ⁾`; pass to that
  subsequence.  `(m⁽ⁿ⁾ − c)/N → (a − c)/N` in `ℤ_p`, since `N` is a `p`-adic unit.  `U_v⁽¹⁾` is pro-`p`, so
  `k ↦ (ε^N)^k` extends continuously to `ℤ_p`.  Applying `π`, the limit gives `π(ε)^a = 1`.  So
  `a ⊗ ε` is in the kernel, and flatness of `ℤ_p` (`ℤ_p ⊗ ℤ^r ↪ ℤ_p ⊗ E`) gives `a = 0`.  Note that the
  prime-to-`p` part of `ε^c` need not be 1 on its own; it is 1 here only because the limit is 1.
- *Lean ⇒ classical.*  Write `E = μ(K) × ⟨η₁, …, η_s⟩`.  A nonzero kernel element is `ζ·η^a`, with `ζ`
  a `p`-power root of unity, and `a ≠ 0` because the map is injective on `μ_{p^∞}`.  Multiply by
  `p^k = ord ζ` to get `a' = p^k·a ≠ 0` with `π(η)^{a'} = 1`.  Choose `m⁽ⁿ⁾ = N·(integer truncations of
  a'/N)`: the factor `N` kills the prime-to-`p` parts.  Then `η^{m⁽ⁿ⁾} → 1` at every `v | p` while
  `m⁽ⁿ⁾ → a' ≠ 0`, contradicting the Lean statement.  (Naive truncations of `a'` do not work; the
  `m ≡ 0 mod N` choice is needed.)
- Quantifying over all independent families is equivalent to a basis, by flatness.  Some `v` lies
  over `p`, because `p` is a nonunit in `𝓞 K`.
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
