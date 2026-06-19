/-
# Prime Number Theorem port — Asymptotics prerequisites (first brick)

This is the **first brick of the `weakPNT` discharge via porting** (`PENDING_WORK.md` option 3 — the only
*active* discharge route, since the lake-dependency route is dead on this no-egress box and `wait-and-cite`
is passive). The flagship no-three-in-line headline
`Combinatorics/NoThreeInLine/PrimeGap.maxNoThreeInLine_ge_three_halves_sub` (HJSW-optimal `3/2 − o(N)`)
rests on the cited axiom `weakPNT : Chebyshev.psi ~[atTop] (·)` (the Prime Number Theorem). Discharging it
means porting `PrimeNumberTheoremAnd`'s Wiener–Ikehara tauberian tower onto our mathlib `v4.29.1` (mathlib
already supplies the heavy analysis + the arithmetic crux `riemannZeta_ne_zero_of_one_le_re`; only the
tauberian bridge is missing).

These four lemmas are a verbatim port of `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean`
(Apache-2.0; a self-contained Wiener-cone prerequisite). All four dependencies exist in our pin, so the port
is clean — confirming the patch layer ports without API drift. Kept in a local namespace to avoid clashing
with mathlib / a future full port (which may re-home them into `Asymptotics`/`Filter.Eventually`).

**Status: speculative.** `wait-and-cite` (mathlib landing Wiener–Ikehara natively — it is on-trajectory,
see `LSeries/PrimesInAP.lean`) remains the *preferred* discharge; continue this port only if mathlib stalls.
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Topology

namespace LeanFormalizations.PrimeNumberTheorem

open Asymptotics

/-- A constant is `=o[cocompact]` the identity. (Port of `Asymptotics.isLittleO_const_id_cocompact`.) -/
theorem isLittleO_const_id_cocompact {E'' F'' : Type*}
    [NormedAddCommGroup E''] [NormedAddCommGroup F''] [ProperSpace F''] (c : E'') :
    (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

/-- A constant is `=o[atTop]` the identity. (Port of `Asymptotics.isLittleO_const_id_atTop2`.) -/
theorem isLittleO_const_id_atTop {E'' F'' : Type*}
    [NormedAddCommGroup E''] [NormedAddCommGroup F''] [LinearOrder F''] [NoMaxOrder F'']
    [ClosedIciTopology F''] [ProperSpace F''] (c : E'') :
    (fun _x : F'' => c) =o[atTop] id :=
  (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

/-- A constant is `=o[atBot]` the identity. (Port of `Asymptotics.isLittleO_const_id_atBot2`.) -/
theorem isLittleO_const_id_atBot {E'' F'' : Type*}
    [NormedAddCommGroup E''] [NormedAddCommGroup F''] [LinearOrder F''] [NoMinOrder F'']
    [ClosedIicTopology F''] [ProperSpace F''] (c : E'') :
    (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

/-- Push an `atTop`-eventually statement over `ℝ` down to the naturals. (Port of
`Filter.Eventually.natCast`.) -/
theorem eventually_natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

/-- Restrict a real `IsBigO` at `atTop` to the naturals. (Port of `Asymptotics.IsBigO.natCast`.) -/
theorem isBigO_natCast {E : Type*} [Norm E] {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

open Real in
/-- `log^b x / x^a → 0` at infinity for `a > 0`. (Port of `Real.tendsto_pow_log_div_pow_atTop`, the
`Mathlib/Analysis/SpecialFunctions/Log/Basic` patch; brick 2 — uses our pin's root-namespace
`isLittleO_log_rpow_rpow_atTop`.) Used by PNTAnd's `WeakPNT` derivation. -/
theorem tendsto_pow_log_div_pow_atTop (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun x ↦ Real.log x ^ b / x ^ a) atTop (nhds 0) := by
  apply (isLittleO_iff_tendsto' ?_).mp (isLittleO_log_rpow_rpow_atTop b ha)
  filter_upwards [eventually_gt_atTop 0] with x hx h
  rw [Real.rpow_eq_zero hx.le ha.ne'] at h
  exact absurd h hx.ne'

end LeanFormalizations.PrimeNumberTheorem
