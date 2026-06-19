/-
Integrability of the Abel-summation dominator t^(-s)*(1 + log t) on (1,∞) for s > 1.
This is the `hg_int` hypothesis for an Abel-summation argument on the prime zeta function.
Since s > 1, the polynomial decay t^(-s) (with -s < -1) makes both t^(-s) and t^(-s)*log t
integrable on (1,∞): the log factor is absorbed because log t = o(t^ε) for any ε > 0, so
t^(-s)*log t = o(t^(-s')) for any s' with 1 < s' < s, and t^(-s') is integrable on (1,∞).

Strategy: write the integrand as t^(-s) + t^(-s)*log t and use Integrable.add.
- t^(-s) on Ioi 1: integrableOn_Ioi_rpow_of_lt (needs -s < -1, i.e. s > 1) or integrableOn_Ioi_rpow_iff.
- t^(-s)*log t on Ioi 1: dominate/compare. Pick s' = (1+s)/2 ∈ (1,s). For large t, log t ≤ C·t^(s-s')
  (Real.isLittleO_log_id_atTop or log_le_rpow type bounds / Real.add_pow_le... ), giving
  |t^(-s) log t| ≤ C t^(-s') eventually, which is integrable (integrableOn_Ioi_rpow_of_lt, -s' < -1).
  Use MeasureTheory.Integrable.mono' / IntegrableOn via comparison, or
  integrableOn_Ioi_of_isBigO / Asymptotics.IsBigO with the eventual bound and local integrability
  (the integrand is continuous on [1,∞)). Continuity on Ioi 1: ContinuousOn.mul of rpow_const and log.
Replace the sorry with a complete proof. Keep the statement exactly as given.
-/
import Mathlib
open MeasureTheory Set

theorem integrable_rpow_neg_mul_log (s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun t : ℝ => t ^ (-s) * (1 + Real.log t)) (Ioi 1) := by
  sorry
