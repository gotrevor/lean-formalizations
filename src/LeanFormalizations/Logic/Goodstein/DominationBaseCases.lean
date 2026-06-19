/-
# Cichoń's lower bound at finite levels: the unconditional closure

`Logic/Goodstein/Domination.lean` reduces the diagonal domination
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` to **one** self-referential length bound
`goodsteinLength m ≥ 2^{m+1} + m` (`goodsteinLength_exp_lower`), via the self-similarity recursion
`leadExp_ge_goodsteinSeq_log` (the leading-exponent sequence dominates the Goodstein sequence one
scale down). That strong induction needs finitely many computational base cases — the seeds
`4 ≤ M < 16`, where the length must already be exponentially large. This file discharges them with the
tail-recursive forward evaluator `gpos` under `native_decide` (each is a finite computation; the
Goodstein values for these small seeds stay polynomial-sized for the required step counts), turning the
diagonal lower bound into a fully machine-checked, unconditional theorem at every finite level.

These `native_decide` calls are deliberately isolated here: the heaviest, `M = 15`, certifies
`goodsteinLength 15 ≥ 2^16 + 15 = 65551` (a `65551`-step forward pass) and takes a few minutes; keeping
them out of `Domination.lean` keeps that file's iteration fast. The unconditional theorems below
therefore carry `Lean.ofReduceBool` (from the finite base-case computations) in addition to the
standard `[propext, Classical.choice, Quot.sound]`; the *mathematical* engine `goodsteinLength_exp_lower`
and the conditional reductions in `Domination.lean` stay axiom-clean.
-/
import LeanFormalizations.Logic.Goodstein.Domination

namespace LeanFormalizations.Logic.Goodstein

open ONote

/-- **The finitely many base cases of Cichoń's exponential length bound** (`4 ≤ M < 16`):
`2^{M+1} + M ≤ goodsteinLength M`, each discharged by the forward evaluator `gpos` + `native_decide`.
The heaviest is `M = 15` (a `65551`-step certificate). -/
theorem goodsteinLength_base_cases (M : ℕ) (h4 : 4 ≤ M) (h16 : M < 16) :
    2 ^ (M + 1) + M ≤ goodsteinLength M := by
  have hM : M = 4 ∨ M = 5 ∨ M = 6 ∨ M = 7 ∨ M = 8 ∨ M = 9 ∨ M = 10 ∨ M = 11 ∨ M = 12 ∨
      M = 13 ∨ M = 14 ∨ M = 15 := by omega
  rcases hM with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact glen_ge_of_gpos (by native_decide)

/-- **Cichoń's exponential length lower bound, UNCONDITIONAL:** `2^{m+1} + m ≤ goodsteinLength m` for
every `m ≥ 4`. The strong-induction engine `goodsteinLength_exp_lower` fed by the computational base
cases. The self-similarity makes the exponential bound reproduce itself at each scale. -/
theorem goodsteinLength_exp_lower_uncond {m : ℕ} (hm : 4 ≤ m) :
    2 ^ (m + 1) + m ≤ goodsteinLength m :=
  goodsteinLength_exp_lower goodsteinLength_base_cases m hm

/-- **THE `o = 2` DIAGONAL DOMINATION — UNCONDITIONAL (every `m ≥ 16`):**
`fastGrowing 2 m ≤ goodsteinLength m + 2`, i.e. `f_2(m) = 2^m · m ≤ goodsteinLength m + 2`. This is the
*true diagonal* bound — budget `m`, not the earlier `log₂ m` of `fastGrowing_two_log_le_goodsteinLength`
— hence Cichoń's lower bound at level `o = 2`, fully machine-checked: the Goodstein descent's leading
CNF exponent provably stays `≥ 2` for the first `m` steps. Assembly: for `m ≥ 16` the smaller seed
`L = Nat.log 2 m` is `≥ 4`, so the unconditional exponential length bound gives
`goodsteinLength L ≥ 2^{L+1} + L ≥ m + 2` (as `m < 2^{L+1}`), discharging the hypothesis of
`fastGrowing_two_le_goodsteinLength_of_log_length`. (The finite tail `4 ≤ m < 16` also holds but its
direct certification is far more expensive — `f_2(15) ≈ 5·10^5` steps — and is omitted: asymptotic
domination is the mathematically meaningful statement.) -/
theorem fastGrowing_two_le_goodsteinLength {m : ℕ} (hm : 16 ≤ m) :
    fastGrowing 2 m ≤ goodsteinLength m + 2 := by
  have hL4 : 4 ≤ Nat.log 2 m := by
    calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
      _ ≤ Nat.log 2 m := Nat.log_mono_right hm
  have hexp := goodsteinLength_exp_lower_uncond (m := Nat.log 2 m) hL4
  have hpow : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m; omega
  have hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m) := by omega
  exact fastGrowing_two_le_goodsteinLength_of_log_length (by omega) hlen

/-- **THE FULL DIAGONAL DOMINATION — UNCONDITIONAL, every finite level `n`:**
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` whenever `n + 1 ≤ Nat.log 2 m` (and `m ≥ 16`).
For each fixed `n` this holds for all sufficiently large `m` (those with `Nat.log 2 m ≥ n + 1`, i.e.
`m ≥ 2^{n+1}`). This is **Cichoń's lower bound at every finite level**, fully machine-checked: the
Goodstein descent's leading CNF exponent provably stays `≥ n` for the first `m` steps, so
`goodsteinLength` diagonally dominates the entire finite fast-growing hierarchy `f_0, f_1, f_2, …`.
The unconditional exponential length bound at the smaller seed `L = Nat.log 2 m` supplies
`goodsteinLength L ≥ 2^{L+1} + L ≥ m + n` (using `m < 2^{L+1}` and `n ≤ L − 1`), discharging the
hypothesis of `fastGrowing_ofNat_le_goodsteinLength_of_log_length`. -/
theorem fastGrowing_ofNat_le_goodsteinLength {n m : ℕ} (hm : 16 ≤ m)
    (hn : n + 1 ≤ Nat.log 2 m) :
    fastGrowing (ONote.ofNat n) m ≤ goodsteinLength m + 2 := by
  have hL4 : 4 ≤ Nat.log 2 m := by
    calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
      _ ≤ Nat.log 2 m := Nat.log_mono_right hm
  have hexp := goodsteinLength_exp_lower_uncond (m := Nat.log 2 m) hL4
  have hpow : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m; omega
  have hloglt : Nat.log 2 m < m := Nat.log_lt_self 2 (by omega)
  have hlen : m + n ≤ goodsteinLength (Nat.log 2 m) := by omega
  exact fastGrowing_ofNat_le_goodsteinLength_of_log_length (by omega) (by omega) hlen

/-- Anti-vacuity: the diagonal bound is non-trivial — `f_n` is astronomically large at its argument.
`f_2(16) = 2^16 · 16 = 1048576`, yet `≤ goodsteinLength 16 + 2`. (Not `native_decide`-able — RHS is
beyond astronomical — but `f_2(16)` itself is, witnessing the LHS is a genuine fast-growing value.) -/
example : fastGrowing 2 16 = 2 ^ 16 * 16 := by rw [ONote.fastGrowing_two]

end LeanFormalizations.Logic.Goodstein
