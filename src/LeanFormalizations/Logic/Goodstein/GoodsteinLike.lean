/-
# `GoodsteinLike` sequences and the self-similarity TOWER

Lap 9 found the winning idea — **self-similarity**: the leading-exponent sequence
`L_k = log_{base k}(G_k)` of a Goodstein descent is *itself* a Goodstein-like descent, so it
dominates the genuine Goodstein sequence seeded at `L_0 = log₂ m`. Lap 10 closed `o = ω` by iterating
that idea once. This file extracts the idea into its **clean reusable abstraction** and proves the
*fully iterated* form, the engine for climbing the ordinal tower toward `f_{ε₀}`.

A sequence `a : ℕ → ℕ` is `GoodsteinLike` when it obeys the Goodstein lower-bound recursion
`a (k+1) ≥ bump (base k) (a k) − 1` at every step (the genuine `goodsteinSeq` obeys it with equality).
Two structural facts hold for every such sequence:

* **`GoodsteinLike.dominates`** — `a` dominates `goodsteinSeq (a 0)` (self-similarity: the recursion
  with the `−1` firing at every step is the slowest, so `goodsteinSeq (a 0)` is a lower envelope).
* **`GoodsteinLike.logSeq`** — `k ↦ log_{base k} (a k)` is again `GoodsteinLike` (the leading exponent
  of a Goodstein-like sequence is Goodstein-like — the level-up that drives the tower).

Iterating the second fact (`GoodsteinLike.iterate`) and feeding the first gives the headline
**`iterLeadExp_dominates`**: the `j`-fold iterated leading exponent of the seed-`m` descent dominates
the Goodstein sequence seeded at the `j`-fold logarithm `(log₂)^[j] m`. For `j = 0` this is the value
itself; `j = 1` is lap-9's `leadExp_ge_goodsteinSeq_log`; each higher `j` is one ordinal level up
(`o = ω^j`-flavoured), the precise self-reference behind Cichoń's lower bound at the limit levels.
-/
import LeanFormalizations.Logic.Goodstein.Domination

namespace LeanFormalizations.Logic.Goodstein

/-- **General per-step log descent.** For any `n`, the leading exponent obeys the Goodstein recursion
as a *lower bound*: `bump b (log_b n) − 1 ≤ log_{b+1} (bump b n − 1)`. Off pure powers it is an
equality at `bump b (log_b n)` (`log_bump_pred_of_not_pow`); at a pure power it drops by exactly one
(`log_bump_pred_of_pow`); when `n = 0` both sides are `0`. Generalizes `leadExp_step_ge` from the
concrete Goodstein value to an arbitrary `n` — the brick that makes `log ∘ a` Goodstein-like. -/
theorem log_step_ge (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    bump b (Nat.log b n) - 1 ≤ Nat.log (b + 1) (bump b n - 1) := by
  rcases eq_or_ne n 0 with hv0 | hv0
  · rw [hv0]; simp
  · by_cases hpp : b ^ Nat.log b n = n
    · rcases Nat.eq_zero_or_pos (Nat.log b n) with he0 | hepos
      · rw [he0, bump_zero]; omega
      · rw [log_bump_pred_of_pow b hb hepos hpp.symm]
    · have hlt : b ^ Nat.log b n < n := by
        have hle := Nat.pow_log_le_self b hv0; omega
      rw [log_bump_pred_of_not_pow b hb hv0 hlt]; omega

/-- A sequence is **Goodstein-like** when it obeys the Goodstein lower-bound recursion at every step:
`a (k+1) ≥ bump (base k) (a k) − 1`. The genuine `goodsteinSeq m` obeys it with equality. -/
def GoodsteinLike (a : ℕ → ℕ) : Prop := ∀ k, bump (base k) (a k) - 1 ≤ a (k + 1)

/-- The leading-exponent operator: `logSeq a k = log_{base k} (a k)`. -/
def logSeq (a : ℕ → ℕ) : ℕ → ℕ := fun k => Nat.log (base k) (a k)

/-- The genuine Goodstein sequence is Goodstein-like (with equality, by definition of the step). -/
theorem goodsteinSeq_goodsteinLike (m : ℕ) : GoodsteinLike (goodsteinSeq m) :=
  fun _ => le_of_eq rfl

/-- **Self-similarity, abstract form.** Every Goodstein-like `a` dominates the genuine Goodstein
sequence seeded at `a 0`: `goodsteinSeq (a 0) k ≤ a k` for all `k`. Induction with `bump_mono`
carrying the step — the `goodsteinSeq` recursion subtracts `1` at *every* step, while `a` does so only
where forced, so `goodsteinSeq (a 0)` is the slowest descent. Generalizes `leadExp_ge_goodsteinSeq_log`
(the case `a = leadExp = logSeq (goodsteinSeq m)`, where `a 0 = log₂ m`). -/
theorem GoodsteinLike.dominates {a : ℕ → ℕ} (ha : GoodsteinLike a) :
    ∀ k, goodsteinSeq (a 0) k ≤ a k := by
  intro k
  induction k with
  | zero => exact Nat.le_of_eq rfl
  | succ k ih =>
    have hb : 2 ≤ base k := Nat.le_add_left 2 k
    have hmono : bump (base k) (goodsteinSeq (a 0) k) ≤ bump (base k) (a k) :=
      bump_mono (base k) hb ih
    have hstep : goodsteinSeq (a 0) (k + 1) = bump (base k) (goodsteinSeq (a 0) k) - 1 := rfl
    have hak := ha k
    rw [hstep]; omega

/-- **The leading exponent of a Goodstein-like sequence is Goodstein-like.** If `a` is Goodstein-like
then so is `logSeq a = (k ↦ log_{base k} (a k))`. Per step: `log_step_ge` gives the recursion lower
bound at `bump (base k) (a k) − 1`, then monotonicity of `Nat.log` in its argument carries it through
`a (k+1) ≥ bump (base k) (a k) − 1`. This is the **level-up** that, iterated, climbs the ordinal
tower. Generalizes `leadExp_step_ge`. -/
theorem goodsteinLike_logSeq {a : ℕ → ℕ} (ha : GoodsteinLike a) : GoodsteinLike (logSeq a) := by
  intro k
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  show bump (base k) (Nat.log (base k) (a k)) - 1 ≤ Nat.log (base (k + 1)) (a (k + 1))
  rw [hbb1]
  exact le_trans (log_step_ge (base k) hb (a k)) (Nat.log_mono_right (ha k))

/-- The `j`-fold iterated leading exponent of a Goodstein-like sequence is Goodstein-like. -/
theorem goodsteinLike_iterate {a : ℕ → ℕ} (ha : GoodsteinLike a) (j : ℕ) :
    GoodsteinLike (logSeq^[j] a) := by
  induction j with
  | zero => exact ha
  | succ j ih => rw [Function.iterate_succ_apply']; exact goodsteinLike_logSeq ih

/-- The seed of the `j`-fold iterated leading exponent is the `j`-fold logarithm of the original seed:
`(logSeq^[j] a) 0 = (log₂)^[j] (a 0)` (each `logSeq` reads `base 0 = 2` at index `0`). -/
theorem logSeq_iterate_zero (a : ℕ → ℕ) (j : ℕ) :
    (logSeq^[j] a) 0 = (Nat.log 2)^[j] (a 0) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show Nat.log (base 0) ((logSeq^[j] a) 0) = Nat.log 2 ((Nat.log 2)^[j] (a 0))
    rw [show base 0 = 2 from rfl, ih]

/-- **The self-similarity TOWER (headline).** The `j`-fold iterated leading exponent of the seed-`m`
Goodstein descent dominates the Goodstein sequence seeded at the `j`-fold logarithm `(log₂)^[j] m`:
`goodsteinSeq ((log₂)^[j] m) k ≤ (logSeq^[j] (goodsteinSeq m)) k`.

* `j = 0`: the value bound `goodsteinSeq m k ≤ goodsteinSeq m k` (trivial).
* `j = 1`: lap-9's `leadExp_ge_goodsteinSeq_log` — the leading exponent dominates `goodsteinSeq (log₂ m)`.
* `j ≥ 2`: each level is one ordinal step up. To certify the descent ordinal `≥ ω^{ω^{···}}` (tower
  of height `j+1`, i.e. `o = ω^j`-flavoured) at step `≈ m`, one needs the `j`-th iterated leading
  exponent `≥ base` there, which via this bound needs `goodsteinSeq ((log₂)^[j] m) (m−2) ≥ m`, i.e. a
  length bound `goodsteinLength ((log₂)^[j] m) ≥ 2m`. The deeper seed `(log₂)^[j] m` is small, so this
  needs an increasingly strong length bound — supplied by *bootstrapping the domination already
  proved* (e.g. `f_ω(t) ≤ goodsteinLength t + 2` makes `goodsteinLength ((log₂)^[2] m) ≥ f_ω(log₂log₂m)
  ≫ 2m`). That bootstrap is the next frontier; this lemma is its reusable backbone. -/
theorem iterLeadExp_dominates (m j : ℕ) :
    ∀ k, goodsteinSeq ((Nat.log 2)^[j] m) k ≤ (logSeq^[j] (goodsteinSeq m)) k := by
  have hgl : GoodsteinLike (logSeq^[j] (goodsteinSeq m)) :=
    goodsteinLike_iterate (goodsteinSeq_goodsteinLike m) j
  have hgz : goodsteinSeq m 0 = m := rfl
  have h0 : (logSeq^[j] (goodsteinSeq m)) 0 = (Nat.log 2)^[j] m := by
    rw [logSeq_iterate_zero, hgz]
  intro k
  have hd := hgl.dominates k
  rwa [h0] at hd

/-- Anti-vacuity: at `j = 1` the tower reproduces lap-9's self-similarity verbatim. -/
example (m k : ℕ) :
    goodsteinSeq (Nat.log 2 m) k ≤ Nat.log (base k) (goodsteinSeq m k) :=
  iterLeadExp_dominates m 1 k

end LeanFormalizations.Logic.Goodstein
