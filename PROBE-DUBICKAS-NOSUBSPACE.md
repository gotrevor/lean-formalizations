# PROBE — Dubickas Theorem 1 without Lemma 6 (phase 9)

**Status (2026-09-28): PARTIALLY CLOSED — the rational-power case is now unconditional (from
`Ridout1957`); the residual core is exactly Corvaja–Zannier's pseudo-Pisot dichotomy.**

After phase 8, the three ⚓ OEIS-linked headlines in
`NumberTheory/Transcendence/Dubickas.lean` rest on a single hypothesis, `Dubickas2022`
(Dubickas's Lemma 6, from Corvaja–Zannier 2004 via the `p`-adic Subspace Theorem).  It is
consumed exactly once, in `exists_pisot_pow` (`DubickasPisot.lean`), at `q = 2`, `s_n = 2ⁿ`.

## What Lemma 6 actually is

Dubickas (2022), p. 574–575, builds Lemma 6 out of three cited pieces:

| his label | content | strength |
|---|---|---|
| Lemma 3 | Corvaja–Zannier's main theorem (Acta Math. 193 (2004), p. 177) at `δ = 1`, `u = α^(s_n)`, `Γ = {α^t}`: if `q α^(s_n)` is **pseudo-Pisot** for only finitely many `n`, then `‖q α^(s_n)‖ ≥ (1−ε)^(s_n)` eventually | **`p`-adic Subspace Theorem** (Schlickewei) |
| Lemma 4 | CZ's Lemma 4: if the trace of `q_n α^(s_n)` is a nonzero integer and `log q_n = o(n)`, then `α` is an `ℓ`-th root of a rational or an algebraic integer | number-theoretic, *not* subspace |
| Lemma 5 | pseudo-Pisot infinitely often ⇒ some `α^(s_m)` is Pisot | elementary, given Lemma 4 |

Lemma 6 = Lemma 3 ∨ Lemma 5.  **All of the subspace strength sits in Lemma 3.**

## What this lap closed, unconditionally

`DubickasNoSubspace.lean` (all sorry-free unless marked):

* `Diophantine.mahler_mul_of_ridout1957` (in `NumberTheory/Diophantine/Edges.lean`) —
  **Mahler (1957 II) with a positive integer multiplier**: for `u > v ≥ 2` coprime and `q ∈ ℕ`,
  `‖q (u/v)ⁿ‖ > e^(−εn)` for all large `n`, derived from `Ridout1957` by Mahler's §3 route with
  `ϑ = q`, `c = 2q`, `p = round(q αⁿ)·vⁿ`, `Q = uⁿ`.  (`Literature.Mahler1957` is the `q = 1`
  case Saito quotes; Dubickas's §2 remark needs the multiplier, and so do we, because our
  approximants are half-integers: `‖2α^(2ⁿ)‖` small does **not** bound `‖α^(2ⁿ)‖`.)
* `round_dist_le_of_bnd` — the hypotheses `2 y_n ∈ ℤ`, `|y_n − α^(2ⁿ)| ≤ C α^(−2ⁿ)` say exactly
  `‖2 α^(2ⁿ)‖ ≤ e^(−(log α / 2) 2ⁿ)` for large `n`.
* `isPisot_of_rat_den_one` — a rational integer `> 1` is Pisot (linear minimal polynomial, so no
  other conjugates to bound).
* `exists_pisot_pow_of_rat`, `exists_pisot_pow_of_pow_rat` — **if `α^(2^a)` is rational for some
  `a`, the conclusion of Lemma 6 holds with no hypothesis beyond `Ridout1957`.**  This is exactly
  the route Dubickas sketches in his §2 for Wagner–Ziegler's Theorem 1.
* `exists_pisot_pow_noD (hR : Ridout1957)` — reduces the full statement to the one residual:

## The obstruction, precisely

`exists_pisot_pow_pseudoPisot_core` (the one `sorry` in `src/`):

> `α > 1` algebraic, **no power `α^(2^a)` rational**, `2 y_n ∈ ℤ`,
> `|y_n − α^(2ⁿ)| ≤ C α^(−2ⁿ)` ⟹ some `α^(2^m)` is Pisot.

Why the elementary tools do not reach it:

1. **Archimedean Liouville/Roth is vacuous here.**  Put `θ_N = 2α^N − k_N` with
   `k_N = 2y_n`, `N = 2ⁿ`.  If `α` is an algebraic integer, `∏_σ σ(θ_N) ∈ ℤ ∖ {0}`, so
   `∏_{σ≠1}|k_N − 2σ(α)^N| ≥ 2^{−d}/|θ_N| ≥ α^N/(2^d C)`.  That is a **lower** bound on the
   conjugate product, i.e. precisely the inequality `M(α) ≥ α` that holds for every algebraic
   number; it carries no information.  Getting an **upper** bound on that product is the same as
   knowing the conjugates are small — what we are trying to prove.  Roth/Ridout applied to `α^N`
   likewise only says `H(α^N) ≳ α^N`.  This kills the first lead in the file header.
2. **Degree 1 is already Mahler's problem.**  For `α = p/q` non-integral, the product formula
   gives only `|θ_N| ≥ 1/(2q^N)`, which is *weaker* than the hypothesis `|θ_N| ≤ 2Cα^{−N}`
   exactly when `p < q²` — e.g. `α = 3/2`, where the required statement is Mahler's problem on
   `‖q(3/2)ⁿ‖`.  So even the rational case is not elementary; it is closed above **only** because
   this repo has `Ridout1957 ⇒ Mahler1957` as a theorem (phase 5) and the same route gives the
   multiplier form.  Sparse exponents `N = 2ⁿ` are also why Pisot's classical
   `∑‖λβⁿ‖² < ∞ ⇒ β` Pisot theorem is unavailable: it needs *all* `n`.
3. **The Böttcher/Mahler-method lead (second lead in the file header) is refuted.**
   `α = Φ_c(y_0)` with `Φ_c ∘ f = Φ_c²`, `f(z) = z² − c`.  Mahler's method needs a functional
   equation `F(z^p) = R(z, F(z))` with `R` rational; conjugating `f` to `z ↦ z²` is what `Φ_c`
   itself does, and `Φ_c` is not algebraic, so no Mahler-method transcendence criterion
   (Nishioka's included) applies.  Nothing was gained over the dynamical formulation.

## The smallest literature `Prop` that closes it (proposal — deliberately *not* stated in `Literature/`)

Two candidates, in increasing generality; either one suffices and both are strictly more
canonical than `Dubickas2022`, because they are the *published* statements rather than Dubickas's
packaging of them.

1. **`CorvajaZannier2004` (his Lemma 3) — recommended.**  With a `def IsPseudoPisot (z : ℂ)`
   (`1 < ‖z‖`, all other conjugates in the open unit disc, `trace z ∈ ℤ`):
   for `α > 1` algebraic, `q : ℕ` positive, `s : ℕ → ℕ` strictly monotone, if
   `{n | IsPseudoPisot (q α^(s n))}` is finite then `∀ 0 < ε < 1, ∃ n₀, ∀ n ≥ n₀,
   (1 − ε)^(s n) ≤ ‖q α^(s n)‖`.  This is CZ 2004, main theorem, p. 177, at `δ = 1`,
   `u = α^(s n)`, `Γ = {α^t}`.  Deriving `exists_pisot_pow_pseudoPisot_core` from it then needs
   CZ's Lemma 4 + Dubickas's Lemma 5 (elementary; Lemma 5's rational-root branch is the `v = 1`
   argument we already formalized in `exists_pisot_pow_of_rat`).
2. **`SchlickeweiSubspace` — the `p`-adic Subspace Theorem** itself (Schlickewei 1977), in the
   `Literature/Diophantine` idiom (finitely many `S`-unit-scaled solutions of a linear-form
   inequality lie in finitely many proper subspaces).  Strictly deeper, reusable by the Catalan
   and Mills threads, but CZ 2004 → our core is then a multi-lap formalization of its own.

A third, narrower option worth recording: our situation has an **exact recursion**
`y_{n+1} = y_n² − c`, hence `2α^{2^n}δ_n → c` (so `y_n = α^{2ⁿ} + c/(2α^{2ⁿ}) + O(α^{−3·2ⁿ})`).
Nothing in the obstruction above is improved by it: the conjugate sequences `σ(δ_n)` satisfy the
same recursion, which is an identity, not new information at the non-archimedean places.

## Recommended next step

Do **not** take option 2 first.  Option 1 splits the residual into one subspace-strength `Prop`
plus two genuinely elementary lemmas (CZ Lemma 4, Dubickas Lemma 5), which is the same shape that
made phase 5 (`Ridout1957 ⇒ Mahler1957`) and phase 8 (Lemma 8 elimination) work.  The `hD` on the
`Dubickas.lean` headlines cannot be dropped until the core is closed; it must not be routed
through a `sorry`.
