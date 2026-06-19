# HANDOFF — lean-formalizations (2026-06-19, lap closing A2/A3 + reducing A4)

## 👉 READ `DIRECTION.md` FIRST. UNBOUNDED expedition (growth theory behind Goodstein/Kirby–Paris). No self-stop.

## 🎉 This lap: both index-monotonicity cruxes CLOSED; A4 reduced to one sharp core

Branch `no-three-in-line`. Repo builds GREEN (8287 jobs). Sorries remaining: **exactly one**
math sorry — `fastGrowing_lt_of_lt_tower` in `Domination.lean` (the A4 index-domination core).

### What got proved (all axiom-clean `[propext, Classical.choice, Quot.sound]`)
- **A3 crux CLOSED** — `fastGrowing_bachmann_reach` (`Basic.lean`): for a limit `o` with
  fund seq `f`, `Reaches (n+1) (f(n+1)) (f n)`. Proved by structural recursion on the
  notation. This is the **Bachmann property** of the CNF fundamental sequences (the descent
  of `o[n+1]` at budget `n+1` passes *exactly* through `o[n]`, because `ONote` descends
  tails-first and coefficients pass through every integer). Consequently:
- **A2 CLOSED** — `fastGrowing_monotone : Monotone (fastGrowing o)` for **every** `o`.
  Same for the **Hardy hierarchy**: `hardy_monotone` (`Hardy.lean`), via a monotonicity-
  aware transfer `hardy_le_of_reaches` (Hardy's successor step shifts the argument, so it
  absorbs the `+1` using IH monotonicity).
- **The `Reaches` engine** (`Basic.lean`): `Reaches x β α` (structural descent), with
  `Reaches.trans`, `reaches_le`, `fastGrowing_le_of_reaches` (value transfer),
  `reaches_zero`, `Reaches.oadd_tail`, `reaches_coeff_step'/chain`, `reaches_omega_pow_lift`.
  These are the reusable core; the A4 core needs to *extend* them (see below).
- **A4 structural prereqs** (`Domination.lean`, all axiom-clean):
  `repr_lt_opow_repr` (`repr o < ω^repr o` for NF `o`, ELEMENTARY structural induction —
  no ε₀ fixed-point machinery), `tower`/`tower_succ`/`tower_NF`/`tower_lt_succ`/
  `tower_strictMono`, `repr_tower_succ`, **`tower_cofinal`** (every NF `o` is below some
  tower level). `fastGrowing_lt_fastGrowingε₀` (**A4 headline**) is PROVED modulo the one core.

### Earlier-lap worked examples (now subsumed by A2, kept as documentation)
`fastGrowing_monotone_omega/'`, `_omega_mul`, `_omega_sq`, `fastGrowing_omega_sq_index_step`,
`fastGrowing_monotone_of_succ_chain_limit`, `hardy_monotone_omega`, etc.

## ⏭️ NEXT — the single open core (the A4 index domination)
`fastGrowing_lt_of_lt_tower {o} (n) (1 ≤ n) (o < tower n) : fastGrowing o n < fastGrowing (tower n) n`.

This reduces (via `fastGrowing_le_of_reaches` + one strict step `lt_fastGrowing`) to the
**general Bachmann reachability**:

> **`reaches_of_lt`** *(the real target)*: for NF `α, β` with `α < β` and budget `x` at least
> the "norm" of `α` (the max finite coefficient/tail appearing in `α`'s CNF), `Reaches x β α`.

Then `Reaches n (tower n) o` follows for `n ≥ max(k, norm o)` (k from `tower_cofinal`).

**Three attack paths for `reaches_of_lt`** (see `ON-LINE-REQUEST.md` for the literature ask):
1. **Direct WF recursion on β** (most promising). Cases on `fundamentalSequence β`:
   - succ `β = γ+1`: `α ≤ γ`; if `α = γ` one succ step, else succ step + recurse `Reaches x γ α` (γ<β).
   - limit `g`: need `α < g x` to descend to `g x` and recurse. From `FundamentalSequenceProp`,
     `∃ i, α < g i`; with `g` increasing, `x ≥ i ⟹ α < g x`. The budget/`norm` condition is
     exactly "x dominates every such `i` along the descent". Formalize `norm` so this closes.
   - The hard bookkeeping: pin the right `norm α` so the limit-case `α < g x` always holds.
2. **Generalize `fastGrowing_bachmann_reach`'s structural induction.** It already proves the
   consecutive case `o[n+1] → o[n]`; reachability of an arbitrary `α < β` is the same machine
   with the target not fixed to `o[n]`. Reuse `reaches_zero`, `oadd_tail`, `reaches_omega_pow_lift`.
3. **Feed Aristotle** the self-contained `reaches_of_lt` (inline `Reaches` + the needed
   `fundamentalSequence` facts as a bounded problem). One job (`ef77034e…`) was already RUNNING
   (unknown provenance) at lap end — submit when the slot frees.

## Other open ladder targets (DIRECTION §ladder) — untouched, lower priority than the A4 core
- **B4**: `H_{ω^α} = f_α` (Hardy↔fast-growing). NOTE mathlib's `ω[n]=n+1` breaks the clean
  identity: measured this lap `H_{ω^0}=f_0` exactly, `H_{ω^1}=f_1+1`, but `H_{ω^2}(2)=23 ≠
  f_2(2)+1=9` — so it is NOT a constant shift; the textbook `H_{ω^α}=f_α` assumes `ω[n]=n`.
  B4 here needs either a reformulated statement or a different fundamental-sequence
  convention. Genuine long-horizon target; don't expect a clean identity.
- **C2/C3**: Goodstein length ↔ hierarchy bridge (reuse `Logic/Goodstein/Engine` ε₀-descent).

## Discipline
- Five completed threads (Transcendence, Constructible, Curtis, PowerTower, Goodstein) stay
  at 0 math axioms — do not touch. Work only in `Logic/FastGrowing/*` + `Logic/Goodstein/{Length,Growth}`.
- Commit every green `lake build`. NEVER push. Verify `#print axioms` clean on closed theorems.
- Reference corpus (cross-lap memory, NOT auto-loaded): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Older HANDOFFs in `archive/handoff/`.
