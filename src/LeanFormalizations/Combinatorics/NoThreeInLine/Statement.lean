/-
# No-three-in-line problem — audit surface

This is the faithful **audit surface** for the no-three-in-line formalization. The
load-bearing definitions are in `Defs.lean`:

* `IsGridSet N s` — `s ⊆ [0,N) × [0,N)`;
* `NoThreeCollinear s` — no three *distinct* points of `s` are `Collinear ℝ` (every line,
  every slope), the corrected form of `formal-conjectures`' `Green72.AllowedSet`;
* `maxNoThreeInLine N` — the largest such `s.card`.

Two results, both fully proven and axiom-clean (`#print axioms` = the bare trust base
`[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axiom):

* **Upper bound** (`maxNoThreeInLine_le`): `maxNoThreeInLine N ≤ 2N`. Pigeonhole on rows.
  The only fully general theorem of the problem; this is `Green72.allowedSetSize_le`, a
  `sorry` stub upstream, here discharged.
* **Erdős lower bound** (`erdos_exists_parabola`, `prime_le_maxNoThreeInLine`): for prime
  `p` the parabola `(i, i² mod p)` gives `p` points with no three collinear. With Bertrand's
  postulate this lifts to **every** `N ≥ 2` (`maxNoThreeInLine_gt_half`), pinning the order
  at `Θ(N)` (`maxNoThreeInLine_order`).

* **Hall–Jackson–Sudbery–Wild lower bound** (`hjsw_lower_bound`): for prime `p`, the `2p × 2p`
  grid admits `3(p−1)` points with no three collinear — i.e. `3N/2 − 3` at `N = 2p` — via the
  closed-form sheared-hyperbola construction `shearSel p` (proven axiom-clean in `Hyperbola.lean`).
  Via Bertrand this lifts to a `3N/4` lower bound for **every** `N ≥ 4` (`maxNoThreeInLine_ge_three_quarters`),
  improving the Erdős `Θ(N)` constant from `1/2` to `3/4`.

What is **not** here (the frontier): the Main Conjecture (open). See `README.md` / `PLAN.md`.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.UpperBound
import LeanFormalizations.Combinatorics.NoThreeInLine.Parabola
import LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola
import Mathlib.NumberTheory.Bertrand

namespace LeanFormalizations.NoThreeInLine

/-! ### Upper bound -/

/-- **The `2N` upper bound.** No set of grid points with no three collinear exceeds `2N`. -/
theorem upper_bound {N : ℕ} {s : Finset (ℕ × ℕ)}
    (hg : IsGridSet N s) (h3 : NoThreeCollinear s) : s.card ≤ 2 * N :=
  card_le_two_mul hg h3

/-- The grid maximum is at most `2N`. -/
theorem maxNoThreeInLine_upper (N : ℕ) : maxNoThreeInLine N ≤ 2 * N :=
  maxNoThreeInLine_le

/-! ### Erdős lower bound -/

/-- **Erdős's lower bound (existence form).** For every prime `p`, the `p × p` grid contains
`p` points with no three collinear — the parabola `(i, i² mod p)`, `i ∈ [0,p)`. -/
theorem erdos_exists_parabola {p : ℕ} (hp : p.Prime) :
    ∃ s : Finset (ℕ × ℕ), IsGridSet p s ∧ NoThreeCollinear s ∧ s.card = p :=
  ⟨parabola p, parabola_grid hp.pos, parabola_noThreeCollinear hp, parabola_card p⟩

/-- **Erdős's lower bound.** For prime `p`, the grid maximum is at least `p`. -/
theorem prime_le_maxNoThreeInLine {p : ℕ} (hp : p.Prime) : p ≤ maxNoThreeInLine p :=
  le_csSup (bddAbove_grid p)
    ⟨parabola p, (parabola_card p).symm, parabola_grid hp.pos, parabola_noThreeCollinear hp⟩

/-- **Erdős's lower bound for all `N ≥ 2`** (via Bertrand's postulate): the grid maximum
exceeds `N/2`. A prime `p ∈ (N/2, N]` gives a parabola of `p > N/2` points inside `[0,N)²`. -/
theorem maxNoThreeInLine_gt_half {N : ℕ} (hN : 2 ≤ N) : N / 2 < maxNoThreeInLine N := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  have hpN : p ≤ N := hhi.trans (by omega)
  refine hlo.trans_le (le_csSup (bddAbove_grid N) ?_)
  exact ⟨parabola p, (parabola_card p).symm,
    (parabola_grid hp.pos).mono hpN, parabola_noThreeCollinear hp⟩

/-! ### Order Θ(N) -/

/-- **The grid maximum has order `Θ(N)`.** At any prime `p`, `p ≤ maxNoThreeInLine p ≤ 2p`:
Erdős's parabola from below, the pigeonhole ceiling from above. -/
theorem maxNoThreeInLine_order {p : ℕ} (hp : p.Prime) :
    p ≤ maxNoThreeInLine p ∧ maxNoThreeInLine p ≤ 2 * p :=
  ⟨prime_le_maxNoThreeInLine hp, maxNoThreeInLine_le⟩

/-! ### Hall–Jackson–Sudbery–Wild `3N/2` lower bound -/

/-- **The HJSW lower bound.** For prime `p`, the `2p × 2p` grid contains `3(p−1)` points with no
three collinear — the closed-form sheared-hyperbola construction. At `N = 2p` this is `3N/2 − 3`,
beating the `2N`-pigeonhole gap below the trivial `2N` ceiling. -/
theorem hjsw_lower_bound {p : ℕ} (hp : p.Prime) : 3 * (p - 1) ≤ maxNoThreeInLine (2 * p) :=
  hjsw_lower hp

/-- **Monotonicity of the grid maximum.** A no-three-collinear set inside `[0,M)²` also sits
inside the larger box `[0,N)²`, so `maxNoThreeInLine` is monotone. (General structural fact;
used to embed any sub-grid construction.) -/
theorem maxNoThreeInLine_mono : Monotone maxNoThreeInLine := by
  intro M N hMN
  refine csSup_le_csSup (bddAbove_grid N) ⟨0, ∅, by simp [IsGridSet, NoThreeCollinear]⟩ ?_
  rintro n ⟨s, rfl, hg, h3⟩
  exact ⟨s, rfl, hg.mono hMN, h3⟩

/-- **The prime-gap interface for HJSW.** Any prime `p` with `2p ≤ N` embeds its `2p × 2p` sheared
construction `shearSel p` into the `N × N` grid, so `3(p−1) ≤ maxNoThreeInLine N`. This isolates the
*combinatorial* HJSW content (the `shearSel` construction) from the *number-theoretic* input (which
prime is available below `N/2`): plug in Bertrand for the `3/4` constant below, a Nagura-type gap for
`5/4`, or a prime-number-theorem gap for the full `3/2 − o(1)`. -/
theorem maxNoThreeInLine_ge_of_two_mul_prime_le {N p : ℕ} (hp : p.Prime) (h2p : 2 * p ≤ N) :
    3 * (p - 1) ≤ maxNoThreeInLine N :=
  le_csSup (bddAbove_grid N)
    ⟨shearSel p, (shearSel_card hp).symm, (shearSel_grid hp).mono h2p, shearSel_noThree hp⟩

/-- **HJSW for all `N ≥ 4`** (via Bertrand's postulate). A prime `p ∈ (N/4, N/2]` gives the sheared
construction `shearSel p` of `3(p−1) ≥ 3·⌊N/4⌋` points inside `[0, 2p)² ⊆ [0, N)²`. This pins the
`Θ(N)` lower constant at `3/4`, improving on Erdős's `1/2` (`maxNoThreeInLine_gt_half`). -/
theorem maxNoThreeInLine_ge_three_quarters {N : ℕ} (hN : 4 ≤ N) :
    3 * (N / 4) ≤ maxNoThreeInLine N := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 4) (by omega)
  have := maxNoThreeInLine_ge_of_two_mul_prime_le hp (show 2 * p ≤ N by omega)
  omega

/-- **State of the art at even grid sizes.** For prime `p`, the `2p × 2p` grid maximum is sandwiched
`3(p−1) ≤ maxNoThreeInLine (2p) ≤ 4p` — the HJSW construction from below, the pigeonhole ceiling from
above (`= 2·(2p)`). At `N = 2p` this is `3N/2 − 3 ≤ maxNoThreeInLine N ≤ 2N`: the best proven
two-sided bounds of the no-three-in-line problem. -/
theorem maxNoThreeInLine_two_mul_prime_bounds {p : ℕ} (hp : p.Prime) :
    3 * (p - 1) ≤ maxNoThreeInLine (2 * p) ∧ maxNoThreeInLine (2 * p) ≤ 4 * p :=
  ⟨hjsw_lower hp, by have := maxNoThreeInLine_le (N := 2 * p); omega⟩

/-- **Best proven two-sided bounds, all `N ≥ 4`.** `3·⌊N/4⌋ ≤ maxNoThreeInLine N ≤ 2N` — HJSW via
Bertrand from below, pigeonhole from above. -/
theorem maxNoThreeInLine_bounds {N : ℕ} (hN : 4 ≤ N) :
    3 * (N / 4) ≤ maxNoThreeInLine N ∧ maxNoThreeInLine N ≤ 2 * N :=
  ⟨maxNoThreeInLine_ge_three_quarters hN, maxNoThreeInLine_le⟩

end LeanFormalizations.NoThreeInLine
