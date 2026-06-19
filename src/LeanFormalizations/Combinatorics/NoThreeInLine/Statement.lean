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

What is **not** here (the frontier): the Hall–Jackson–Sudbery–Wild `3N/2` constant, and the
Main Conjecture (open). See `README.md` / `PLAN.md`.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.UpperBound
import LeanFormalizations.Combinatorics.NoThreeInLine.Parabola
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

end LeanFormalizations.NoThreeInLine
