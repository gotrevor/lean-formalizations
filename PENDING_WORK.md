# PENDING_WORK — no-three-in-line / HJSW frontier (branch `ntl-hjsw`)

Inventory of open items + attack paths (per `how-to-get-unblocked.md`). Refreshed 2026-06-19.
(This isolated clone's focus is solely the HJSW frontier; the main-branch threads — Curtis,
power-tower, constructibles, transcendence, Goodstein — are complete & axiom-clean, recorded in
`STATUS.md` and git history. Do not reopen them here.)

## Open items (full `#print axioms` + `grep sorry` sweep of `src/.../NoThreeInLine/`)

1. **`hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2*p)`** (`Hyperbola.lean`) — the ONLY open `sorry`.
   The covering count of the HJSW `3N/2` lower bound. Everything else is proven & axiom-clean:
   2N upper bound, Erdős Θ(N), hyperbola-arc non-collinearity, the decidable `det3=0 ⟺ Collinear`
   certificate (`decNoThree_iff`), and native-decide witnesses at p=5 and p=7.

Single-crux target ⇒ "broaden" mostly means *broaden the attack on this crux*.

## Three attack paths for `hjsw_lower`

### Path A — get the real construction from the HJSW 1975 paper (filed; network-blocked)
`ON-LINE-REQUEST.md` asks for the explicit (multi-)curve set + cross-curve non-collinearity proof.
When `ON-LINE-FINDINGS-*.md` lands: build the candidate set, validate via `native_decide (decNoThree …)`
at p=5,7,11, port to a clean `def`, prove (reuse `hyperbola_noThreeCollinear` for intra-curve triples;
the new content is cross-curve). Highest-confidence path — the construction is *known*, just not here.

### Path B — find a generalizable construction computationally, then prove it
The `decNoThree` certificate is an EXACT iff, so candidates are cheap to refute/confirm.
- **Established:** a single modular hyperbola `xy≡k` cannot reach `3(p−1)` at p=7 (max ≤17) for any k
  ⇒ **need ≥2 curves**. Naive multi-block arc unions also fail.
- **Obstruction characterized:** single-curve collinearities are all **slope ±1 alignments** —
  `(r,s)` & `(r+p,s+p)` share `y=x+(s−r)`, and residues with equal `s−r` pile onto it (for p=7,k=1:
  lines `y=x`, `y=x+2`, `y=−x+13` each carry 4 lifts). Doubling in BOTH coords creates them.
- Update: greedy over the union of 2 hyperbola-lift curves (all key pairs, p=7) caps at ≤17 too —
  so even 2-curve hyperbola-LIFT unions don't easily give 18. HJSW likely uses non-hyperbola or a
  cleverer lift/curve family; do not keep brute-forcing hyperbola variants — get the paper (Path A).
- Next experiments: (i) search the union of 2 curves' lifts (all key pairs) for an 18-set + decode;
  (ii) design a per-residue lift rule that provably dodges slope-±1 alignments (no `s−r` repeats with a
  collinear third), let a 2nd curve fill the deficit; (iii) validate any rule across p=5,7,11,13 before
  the general Lean proof.

### Path C — special-case ladder (partial, native-certified) while A/B mature
Extend the verified witness ladder (p=5 ✓ `hjsw_lower_five`, p=7 ✓ `hjsw_lower_seven`) to p=11, p=13
via greedy + `native_decide`. Anti-vacuity locks confirming achievability; do NOT generalize to the
headline proof, but keep the lap productive when A is blocked and B hasn't cracked.

## Done this lap
Path B obstruction analysis (slope-±1 characterization, above + in `ON-LINE-REQUEST.md`); Path C
(p=7 witness added & verified). **Next lap:** act on findings (A) the moment they land; else push
B(i)/B(ii) — design + test a 2-curve rule that dodges the slope-±1 obstruction.
