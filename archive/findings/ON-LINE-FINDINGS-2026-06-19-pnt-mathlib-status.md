# Online findings — PNT / mathlib status (closes the HJSW-frontier online request)

**Date:** 2026-06-19 (host fulfiller session)
**Resolves:** `ON-LINE-REQUEST.md` — all three asks (Nagura 6/5 inequality; refined elementary
Chebyshev constants; `weakPNT` discharge). The request file's own UPDATE 2 already declared "No open
online requests remain"; this note records the **independent online verification** and clears the badge.
**Sources read:** mathlib4 docs `Mathlib.NumberTheory.LSeries.PrimesInAP`; `AlexKontorovich/PrimeNumberTheoremAnd`
(GitHub repo + blueprint); the project's Wiener–Ikehara section; local repo state (`git log`, toolchains).

---

## Bottom line: nothing left to fetch — the box self-resolved it on-box

The live lap **discharged `weakPNT`** before/while this was researched (commit `9f0975f`,
"DISCHARGE weakPNT — flagship 3/2−o(N) now axiom-clean"). Verified structurally:
`PrimeGap.lean:1157` now reads

```lean
theorem weakPNT : Chebyshev.psi ~[atTop] (fun x ↦ x) := WeakPNT''
```

— it is a **theorem**, no longer `axiom weakPNT`. `WeakPNT''` is the in-repo **port** of the
PrimeNumberTheoremAnd Wiener tower (bricks 1–2 + the SmoothExistence/Asymptotics support files).
(Compiler-level `#print axioms` not run here — a treadmill lap is actively editing the repo; the
axiom audit is left to the box. The structural change `axiom → theorem := WeakPNT''` is confirmed.)

The Nagura (6/5) and refined-Chebyshev asks are **moot**: PNT (ψ(x)~x) leapfrogs the elementary
`5/4` ceiling straight to the headline `3/2 − o(N)`, so the sharper elementary constants were never
needed once the port landed.

## Independent online verification (the part the box could not check offline)

1. **mathlib4 still does NOT contain the PNT.** As of today its prime-distribution frontier is
   `Mathlib.NumberTheory.LSeries.PrimesInAP` = **Dirichlet's theorem only** (infinitely many primes
   in each coprime residue class: `Nat.infinite_setOf_prime_and_eq_mod` etc.). There is **no**
   declaration asserting `Chebyshev.psi ~ x` or `π(x) ~ x/log x`. ⟹ There is currently **nothing in
   mathlib to cite** for `weakPNT`; the port is the only route. The KB note
   `mathlib-pnt-gap-is-only-tauberian` (v4.29.1: ζ≠0 on Re=1 present, only Wiener–Ikehara missing) is
   corroborated.

2. **PrimeNumberTheoremAnd (Kontorovich / Tao) is the right source, and it does have WeakPNT.**
   The project formalizes PNT via the **Wiener–Ikehara Tauberian theorem**; `WeakPNT''`
   (`Chebyshev.psi ~ x`, the Stoll-style "assuming Wiener–Ikehara" piece) is proven there. Latest
   release **v4.30.0, dated 2026-06-03**. Stated future goal: **upstream into mathlib** "in the near
   future" (plus explicit error term + primes-in-AP asymptotics).

3. **Why the lake-dep route was correctly abandoned (commit `7aee6ce` "DEAD on-box").** Confirmed
   version skew:
   - this repo: `leanprover/lean4:v4.29.1`
   - local PNTAnd clone: `leanprover/lean4:v4.29.0` (off-by-patch)
   - PNTAnd's shipped v4.30.0 release: newer mathlib still.

   A transitive git dependency would need network egress (box is network-isolated) **and** a matching
   mathlib rev. Porting the ~525 lines of `WeakPNT''` source was the correct call — it matches the
   standing KB note `pntand-not-lake-dependable-offline` ("port source instead").

## Forward-looking (for a future lap — not a blocker now)

- **The port is permanent *until* mathlib ships PNT.** When a mathlib `PrimeNumberTheorem` /
  Wiener–Ikehara declaration lands (the PNT+ project's explicit upstreaming goal), the ~525-line port
  can be replaced by a **one-line mathlib citation** and `weakPNT` becomes directly citable. Until
  then there is nothing to swap to. Watch `Mathlib/NumberTheory/LSeries/` for a PNT file.
- **The Nagura / refined-elementary-Chebyshev path is not needed and not worth reviving** for the
  `3/2 − o(N)` headline. The box already proved the elementary lower constant caps at
  `θ(x) ≳ (log4/2)x ≈ 0.69x` (true `θ(x)~x` needs PNT), and `5/4`/`6/5` need the sharper bound. If the
  *exact* `5/4` elementary constant is ever wanted independently of PNT, the reference line is the
  explicit-bounds literature (Rosser–Schoenfeld 1962; Nagura 1952) — but this is **non-blocking** and
  was **not** transcribed this session, since PNT supersedes it.

**No open online requests remain.** Badge cleared by removing `ON-LINE-REQUEST.md`.
