# Handoff: π-transcendence COMPLETE modulo one Aristotle fact (`b7252abe`)

**Date**: 2026-06-16 (π algebraic-part lap) · **Branch**: main · **HEAD**: `d3560bc`

## 🎯 Headline
The **entire algebraic part of Lindemann's π-transcendence** is now assembled, every step
machine-checked and **axiom-clean** (`[propext, Classical.choice, Quot.sound]`), reduced to a
**single open input**. The capstone

```
MonicRootSums.transcendental_pi_of_subsetSumEsymm
    (hsse : ∀ (n) (θ : Fin n → ℂ) (G : ℚ[X]), G.Monic →
        (G.map (algebraMap ℚ ℂ)).roots = (univ : Finset (Fin n)).val.map θ →
        ∀ j, ((univ.powerset.val.map (fun t => ∑ k ∈ t, θ k)).esymm j) ∈ range (algebraMap ℚ ℂ))
    : Transcendental ℚ Real.pi
```

`hsse` is **exactly** the statement of Aristotle job **`b7252abe`** (`subsetSum_esymm_rational`):
the elementary symmetric functions of the multiset of subset-sums of the conjugates of `iπ`
are rational. That is the **only** remaining mathematical input for π.

## ✅ What's done this lap (19 commits `b2b56f9`…`d3560bc`, all axiom-clean)
New files `NumberTheory/Transcendence/PiLindemann.lean` + `MonicRootSums.lean`:
- **Combinatorial reduction (★)**: `prod_one_add_exp_eq_sum_subsetSum`, `pi_exp_relation`
  (`e^{iπ}=−1 ⟹ K + ∑_{σ_t≠0} e^{σ_t}=0`).
- **Analytic engine**: `no_intPoly_exp_relation` (general non-monic; the full integer-`N`/mod-`p`
  contradiction over an arbitrary `F.aroots`, generalizing the `e` proof).
- **`hsum` bridge**: `aroots_integralNormalization`, `hsum_of_monic_rootsum` (discharge the
  analytic hypothesis for ANY integer `F` from the monic case).
- **Fact (a) PROVEN**: `sum_aeval_roots_int` (+ `roots_esymm_int`, `power_sum_int`) — produced
  by Aristotle (`9a19f72e`) and **independently kernel-verified** here.
- **Descent**: `esymm_aroots_mem_range` (esymm of conjugates rational), `subsetSum_poly_lifts`
  (conjugate poly descends to `ℚ[X]` from `hsse`).
- **Glue**: `exists_ratPoly_removeZeroRoots` (drop the `X^K` zero roots),
  `exists_intPoly_aroots_eq` (clear denominators to integer `F`).
- **Capstones**: `subsetSum_relation_impossible` (+ `_of_conjugatePoly`, `_of_esymm`),
  `transcendental_pi_of_subsetSumEsymm`.

`lake build` green (8272 jobs); `src/` sorry-free; repo's only math axiom is still the cited
`hermite_lindemann`.

## 🎬 Next actions (in order)
1. **Harvest `b7252abe`** (likely IDLE by now). `aristotle download b7252abe... --destination
   x.tar.gz; tar xzf`. **VERIFY in-kernel** (`lake env lean` a tmp file) and **`#print axioms`
   clean** before trusting (Aristotle pins v4.28; we're v4.29.1). The returned theorem proves
   `subsetSum_esymm_rational` in the form of `hsse` (modulo trivial renaming). Port it into a
   new file (or `MonicRootSums.lean`), namespaced.
   - If it came back with an isolated `sorry` (open-problem wrapper) or fails to verify:
     prove locally. **Validated local-proof roadmap** (the approach was checked to compile up
     to the two hard sub-lemmas this lap):
     1. `map_multiset_esymm (φ : R →+* S) (s) (j) : (s.map φ).esymm j = φ (s.esymm j)` —
        PROVEN (clean, ~5 lines: `Multiset.esymm` + `map_multiset_sum` + `powersetCard_map` +
        `Multiset.prod_hom`). Keep this helper.
     2. `Φ_j := (univ.powerset.val.map (fun t => ∑ k ∈ t, MvPolynomial.X k)).esymm j`. Then
        `aeval θ Φ_j = (univ.powerset.val.map (fun t => ∑ k∈t, θ k)).esymm j` (the target LHS),
        via `map_multiset_esymm (aeval θ).toRingHom` + `aeval (∑_{k∈t} X k) = ∑_{k∈t} θ k`.
     3. **Φ_j is symmetric** (`IsSymmetric`): for `σ : Equiv.Perm (Fin n)`,
        `rename σ Φ_j = Φ_j` via `map_multiset_esymm (rename σ).toRingHom`; reduces to
        `univ.powerset.val.map (fun t => t.image σ) = univ.powerset.val` (σ permutes the
        powerset). Prove the latter via `Finset.image` injOn (`(s.image f).val = s.val.map f`)
        + `univ.powerset.image (·.image σ) = univ.powerset`. [the genuine work]
     4. **Fundamental theorem**: `IsSymmetric` ⟹ `Φ_j ∈ symmetricSubalgebra` ⟹
        (`esymmAlgHom_surjective`) `Φ_j = esymmAlgHom P`, so
        `aeval θ Φ_j = aeval (fun i => (univ.val.map θ).esymm (i+1)) P`
        (`esymmAlgHom` def + `aeval_esymm_eq_multiset_esymm`). Each
        `(univ.val.map θ).esymm (i+1) = (G.aroots ℂ).esymm (i+1) ∈ range` (`esymm_aroots_mem_range`,
        already in repo, using `hroots`). A `ℚ`-`aeval` at range-valued points lands in
        `(algebraMap ℚ ℂ).range` (it's a subalgebra). Done.
     Prompt archived: `tools/aristotle/pi-subsetsum-esymm-submitted.txt`.
   - **CLI gotcha** (resubmitting): `aristotle submit` does `Path(prompt).is_file()` which
     raises `ENAMETOOLONG` for any 255+ char run without `/`. Sprinkle `/` (e.g. append
     ` -- ref/x` per line) — see `tools/aristotle/README-cli-gotcha.md`.
2. **Plug in**: `have hsse := <ported subsetSum_esymm_rational>` (adapt to the exact
   signature), then `theorem transcendental_pi : Transcendental ℚ Real.pi :=
   transcendental_pi_of_subsetSumEsymm hsse`. `#print axioms` should be clean.
3. **Kill `hermite_lindemann` at π**: with unconditional `Transcendental ℚ Real.pi`, replace
   `HermiteLindemann.transcendental_pi`'s axiom use; then
   `squaring_the_circle_impossible_uncond` becomes fully axiom-clean. (The general
   `hermite_lindemann` for arbitrary α stays an axiom — only the π instance is now discharged;
   that's all squaring-the-circle needs.) Update STATUS axiom ledger.

## ⚠️ Gotchas
- Re-check `#print axioms` after ANY Aristotle port (`grind`/`simp_all` can inject `sorryAx`).
- `MonicRootSums.lean` uses `import Mathlib` (broad) deliberately — it's the kernel-verified
  Aristotle environment; don't narrow it.
- The `Curtis/Lemma2.lean` lint warnings are intentional — leave them.

## 📁 Key files
- `NumberTheory/Transcendence/PiLindemann.lean` — reduction + analytic engine + descent + glue.
- `NumberTheory/Transcendence/MonicRootSums.lean` — fact (a) + the two final capstones.
- `NumberTheory/Transcendence/HermiteLindemann.lean` — the cited axiom + `transcendental_pi`.
- `PENDING_WORK.md` (item B, refreshed) · `STATUS.md` (refreshed) ·
  `tools/aristotle/` (prompts + CLI gotcha).

---
**→ Next session: harvest `b7252abe`, verify, plug into `transcendental_pi_of_subsetSumEsymm`.
That single step completes π-transcendence and makes squaring-the-circle unconditional. The
whole assembly around it is already machine-checked and axiom-clean — do not re-derive it.**
