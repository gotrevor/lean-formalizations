# Findings — HJSW `3(p−1)` no-three-in-line construction (the covering / count)

**Request:** `ON-LINE-REQUEST.md`, 2026-06-19 — the genuine content of the `3/2` bound: the explicit
HJSW point set, the grid side `N` vs `p`, and the cross-arc (cross-block) non-collinearity argument.

**Primary source read (gold standard):** R. R. Hall, T. H. Jackson, A. Sudbery, K. Wild,
*Some Advances in the No-Three-in-Line Problem*, **J. Combin. Theory Ser. A 18 (1975) 336–341**,
DOI `10.1016/0097-3165(75)90043-6`. Trevor pulled the actual Elsevier PDF; I read all 6 pages
(Theorem 2 + figure + proof on pp. 339–340) directly and **re-derived the figure layout, the count,
and the reflection argument by hand** to fix OCR errors. So this is faithful to the paper, not a
secondary paraphrase. Cross-checked the headline numbers against three secondary sources (the
"extensible no-three-in-line" arXiv:2209.01447 T₂/M block restatement; arXiv:2512.11469; the
no-(k+1)-in-line literature).

> ⚠️ **The whole `3/2` lives in Theorem 2 of HJSW, and it is NOT "stack doubled arcs."** Your paper
> hunch ("3 translated arcs", "stacking two 2p×2p doubled arcs gives ratio 2, so something must
> obstruct") is the right instinct but the wrong mechanism. The real construction is a **12-of-16
> block "pinwheel"** carved out of a single modular hyperbola `H(k,p)` over a `2p × 2p` grid, and the
> obstruction is a slope-only congruence argument, not an inter-arc intersection count. Details below.

---

## 0. TL;DR (what to formalize)

- Grid side **`N = 2p`** (`p` prime). Point set **`|N_set| = 3(p − 1) = 3(N−2)/2`**. Density → `3/2`.
- One hyperbola `H(k,p) = {(x,y) : xy ≡ k (mod p)}`, any fixed `k ≢ 0`. **No second hyperbola, no
  reflection of the curve.** The `3/2` comes from taking **3 congruent copies** of each of **4
  quadrant-types** of one `p×p` fundamental cell — 12 sub-blocks forming the **outer ring** of a
  4×4 grid of `(p−1)/2 × (p−1)/2` sub-blocks; the **central 2×2 (= set `M`) is discarded.**
- The single load-bearing lemma is **stronger than your current `hyperbola_noThreeCollinear`**: *any*
  line meets `H(k,p)` in **at most two congruence classes mod p** (HJSW "Lemma"). Your arc lemma is
  the special case "one representative per class." Reformulate around the general lemma — the
  12-block argument needs it.
- The cross-block argument is **pure slope bookkeeping**: two congruent points of `N_set` can only be
  joined by a line of slope `0, ∞, 1, −1`; each such slope is shown to admit no third point of `N_set`.

---

## 1. The pieces (faithful, with exact coordinate formulas)

### 1.1 The hyperbola and congruence (HJSW "Definitions", p. 337)
`H(k,p) = { (x,y) ∈ ℤ² : xy ≡ k (mod p) }`, `k ≢ 0 (mod p)`.
Two points are **congruent (mod p)** iff `x₁ ≡ x₂` and `y₁ ≡ y₂ (mod p)`.

### 1.2 The general Lemma (p. 337) — the one to formalize first
> **Lemma.** If three points of `H(k,p)` lie on a straight line, two of them are congruent (mod p).

**Proof (faithful).** Let the line be `L : ax + by + c = 0` with `a,b,c ∈ ℤ`, `gcd(a,b)=1`. Every
integer point on `L` satisfies `ax + by + c ≡ 0 (mod p)`, and since `gcd(a,b)=1` at least one of
`a,b` is `≢ 0 (mod p)`. Say `a ≢ 0`. Then on `L ∩ H`, substitute `x ≡ −a⁻¹(by+c)` into `xy ≡ k`:
`−a⁻¹ b y² − a⁻¹ c y − k ≡ 0 (mod p)`, a **quadratic congruence in `y`** ⇒ `y` lies in **≤ 2 residue
classes mod p**. The residue of `y` (with the line) fixes the residue of `x`, hence the **congruence
class** of `(x,y)`. So `L ∩ H` meets **≤ 2 congruence classes**. ∎

This is the clean statement underlying everything; your `Hyperbola.lean` proof (collapse the mod-`p`
determinant via `xy ≡ k` to `−k(a−b)(a−c)(b−c) ≡ 0`) is the *arc-restricted corollary* (one rep per
class ⇒ "≤ 2 classes" = "no 3 collinear"). Keep your determinant proof; **also expose the general
"≤ 2 congruence classes per line" form** — it's what the block argument consumes.

### 1.3 The grid `T'_{2p}` (p. 339)
HJSW shift the origin for convenience: `T'_{2p} = { (x,y) : −½(p−1) ≤ x ≤ p + ½(p−1) }` (a `2p × 2p`
square; `p` odd ⇒ `(p−1)/2 ∈ ℤ`). In words: `x ∈ [−(p−1)/2, (3p−1)/2]` (2p columns), `y ∈ [1, 2p−1]`
(the construction never uses `y = p` or `y ≡ 0`). **For your `IsGridSet (2p)` (which wants
`[0,2p)²`): translate `x ↦ x + (p−1)/2`.** Then `x ∈ [0, 2p−1] ⊂ [0,2p)` and `y ∈ [1,2p−1] ⊂ [0,2p)`.
Translation preserves collinearity, so the whole proof is unaffected — do the math in the HJSW frame,
translate the final `Finset`.

### 1.4 The four quadrant-families (p. 339, exact)
For each integer pair `(r,s)` (cell indices), inside the `p×p` cell `[rp,(r+1)p) × [sp,(s+1)p)`, split
both coordinates at the midpoint into two half-bands of width `(p−1)/2` (the middle line `≡ 0 mod p`
is dropped — it carries no `H`-point). The four quadrants:

```
A_{rs} = {(x,y)∈H : rp        <  x ≤ rp+½(p−1),   sp+½(p+1) ≤ y <  (s+1)p }   -- x LEFT half,  y UPPER half
B_{rs} = {(x,y)∈H : rp+½(p+1) ≤  x <  (r+1)p,     sp+½(p+1) ≤ y <  (s+1)p }   -- x RIGHT half, y UPPER half
C_{rs} = {(x,y)∈H : rp        <  x ≤ rp+½(p−1),   sp        <  y ≤ sp+½(p−1) } -- x LEFT half,  y LOWER half
D_{rs} = {(x,y)∈H : rp+½(p+1) ≤  x <  (r+1)p,     sp        <  y ≤ sp+½(p−1) } -- x RIGHT half, y LOWER half
```

Note the two x-bands `(rp, rp+(p−1)/2]` and `[rp+(p+1)/2, (r+1)p)` are **contiguous** (they meet at
`rp+(p−1)/2` / `rp+(p+1)/2`, consecutive integers) and together cover the `p−1` nonzero residues of
cell `r`; ditto `y`. So **`A₀₀ ∪ B₀₀ ∪ C₀₀ ∪ D₀₀ = [1,p−1]×[1,p−1] = T_p`**, and `|(A∪B∪C∪D)₀₀ ∩ H| =
p − 1` (one `H`-point per nonzero `x`-residue).

**Congruence structure (the key invariant, p. 339):** each family is a union of *complete* congruence
classes — `A = ⋃_{rs} A_{rs}`, `B = ⋃ B_{rs}`, `C = ⋃ C_{rs}`, `D = ⋃ D_{rs}` are exactly the four
congruence-class unions of `H`. No two sets from different families are congruent; **if two `H`-points
are congruent they lie in the same family.** (Because a quadrant-type is determined by `(x mod p, y mod
p)` landing in lower/upper half — congruent points share residues, hence the same half-bands.)

### 1.5 The point set `N_set` (12 blocks = 3 of each type; p. 339)
```
N_set = A₀₁ ∪ A₁₁ ∪ A₁₀                  (3 A-blocks)
      ∪ B₀₁ ∪ B₋₁,₁ ∪ B₋₁,₀             (3 B-blocks)
      ∪ C₀₀ ∪ C₁₀ ∪ C₁₁                  (3 C-blocks)
      ∪ D₀₀ ∪ D₋₁,₀ ∪ D₋₁,₁             (3 D-blocks)
```

**Layout (HJSW Figure I, verified by hand).** Read as a 4×4 grid of `(p−1)/2`-side sub-blocks.
Columns = x half-bands, rows = y half-bands:

```
 col1: r=−1 RIGHT  x∈[−(p−1)/2,−1]   (after +(p−1)/2 shift: [0,(p−3)/2])
 col2: r= 0 LEFT   x∈[1,(p−1)/2]
 col3: r= 0 RIGHT  x∈[(p+1)/2,p−1]
 col4: r= 1 LEFT   x∈[p+1,(3p−1)/2]

 row4 (top): s=1 UPPER  y∈[(3p+1)/2, 2p−1]
 row3:       s=1 LOWER  y∈[p+1, (3p−1)/2]
 row2:       s=0 UPPER  y∈[(p+1)/2, p−1]
 row1 (bot): s=0 LOWER  y∈[1, (p−1)/2]

        col1     col2    col3    col4
 row4 | B₋₁,₁  | A₀₁  | B₀₁  | A₁₁ |
 row3 | D₋₁,₁  |  ·   |  ·   | C₁₁ |
 row2 | B₋₁,₀  |  ·   |  ·   | A₁₀ |
 row1 | D₋₁,₀  | C₀₀  | D₀₀  | C₁₀ |
```

The 12 occupied cells are the **outer ring**; the central 2×2 (`row2–3 × col2–3`, which would be
`A₀₀,B₀₀,C₀₁,D₀₁`) is the **discarded set `M`**. This is the "12 blocks / three of each type" and the
`16 = 12 (T₂) + 4 (M)` you saw in the secondary sources.

### 1.6 The count (p. 339)
All `A_{rs}` are mutually congruent ⇒ equal cardinality, ditto `B,C,D`. Hence
```
|N_set| = 3·|A₀₀| + 3·|B₀₀| + 3·|C₀₀| + 3·|D₀₀|
        = 3·|A₀₀ ∪ B₀₀ ∪ C₀₀ ∪ D₀₀|
        = 3·|T_p ∩ H(k,p)|
        = 3(p − 1).
```
With `N = 2p`: `|N_set| = 3(p−1) = 3(N−2)/2`. **This is where the `3/2` comes from** — 3 copies of a
`(p−1)`-point cell laid in a `2p`-wide grid, not from any "ratio-2 minus collinearities" cancellation.

---

## 2. The cross-block non-collinearity argument (what you most needed)

This is HJSW pp. 339–340, the part that replaces your "stacking gives ratio 2, what caps it?" worry.
There is **no inter-arc intersection count.** It is a slope argument:

**Step 1 — only 4 slopes join congruent points.** Two congruent points `(x,y),(x',y') ∈ N_set` have
`Δx ≡ 0, Δy ≡ 0 (mod p)`. The grid is `2p` wide/tall, so `Δx, Δy ∈ {−p, 0, +p}` (a `±2p` gap won't
fit). Hence the joining line has slope ∈ **`{0, ∞, 1, −1}`** (`0`: Δy=0; `∞`: Δx=0; `1`: Δx=Δy=±p
same sign; `−1`: opposite signs).

**Step 2 — what each slope sees of `H` (p. 340).**
- **slope `0` or `∞`** (horizontal/vertical): meets a **single** congruence class of `H` (a horizontal
  `y=const` forces one `x`-residue `x ≡ k y⁻¹`; ≤ 2 actual points in the `2p` width, both congruent).
  ⇒ no third `N_set`-point.
- **slope `1`**: if it carries two *noncongruent* `H`-classes, their residue reps are `(x,y)` and
  `(−y,−x)` — **reflections in the anti-diagonal `x+y=p`**. Under that reflection `(x,y) ↦ (p−y,p−x)`:
  `A ↦ A`, `D ↦ D`, `B ↦ C` (I verified each quadrant maps as claimed). So the two classes are
  **(both A) or (both D) or (one B + one C)**. (If it meets only one class, the rep is on `x+y=p`,
  i.e. in `A₀₀` or `D₀₀`.)
- **slope `−1`** (the mirror statement): the two classes are **(both B) or (both C) or (one A + one D)**.

**Step 3 — finish (p. 340).** Suppose `N_set` had 3 collinear points. By the Lemma two of them are
congruent, so (Step 1.4 invariant) both lie in one family, say `A`, i.e. among `{A₀₁,A₁₁,A₁₀}`:
- `A₀₁,A₁₁` → differ by `Δx=p,Δy=0` → **slope 0** → single class → no 3rd point. ✓
- `A₁₀,A₁₁` → `Δx=0,Δy=p` → **slope ∞** → no 3rd point. ✓
- `A₀₁,A₁₀` → `Δx=p,Δy=−p` → **slope −1** → by Step 2 the `H`-points on this line lie in `A ∪ D`; the
  only `A`-points of `N_set` on it are the two we started with, and the line **misses every D-block in
  `N_set` (`D₀₀,D₋₁,₀,D₋₁,₁`)**. So no 3rd point. ✓

Symmetric arguments dispatch families `B,C,D`. Hence `N_set` is no-three-in-line. ∎

**The pinwheel is the whole trick.** The specific `(r,s)` choices (`A` at `{01,11,10}`, `B` at
`{01,−1·1,−1·0}`, `C` at `{00,10,11}`, `D` at `{00,−1·0,−1·1}`) are arranged so that the slope-`±1`
line through the two "diagonal" same-family blocks runs *into the empty center `M` / off-grid*, never
through a block of the partner family (`D` for `A`, `C` for `B`, etc.). Formalizing Step 3's last
bullet = checking those 4 slope-`±1` lines miss the 3 partner blocks — a finite, explicit incidence
check, not an asymptotic argument.

---

## 3. The `(3/2 − ε)n` corollary for ALL `n` (p. 340–341)
Per-prime you get `maxNoThreeInLine (2p) ≥ 3(p−1)` with **no PNT needed** (just the construction).
For *every* large `n`: by the **Prime Number Theorem** pick `p` with `(1−ε₁)n < 2p ≤ n`; then
`3(p−1) > (3/2 − ε₂)·2p > (3/2 − ε)n`. **Target the clean per-prime theorem first**; the all-`n`
corollary needs prime density (PNT, or even just a good prime gap), which is heavier — note mathlib
*does* have PNT now, but you can also state the headline only at `N=2p`.

---

## 4. Formalization guidance (concrete, dovetails your current files)

1. **Generalize the lemma.** Add to `Hyperbola.lean` (or a new `HyperbolaLine.lean`) the HJSW general
   Lemma: *any* line meets `H(k,p)` in ≤ 2 congruence classes. Your determinant collapse already
   proves the hard direction; restate it as "two noncongruent collinear `H`-points are impossible for
   a third noncongruent one." Concretely: a line `ax+by+c=0` (primitive) ⇒ quadratic in one residue ⇒
   `Finset.card ≤ 2` of `{y mod p}`. mathlib: `Polynomial.card_roots_le_degree` over `ZMod p` (field),
   or just "a degree-≤2 poly over a field has ≤2 roots."
2. **Define the blocks as `Finset (ℤ × ℤ)`** (work in ℤ with the HJSW offset; translate to ℕ/`[0,2p)`
   at the very end). `A_{rs} … D_{rs}` are `H ∩` an explicit rectangle — `Finset.filter` over the cell.
3. **Congruence-class completeness** (`§1.4`): prove "`(x,y) ∈ A ↔ (x mod p ∈ left, y mod p ∈ upper)`"
   so congruent points share a family. This is the invariant Step 3 leans on.
4. **`N_set`** = the explicit union of the 12 blocks; `card = 3(p−1)` via the 3-congruent-copies
   argument (`card_A01 = card_A11 = card_A10`, each a translate of `A₀₀`).
5. **No-three-in-line** via the slope case split. The only "geometric" content is the 4 slope-`±1`
   incidence checks in Step 3 — finite and explicit; the rest is the Lemma + the congruence invariant.
6. **Grid fit:** final `Finset` translated by `+(p−1)/2` in `x` lands in `[0,2p)²` ⇒ feeds your
   `IsGridSet (2*p)` and `maxNoThreeInLine`. Headline: `3*(p-1) ≤ maxNoThreeInLine (2*p)`.

mathlib facts you'll want: `ZMod p` is a field (have it); `Polynomial` root-count over a field;
`Finset.card_image_of_injective` / translation injectivity (have it); `Int.fract`/midpoint splits are
just `omega`-friendly interval arithmetic.

**Effort read (confidence 70%):** the general Lemma is ~your existing proof re-skinned (low risk). The
real work is the bookkeeping of items 2–4 (defining 12 blocks + the congruence invariant + the count)
and the 4 incidence checks in 5. All elementary, all `ZMod p` + interval `omega` + finite case split —
no new mathlib theory. This is "fiddly but unblocked," exactly as your PLAN predicted.

---

## 5. Sources
- **Hall, Jackson, Sudbery, Wild**, *Some Advances in the No-Three-in-Line Problem*, J. Combin. Theory
  Ser. A **18** (1975) 336–341, DOI `10.1016/0097-3165(75)90043-6`. **(Read in full — primary.)**
- Pór/Wood-lineage restatement of the T₂/M block structure: *The extensible No-Three-In-Line problem*,
  arXiv:2209.01447 (confirms `H(c,p)`, `T₂` = 12 ring blocks, `M` = central 4, `S₂ = H ∩ T₂`,
  `|S₂| = 3(p−1)` in `2p×2p`).
- Headline cross-checks: arXiv:2512.11469 ("Three methods, one problem"); no-(k+1)-in-line papers
  arXiv:2508.07632 / 2510.17743 (HJSW is their `k=2` base case).
