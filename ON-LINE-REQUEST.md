# ON-LINE-REQUEST — lean-formalizations-ntl

## 2026-06-20 — propagate two v4.31 gotchas to the shared bump cookbook (sandbox can't write outside repo)

The de-vendor + v4.31 bump of this repo (`a0f17d1`) surfaced two durable gotchas. I (YOLO/sandboxed
session) can only write inside this repo, so the canonical docs at
`~/src/lean-universe/MIGRATE-v4.29.1-to-v4.31.0.md` and `~/src/mathlib-bump-cookbook/` are read-only to me.
**Please fold these in** (then delete this item):

1. **Mark `lean-formalizations-ntl` DONE** in MIGRATE §2 (replace the "🟡 mid-bump, UNCOMMITTED" entry):
   DONE `a0f17d1`, branch `ntl-hjsw`. NOT bare-mathlib — **de-vendored** the hand-ported PNTAnd tower into a
   real lake dep on `kim-em/PrimeNumberTheoremAnd @ bump/v4.31.0`. Deleted 8 vendored files
   (Asymptotics/Support/Sobolev/SmoothExistence/Fourier/Defs/Wiener/Consequences); two consumers now
   `import PrimeNumberTheoremAnd.Consequences` (`WeakPNT''`, `pi_alt'`). Baseline lost → gated erdos-1050 way:
   13 headlines `#print axioms`-clean NOW incl. `weakPNT`/`prime_number_theorem` through the EXTERNAL dep
   (clean `#print axioms` is authoritative even though the dep's `Wiener.lean:323/342` hold 2 dead-code
   `prelim_decay` sorries off the WeakPNT path). 3 own-file proof-body fixes: Mertens `using!` + `convert …
   <;> first | rfl | (field_simp <;> ring)`; MertensConstant `Function.comp_def`; PrimeGap
   `factorization_eq_zero_of_non_prime`→`…_not_prime`. Full build green (8620 jobs).

2. **NEW cookbook gotcha — macOS-side FD exhaustion on first-from-source v4.31 full builds (orbstack):**
   v4.31 splits each olean into 3 files (`.olean` + `.olean.private` + `.olean.server`), tripling open-file
   pressure. When ~10–16 heavy leaf files COMPILE FROM SOURCE in parallel in the final build wave, each
   opening its full mathlib import closure on the **bind-mounted** `/Users/...` path, the combined FD count
   exhausts the **macOS host** file-sharing daemon. The Linux VM's `ulimit -n` is 1048576 and
   `fs.file-max` ~9e18 — NOT the limit; the cap is macOS `kern.maxfiles`, unreachable from the sandbox.
   Symptom: `failed to open file '…olean.private': Too many open files` on a ROTATING set of leaf files
   (jobs ~8590–8620). **Spurious** — each file builds fine alone. This toolchain's `lake` has **no `-j`/
   `--jobs` flag** (`lake -j`, `lake build --jobs=` both rejected), so reduce parallelism by building each
   module SEQUENTIALLY once to cache it:
   `find src -name '*.lean' | sed 's#^src/##; s#\.lean$##; s#/#.#g' | while read m; do lake build "$m"; done`
   then the full `lake build` is an all-cached **replay** (replays don't open the closure → no spike).
   Re-running the plain build a few times also converges. Hits any v4.31 repo with many heavy leaves on this box.
