/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Comparator harness root

Doc-only root module for the `Comparator` lean_lib (its `globs = ["Comparator.+"]` matches the
root module too, so this file must exist). The content lives in `Comparator/<Result>/`:

- `Challenge.lean` - imports **only Mathlib**, states the headline theorems with `sorry`.
  This is the human audit surface.
- `Solution.lean` - imports the real development and declares nothing.
- `config.json` - what `leanprover/comparator` checks: the theorem names, the permitted-axiom
  whitelist, and `enable_nanoda: true` for the independent second kernel.

CI runs comparator over every `Comparator/*/config.json` (`.github/workflows/comparator.yml`);
`scripts/comparator-probe` is the macOS-friendly local pre-flight of the statement-identity check.
-/
