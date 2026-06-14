# .githooks

`pre-commit` runs `lake build` when staged changes touch `*.lean` / lakefile /
toolchain / manifest — the "green before commit" gate.

## Enable (per clone — `core.hooksPath` is local config, not tracked)
```sh
git config core.hooksPath .githooks
```
Do this **after** the first successful `lake exe cache get && lake build`, so the
very first commit isn't blocked waiting on a cold mathlib build.

## Why bash-in-repo, not the Python `pre-commit` framework
Works offline (the lean-yolo-box has no pip/network); the gate is just "run one
local command"; and it doesn't fight a global `core.hooksPath`.

## Non-vacuous gate
`lakefile.toml` sets `defaultTargets = ["LeanFormalizations"]`, so bare
`lake build` actually builds the library (a bare `lake build` with no default
target builds nothing — a silently vacuous gate). If you add a `lean_lib`, add it
to `defaultTargets` too.
