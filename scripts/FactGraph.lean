/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
Fact graph extractor.  For every theorem under the listed namespaces, split its statement into
hypotheses (binder types) and conclusion, and print one TSV row per theorem:
  kind<TAB>theorem<TAB>hyps (comma-separated Literature Props)<TAB>conclusion Literature Props
kind is `edge` (conclusion is a Literature Prop), `refute` (conclusion is ¬ of one),
`uses` (hypotheses only), or `plain` (no Literature Props at all).
Driven by `scripts/fact-graph`, which renders FACT-GRAPH.md.
-/
import LeanFormalizations
open Lean Meta

def litPrefix : Name := `LeanFormalizations.Literature

/-- A named hypothesis: any `LeanFormalizations.*` definition of type `Prop` (Literature Props
and local ones such as `ExponentialsKnown.BakerTwoLogs`). -/
def isLitProp (env : Environment) (n : Name) : Bool :=
  n == `RiemannHypothesis ||
  (`LeanFormalizations : Name).isPrefixOf n && match env.find? n with
    | some (.defnInfo d) => d.type == .sort 0
    | _ => false

def short (n : Name) : String :=
  (if litPrefix.isPrefixOf n then n.replacePrefix litPrefix .anonymous
   else n.replacePrefix (`LeanFormalizations : Name) .anonymous).toString

#eval show MetaM Unit from do
  let env ← getEnv
  let roots : List Name := [`LeanFormalizations.Schanuel, `LeanFormalizations.Exponentials,
    `LeanFormalizations.ExponentialsKnown, `LeanFormalizations.Waldschmidt2023,
    `LeanFormalizations.StructuralRank, `LeanFormalizations.Bedrock,
    `LeanFormalizations.Champernowne, `LeanFormalizations.Mills, `LeanFormalizations.Diophantine,
    `LeanFormalizations.Maze]
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    unless roots.any (·.isPrefixOf n) do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    let row ← forallTelescope ci.type fun xs body => do
      let mut hyps : Array Name := #[]
      for x in xs do
        let t ← inferType x
        for c in t.getUsedConstants do
          if isLitProp env c && !hyps.contains c then hyps := hyps.push c
      let (kind, concl) := match body.getAppFn.constName?, body with
        | _, .app (.const ``Not _) (.const c _) =>
            if isLitProp env c then ("refute", #[c]) else ("x", #[])
        | some c, _ => if isLitProp env c && body.getAppNumArgs == 0 then ("edge", #[c]) else ("x", #[])
        | none, _ => ("x", #[])
      let kind := if kind != "x" then kind else if hyps.isEmpty then "plain" else "uses"
      return s!"{kind}\t{n}\t{",".intercalate (hyps.map short).toList}\t{",".intercalate (concl.map short).toList}"
    rows := rows.push row
  for r in rows.qsort (· < ·) do IO.println r
