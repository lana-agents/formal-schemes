/-
Emit one line per declaration of this project, keyed by the *shape of its statement*.

Run from the repository root, after a full `lake build`:

    lake env lean scripts/signature_scan.lean > /tmp/signatures.tsv
    python3 scripts/signature_scan.py /tmp/signatures.tsv

`scripts/signature_scan.py` documents what the keys are for and how to read the buckets; this file
only produces them.  It takes about 15 seconds once the environment is loaded.

Four columns, and the difference between the last two is the whole point:

* **typeHash**  — hash of the whole type.  Exact, and blind to the binder *list*: two spellings of
  one map differ here as soon as one of them takes an instance argument the other does not.
* **conclHash** — hash of the conclusion, reached by peeling `∀` binders off the raw expression.
  Loose de Bruijn indices survive, so this too is relative to the binder list.
* **concl**     — the conclusion *pretty-printed* inside `Lean.Meta.forallTelescope`, so the
  binders appear under the names the author gave them.  This is the key that finds a map written
  twice:
  `FormalSpectrum.sectionsMk` and `FormalSpectrum.sectionsOpenHom` are the same
  `R →+* Γ (U, O_{Spf R})` and agree on it, while differing on both hashes above.  It trades on
  this tree naming its section variables consistently, and it hides the binders' *types*, so two
  fields of unrelated structures collide as `Ideal self.K`.  More recall, more to read.
* **foldable**  — 1 when the conclusion's head is a `def` of this project, so `whnf` would change
  it.
  That is the folded/unfolded class: `LocallyRingedSpace.hasAffineChartAt_of_formalScheme` states
  `HasAffineChartAt X x` where `FormalScheme.exists_openImmersion` states it unfolded.  A marker,
  not a normalisation — unfolding them all belongs in a successor.

**Do not "canonicalise" by rebuilding the `Lean.Expr`.** Erasing binder names with a plain recursive
rewrite turns a heavily shared DAG into a tree and does not finish on this library: the scan that
runs in 15 seconds here ran 20 minutes and was killed at 10 GB with that one change (issue 1534).
-/
import FormalSchemes
open Lean Meta Elab Command

set_option maxHeartbeats 0

/-- The conclusion, reached by peeling `∀` binders off the raw expression. -/
partial def peelForalls : Expr → Expr
  | .forallE _ _ b _ => peelForalls b
  | .mdata _ e       => peelForalls e
  | e                => e

/-- Is `n` a `def` declared in a module of this project — something `whnf` would unfold? -/
def isProjectDef (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => m.getRoot == `FormalSchemes && (env.find? n matches some (.defnInfo _))
  | none   => false

run_cmd liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let out ← IO.getStdout
  let mut n := 0
  for i in [0:mods.size] do
    let m := mods[i]!
    if m.getRoot == `FormalSchemes then
      for c in env.header.moduleData[i]!.constNames do
        if c.isInternalDetail then continue
        let some ci := env.find? c | continue
        match ci with
        | .thmInfo _ | .defnInfo _ | .axiomInfo _ | .opaqueInfo _ =>
          let raw := peelForalls ci.type
          let foldable := if isProjectDef env raw.getAppFn.constName then "1" else "0"
          let kind := if ci matches .thmInfo _ then "thm" else "def"
          -- `Lean.Meta.forallTelescope` can fail on a type this environment cannot instantiate;
          -- a `?` is a key that collides with nothing, the right failure for a *reporting* pass.
          let pp ← try
              forallTelescope ci.type fun _ concl => do pure (toString (← ppExpr concl))
            catch _ => pure "?"
          let pp := (pp.replace "\n" " ").replace "\t" " "
          out.putStrLn
            s!"DECL\t{c}\t{m}\t{kind}\t{ci.type.hash}\t{raw.hash}\t{foldable}\t{pp}"
          n := n + 1
        | _ => continue
  out.putStrLn s!"TOTAL\t{n}"
