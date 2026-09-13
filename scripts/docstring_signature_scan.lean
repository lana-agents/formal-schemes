/-
Emit one line per declaration of this project that carries a docstring, with the finiteness
notions its own signature mentions.  `scripts/docstring_signature_scan.py` reads the prose and
decides; this file only produces the rows.

Run from the repository root, after a full `lake build`:

    lake env lean scripts/docstring_signature_scan.lean > /tmp/docsig.tsv
    python3 scripts/docstring_signature_scan.py /tmp/docsig.tsv

It takes about 15 seconds once the environment is loaded.

## Why this exists

Every other instrument in `scripts/` reads one half of a declaration.
`scripts/closure_audit.py` and `scripts/citation_audit.py` read prose -- comments, docstrings,
figures, backticked names -- and never look at a type.  `scripts/signature_scan.lean` and
`scripts/symm_duplicate_statement_scan.lean` walk the environment and never look at a docstring.
So a sentence that contradicts the theorem it is attached to is invisible by construction, and
issue 1961 is what that costs: three declaration headlines in
`FormalSchemes.StructureSheafStalkPowerSeriesCofinal` said *finitely generated ideal of
definition* over theorems taking no `Ideal.FG`, each contradicted by its own docstring four lines
below, and all four of the instruments above passed them.  A human found them by reading a
docstring against a signature.  This pair makes that cheap.

## Why the environment and not the sources

A regex over the sources can find the sentence but not the hypothesis.  Measured on this tree:
the source-level version flags three real sites inside the power-series cluster and 64 tree-wide,
of which ten read are ten false positives.  Two of its four failure modes cannot be
fixed at source level at all -- the hypothesis lives in a `variable` command above the
declaration, outside any signature slice, and a definition's finiteness lives in its **body**.
Both are ordinary reads here: the elaborated type already carries what the `variable` command
contributed, and the value is available for the body case.

## The four columns

* **name**   -- the declaration.
* **module** -- the module it was declared in.
* **kind**   -- theorem, definition, inductive or other; the matcher reports them separately
  because a definition is the case whose finiteness usually sits in the value, not in the type.
* **type** / **value** / **ctor** -- every constant occurring in the elaborated type, respectively
  in the value, respectively in the constructor types of an inductive, whose *name* carries a
  finiteness notion.  Comma-separated, deduplicated, possibly empty.  The names are emitted rather
  than a yes/no so the matcher can change the rule without a rebuild; that is the whole reason for
  the split.  The third column is where a **structure field** lives: `AffineFormalSchemeCat` is an
  adic ring whose ideal of definition is finitely generated, and that `Ideal.FG` is a field, so it
  occurs in neither the type (which is `Type _`) nor a value (a structure has none).  Measured: the
  column removes three of the seven flags the first two columns leave.
* **doc**    -- the docstring, with backslash, tab, newline and carriage return escaped, so that
  one docstring is one line.  The matcher un-escapes it and matches the prose there, which is what
  lets it see a phrase that wraps across the 100-column margin.

## Why the matched constants are collected by name and not against a fixed list

Measured on this tree: a fixed list naming `Submodule.FG`, `Module.Finite`, `IsNoetherianRing` and
the obvious companions flags 143 declarations, and almost all of it is one mistake.  `Ideal.FG` is
a constant in its own right in this Mathlib and is **not** notation for `Submodule.FG`, so a fixed
list misses every `(hI : I.FG)` on the tree.  Matching a substring of the constant's name takes
that from 143 to 17.  The remedy for a rule you are unsure of is to print the constants of a type
you know the answer for, which is how that was found.

## Do not rebuild the expression to collect the constants

The collection below is `Lean.Expr.getUsedConstants`, which folds with a visited set.  A plain
recursive walk turns a heavily shared DAG into a tree and does not finish on this library:
`scripts/signature_scan.lean` records a run that took 20 minutes and was killed at 10 GB after
exactly that change (issue 1534).

## What this still cannot see

A probe that does not say what it misses is how a tree accumulates defects, so:

* **One phrase family at a time.**  The matcher ships with finite generation.  *Noetherian*,
  *complete*, *local*, *nontrivial* and *adic* are the same shape and each brings its own
  population; running one is a row's worth of triage.
* **Declaration docstrings only.**  A module docstring is attached to no signature, so a claim
  made in a `## Main results` bullet or in a file header is out of reach here.  Those are where
  issue 1961's *correct* sentences lived, which is exactly why the defect survived.
* **An under-claim and an over-claim are indistinguishable.**  This reports that a sentence names
  a hypothesis its signature does not carry.  Whether the repair is to the sentence or to the
  theorem is a judgement no instrument makes.
* **The notion, never the object.**  This file emits every finiteness-named constant of a
  signature and the matcher asks only whether the set is empty.  A signature carrying finiteness
  about something else satisfies it.  Which *notions* count is the matcher's choice and is
  argued in its header -- the loose reading, in which an `IsNoetherianRing` in scope excuses a
  sentence about an ideal being finitely generated, misses one of issue 1961's three sites.
* **A hypothesis that is present but useless.**  A signature carrying `Ideal.FG` about some other
  object satisfies the rule.  The pairing is *declaration to declaration*, never phrase to binder.
* **Nothing outside `FormalSchemes`.**  Mathlib and core are filtered out.
-/
import FormalSchemes

open Lean Meta Elab

/-- Is `n` an internal / auto-generated name we should ignore?  From
`scripts/symm_duplicate_statement_scan.lean`, verbatim. -/
def isNoise (n : Name) : Bool :=
  n.isInternal ||
  (n.components.any fun c =>
    let s := c.toString
    s.startsWith "_" || s == "proof" || s == "eq_def" || s == "eq_1" ||
    s == "casesOn" || s == "recOn" || s == "below" || s == "brecOn" ||
    s == "noConfusion" || s == "noConfusionType" || s == "sizeOf_spec" ||
    s == "injEq" || s == "ndrec" || s == "rec" || s == "ofNat" || s == "match_1")

/-- Was `n` declared by this project, rather than by Mathlib or core?  From
`scripts/symm_duplicate_statement_scan.lean`, verbatim. -/
def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => (`FormalSchemes).isPrefixOf m || m == `FormalSchemes
  | none => false

/-- The module `n` was declared in, for the report.  From
`scripts/symm_duplicate_statement_scan.lean`, verbatim. -/
def modOf (env : Environment) (n : Name) : Name :=
  (env.getModuleFor? n).getD Name.anonymous

/-- Substring test. -/
def has (needle hay : String) : Bool := (hay.splitOn needle).length > 1

/-- Does this constant's *name* carry a finiteness notion?  Deliberately a substring test and not
a fixed list: see the note on 143 versus 17 at the top of this file. -/
def finiteish (n : Name) : Bool :=
  let s := n.toString
  has "FG" s || has "Finite" s || has "Noether" s || has "Finset" s || has "Finsupp" s

/-- Drop repeats, keeping the first occurrence. -/
def dedup (ns : Array Name) : Array Name :=
  ns.foldl (fun (acc : Array Name) n => if acc.contains n then acc else acc.push n) #[]

/-- The finiteness-carrying constants of an expression, deduplicated. -/
def finiteConsts (e : Expr) : Array Name :=
  dedup (e.getUsedConstants.filter finiteish)

/-- Escape a docstring so that it occupies exactly one line of the output. -/
def esc (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else if c == '\t' then acc ++ "\\t"
    else if c == '\r' then acc ++ "\\r"
    else acc.push c) ""

/-- The declaration's kind, as one word, for the matcher's report. -/
def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .inductInfo _ => "induct"
  | _ => "other"

run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let out ← IO.getStdout
  out.putStrLn "name\tmodule\tkind\ttype\tvalue\tctor\tdoc"
  for (n, ci) in env.constants.toList do
    if isNoise n then continue
    if !isProject env n then continue
    match ← findDocString? env n with
    | none => pure ()
    | some doc =>
      let tc := ",".intercalate ((finiteConsts ci.type).toList.map toString)
      let vc := match ci.value? with
        | some v => ",".intercalate ((finiteConsts v).toList.map toString)
        | none => ""
      let cc := match ci with
        | .inductInfo iv =>
          let ns : Array Name := iv.ctors.foldl (fun acc c =>
            match env.find? c with
            | some cci => acc ++ finiteConsts cci.type
            | none => acc) #[]
          ",".intercalate ((dedup ns).toList.map toString)
        | _ => ""
      out.putStrLn s!"{n}\t{modOf env n}\t{kindOf ci}\t{tc}\t{vc}\t{cc}\t{esc doc}"
