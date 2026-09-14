#!/usr/bin/env python3
"""Flag a declaration whose docstring names a hypothesis its own signature does not carry.

Every other instrument in `scripts/` reads one half of a declaration.  `closure_audit.py` and
`citation_audit.py` read prose and never look at a type; `signature_scan.lean` and
`symm_duplicate_statement_scan.lean` walk the environment and never look at a docstring.  A
sentence that contradicts the theorem it is attached to therefore sits in the gap between them,
and issue 1961 measured what that costs: three declaration headlines in
`FormalSchemes.StructureSheafStalkPowerSeriesCofinal` said *finitely generated ideal of
definition* over theorems taking no `Ideal.FG`, each contradicted by its own docstring four lines
below, and every instrument on the tree passed them.  `scripts/docstring_signature_scan.lean`
emits the rows; this file reads the prose, applies the rule and reports.

Usage, from the repository root, after a full `lake build`:

    lake env lean scripts/docstring_signature_scan.lean > /tmp/docsig.tsv
    python3 scripts/docstring_signature_scan.py /tmp/docsig.tsv
    python3 scripts/docstring_signature_scan.py /tmp/docsig.tsv --rules

`--selftest` checks the matcher against the shapes it exists to get right and needs no build and
no extractor output.

## The rule, and the three refinements it is made of

A declaration is **flagged** when its docstring claims a finiteness property in prose and no
finiteness notion the rule accepts occurs anywhere in its signature.  Each half of that is a
choice, and each was measured on this tree rather than assumed.  `--rules` re-runs the table on
whatever extractor output it is given; **re-measure it and do not quote the figures below**, which
are one run at one revision -- `ebeb9ed`, this file's base, unless another is named beside the
number.  A pull request that adds a module moves every count here, so a figure written down
without its revision goes quietly false, which is the defect this whole scan exists to catch.

* **Which constants count as a finiteness notion.**  A fixed list of the obvious names flags 134.
  Almost all of that is one mistake: `Ideal.FG` is a constant in its own right in this Mathlib and
  is *not* notation for `Submodule.FG`, so a fixed list misses every hypothesis spelled `I.FG`,
  and nobody writing the list from memory puts it there.  Matching a substring of the constant's
  *name* takes 134 to 17.  The way to debug a rule of this kind is to print the constants of a
  type whose answer you know, not to add names to a list.
* **Where in the declaration to look.**  The type alone leaves 17.  Adding the **value** removes
  ten: a definition's finiteness usually lives in its body, not its statement.  Adding an
  inductive's **constructor** types removes three more, because a structure's finiteness is a
  *field* -- `AffineFormalSchemeCat` is an adic ring with a finitely generated ideal of
  definition, and that `Ideal.FG` occurs in neither its type (which is `Type _`) nor a value (a
  structure has none).  That is 17, then 7, then 4.
* **Where in the docstring to look.**  Inline code spans and fenced blocks are stripped before the
  phrase is matched, so a phrase quoted as code is not read as a claim.  Measured on this tree the
  stripping changes nothing -- 170 either way -- which is worth knowing rather than guessing at.
  It is kept because a claim and a quotation are different things, and the selftest pins it.

## Why the default is the tight rule

Two rules survive that table.  The **loose** one asks *does the signature mention any finiteness
notion at all*; the **tight** one counts only the FG family, so a stray `IsNoetherianRing` does not
excuse a sentence about an ideal being finitely generated.  Loose flags 4 here and tight flags 6.

The tight rule is the default, for a reason that is about this tree and not about taste.  **On a
Noetherian ring a signature's `IsNoetherianRing` is evidence that an FG hypothesis is absent, not
that it is present** -- it is the thing that lets a theorem drop the hypothesis.  Issue 1961 is
exactly that: `FormalSpectrum.fg_powerSeriesIdeal_of_isNoetherianRing` discharges finite
generation inside each of three proofs, from the base ring's Noetherianness, which is why the
three statements carry no `Ideal.FG` and why the three headlines claiming one were wrong.  A rule
that reads `IsNoetherianRing` as *finiteness is handled here* excuses the one case it exists for.

Measured at `f457fab`, before `#680` repaired them -- the only population on this tree where the
answer is known independently:

| rule | flags | of issue 1961's three sites |
|---|---|---|
| loose | 6 | **2** -- the third is excused by an `IsNoetherianRing` |
| tight | 9 | **3** |

The `IsNoetherianRing` that excuses the third site is not even in its statement: a `variable`
command put it in scope, which is the shape no source-level probe can see at all.

Both rows reproduce at `ebeb9ed` with that one file restored to its `f457fab` text and its module
rebuilt: loose 6 and 2 of 3, tight 9 and 3 of 3, and `--rules` reads `136 / 19 / 9 / 6 / 9` over
173 claiming docstrings.  That is the check worth having, because it separates the instrument
from the revision -- the counts move with the tree, and the three sites are found either way.

Same precision, one third more recall: 2 of 6 against 3 of 9.  The two extra flags tight leaves at
this base are `FormalSpectrum.isNoetherianRing_awayCompletion` and `IsAdic.isAdic_radical`, both
sentences describing a step inside a proof.  Two extra reads, tree-wide, against a third of the
defects the instrument exists to find.  `--rule loose` is one flag away if a later population
inverts that.

## What this still cannot see

A probe that does not say what it misses is how a tree accumulates defects, so:

* **One phrase family at a time**, and the one that ships is finite generation.  *Noetherian*,
  *complete*, *local*, *nontrivial* and *adic* are the same shape; each brings its own population
  to triage and is its own row.
* **Declaration docstrings only.**  A module docstring is attached to no signature.  Issue 1961's
  *correct* sentences lived in one, which is exactly why the contradiction survived.
* **An under-claim and an over-claim are indistinguishable.**  This reports that a sentence names
  a hypothesis its signature does not carry.  Which of the two to repair is a judgement.
* **The notion, never the object.**  A signature carrying finiteness about something else
  satisfies the rule; the pairing is declaration to declaration, never phrase to binder.  `--rule
  tight` narrows *which notion* counts and nothing else -- it does not check what the notion is
  about.
* **A sentence about a proof step, or about another declaration's hypothesis, reads exactly like
  a claim about this signature.**  Every flag this scan leaves on the tree today is one of those,
  so the class is not rare -- it is the entire residual.  The disposition of all six is tabled on
  issue 1965.
* **A docstring that correctly reports an absence is flagged too.**
  `FormalSpectrum.atPrimeCofinalRingEquiv` says in as many words that it carries *no finiteness
  hypothesis at all*, which is true, and the phrase is in the sentence, so it is flagged.  The
  matcher reads a phrase, never a polarity.
* **Nothing outside `FormalSchemes`.**  The extractor filters Mathlib and core out.
"""

from __future__ import annotations

import argparse
import re
import sys

COLUMNS = ["name", "module", "kind", "type", "value", "ctor", "doc"]

# The phrase families.  One ships; the others are here to say what the shape of a second one is,
# and running one is a row of its own -- each brings its own population to triage.
FAMILIES = {
    "fg": re.compile(r"finitely[\s-]+generated", re.I),
}

# A fixed list of the obvious finiteness names, kept only so that `--rules` can show what it
# costs.  It is what this scan would have used had the rule not been measured, and the reason it
# is wrong is that `Ideal.FG` is missing from it and cannot be guessed onto it.
FIXED = {
    "Submodule.FG", "Module.Finite", "IsNoetherianRing", "IsNoetherian",
    "Finite", "Set.Finite", "Finset", "Finsupp", "FiniteDimensional",
}

# The FG family alone, for `--rule tight`: a stray Noetherian instance does not excuse a sentence
# about an ideal being finitely generated.
TIGHT = re.compile(r"FG|Finset|Finsupp|Finite")

FENCE = re.compile(r"```.*?```", re.S)
SPAN = re.compile(r"`+[^`]*`+")

RULES = ["fixed", "type", "type+value", "loose", "tight"]
DEFAULT_RULE = "tight"


def unescape(field: str) -> str:
    """Invert the extractor's escaping.  One docstring is one line there and many lines here."""
    out: list[str] = []
    i = 0
    while i < len(field):
        c = field[i]
        if c == "\\" and i + 1 < len(field):
            nxt = field[i + 1]
            out.append({"n": "\n", "t": "\t", "r": "\r", "\\": "\\"}.get(nxt, nxt))
            i += 2
            continue
        out.append(c)
        i += 1
    return "".join(out)


def prose(doc: str) -> str:
    """The docstring with code removed, so a phrase quoted as code is not read as a claim."""
    return SPAN.sub(" ", FENCE.sub(" ", doc))


def claims(doc: str, family: re.Pattern) -> bool:
    """Does this docstring claim the family's property, in prose?

    The match runs over the *unwrapped* docstring, with the separator a run of whitespace or
    hyphens.  That is
    not a detail: issue 1961's lead site wraps at the 100-column margin as `finitely` /
    `generated`, and a line-bound `git grep` for the phrase misses it -- which is how the row's
    own prescribed probe found two of its three sites.
    """
    return bool(family.search(prose(doc)))


def evidence(row: dict[str, str], rule: str) -> list[str]:
    """The finiteness notions this rule is willing to count, for one declaration."""
    def consts(col: str) -> list[str]:
        return [c for c in row[col].split(",") if c]

    if rule == "fixed":
        return [c for c in consts("type") + consts("value") + consts("ctor") if c in FIXED]
    if rule == "type":
        return consts("type")
    if rule == "type+value":
        return consts("type") + consts("value")
    if rule == "loose":
        return consts("type") + consts("value") + consts("ctor")
    if rule == "tight":
        found = consts("type") + consts("value") + consts("ctor")
        return [c for c in found if TIGHT.search(c)]
    raise SystemExit(f"unknown rule {rule!r}; expected one of {', '.join(RULES)}")


def read_rows(path: str) -> list[dict[str, str]]:
    rows = []
    with open(path, encoding="utf-8") as handle:
        header = handle.readline().rstrip("\n").split("\t")
        if header != COLUMNS:
            raise SystemExit(
                f"{path}: header is {header}, expected {COLUMNS} -- "
                "re-run scripts/docstring_signature_scan.lean"
            )
        for lineno, line in enumerate(handle, start=2):
            parts = line.rstrip("\n").split("\t")
            if len(parts) != len(COLUMNS):
                raise SystemExit(f"{path}:{lineno}: {len(parts)} columns, expected {len(COLUMNS)}")
            rows.append(dict(zip(COLUMNS, parts)))
    return rows


def scan(rows, family: re.Pattern, rule: str):
    claiming, flagged = [], []
    for row in rows:
        doc = unescape(row["doc"])
        if not claims(doc, family):
            continue
        claiming.append(row)
        if not evidence(row, rule):
            flagged.append(row)
    return claiming, flagged


def report(rows, family: re.Pattern, rule: str) -> int:
    claiming, flagged = scan(rows, family, rule)
    print(f"declarations with a docstring     : {len(rows):6d}")
    print(f"  docstring claims the property   : {len(claiming):6d}   (rule: {rule})")
    print(f"  FLAGGED: no finiteness in sight : {len(flagged):6d}")
    for row in sorted(flagged, key=lambda r: (r["module"], r["name"])):
        print(f"    {row['name']}   ({row['module']}, {row['kind']})")
    if flagged:
        print()
        print("A flag is a question, not a finding: repair the sentence, repair the theorem, or")
        print("decline it by name with a reason.  A flag left unmentioned is a defect.")
    return 0


def rules_table(rows, family: re.Pattern) -> int:
    print("rule          flags   what it adds")
    blurb = {
        "fixed": "a fixed list of finiteness names",
        "type": "any finiteness-named constant, elaborated type only",
        "type+value": "  ... plus the value, for a def whose finiteness is in its body",
        "loose": "  ... plus constructor types, for a structure field",
        "tight": "  ... counting the FG family only  <-- the default",
    }
    for rule in RULES:
        _, flagged = scan(rows, family, rule)
        print(f"{rule:<12} {len(flagged):6d}   {blurb[rule]}")
    with_code, without_code = 0, 0
    for row in rows:
        doc = unescape(row["doc"])
        if family.search(doc):
            with_code += 1
        if claims(doc, family):
            without_code += 1
    print()
    print(f"docstrings matching anywhere      : {with_code:6d}")
    print(f"  ... with code spans stripped    : {without_code:6d}")
    return 0


def selftest() -> int:
    """Pin the shapes this matcher exists to get right.  Needs no build and no extractor run."""
    ok, fail = 0, 0

    def check(label: str, got, want) -> None:
        nonlocal ok, fail
        if got == want:
            ok += 1
            print(f"ok    {label}")
        else:
            fail += 1
            print(f"FAIL  {label}: got {got!r}, wanted {want!r}")

    fg = FAMILIES["fg"]

    # The failure that hid issue 1961's lead site from `git grep`: docstrings wrap at the
    # 100-column margin and the phrase lands with the break inside it.  A line-bound probe
    # misses it; `\s+` over the unwrapped text does not.
    wrapped = "IsStalkLimit is false at every point, for every finitely\ngenerated ideal."
    check("a phrase wrapped across a line break is still a claim", claims(wrapped, fg), True)
    check("a line-bound probe would have missed it",
          any(fg.search(line) for line in wrapped.split("\n")), False)

    # A phrase quoted as code is a quotation, not a claim about this signature.
    check("an inline code span is not prose",
          claims("see `finitely generated` in Mathlib", fg), False)
    check("a fenced block is not prose",
          claims("example:\n```\nfinitely generated\n```\n", fg), False)
    check("prose beside a code span is still prose",
          claims("`Ideal.FG` says the ideal is finitely generated", fg), True)

    # The escaping round-trip, which is what makes one docstring one line.
    check("escapes round-trip", unescape("a\\nb\\tc\\\\d"), "a\nb\tc\\d")
    check("a wrapped phrase survives the round-trip",
          claims(unescape("every finitely\\ngenerated ideal"), fg), True)

    def row(**kw):
        base = dict.fromkeys(COLUMNS, "")
        base.update(kw)
        return base

    # A true positive: issue 1961's lead site as it stood at `f457fab`.  No finiteness notion
    # anywhere in the declaration, and a headline that names one.
    true_positive = row(
        name="FormalSpectrum.not_isStalkLimit_powerSeriesXCofinal_int",
        module="FormalSchemes.StructureSheafStalkPowerSeriesCofinal", kind="thm",
        doc="false at every point, for every finitely\\ngenerated ideal of definition.")
    check("a headline naming a hypothesis its signature lacks is flagged",
          [r["name"] for r in scan([true_positive], fg, "loose")[1]], [true_positive["name"]])

    # A hypothesis contributed by a `variable` command above the declaration.  No source-level
    # probe can see it; the elaborated type carries it, so the type column does.
    from_variable = row(name="X", module="M", kind="thm", type="IsNoetherianRing",
                        doc="every ideal is finitely generated here")
    check("a hypothesis from a variable command is in the elaborated type",
          scan([from_variable], fg, "loose")[1], [])
    check("... and the tight rule declines to accept it",
          [r["name"] for r in scan([from_variable], fg, "tight")[1]], ["X"])

    # A definition whose finiteness lives in its body rather than its statement.
    in_body = row(name="Y", module="M", kind="def", value="Ideal.FG",
                  doc="the finitely generated ideal this produces")
    check("a def's finiteness in its body is counted", scan([in_body], fg, "loose")[1], [])
    check("... and the type-only rule would have flagged it",
          [r["name"] for r in scan([in_body], fg, "type")[1]], ["Y"])

    # A structure whose finiteness is a field: neither a type nor a value carries it.
    in_field = row(name="AffineFormalSchemeCat", module="M", kind="induct", ctor="Ideal.FG",
                   doc="an adic ring with a finitely generated ideal of definition")
    check("a structure field is counted", scan([in_field], fg, "loose")[1], [])
    check("... and type+value would have flagged it",
          [r["name"] for r in scan([in_field], fg, "type+value")[1]],
          ["AffineFormalSchemeCat"])

    # The mistake that made a fixed list flag 134: `Ideal.FG` is its own constant here and is not
    # notation for `Submodule.FG`, so no fixed list anyone would write contains it.
    check("Ideal.FG is not on any fixed list", "Ideal.FG" in FIXED, False)
    ideal_fg = row(name="Z", module="M", kind="thm", type="Ideal.FG",
                   doc="for J a finitely generated ideal")
    check("the substring rule accepts Ideal.FG", scan([ideal_fg], fg, "loose")[1], [])
    check("the fixed list does not",
          [r["name"] for r in scan([ideal_fg], fg, "fixed")[1]], ["Z"])

    # A docstring that says nothing about the family is not a claim, however it is spelled.
    quiet = row(name="W", module="M", kind="thm", doc="finite type, finitely many primes")
    check("a neighbouring finiteness word is not this family",
          scan([quiet], fg, "loose")[1], [])
    check("the hyphenated spelling is the same claim",
          claims("a finitely-generated ideal", fg), True)
    check("a hyphen across a line break too",
          claims("a finitely-\ngenerated ideal", fg), True)

    print(f"\n{ok} ok / {fail} FAIL")
    return 1 if fail else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("tsv", nargs="?", help="output of scripts/docstring_signature_scan.lean")
    parser.add_argument("--rule", default=DEFAULT_RULE, choices=RULES)
    parser.add_argument("--family", default="fg", choices=sorted(FAMILIES))
    parser.add_argument("--rules", action="store_true", help="re-run the refinement table")
    parser.add_argument("--selftest", action="store_true", help="needs no build")
    args = parser.parse_args()

    if args.selftest:
        return selftest()
    if not args.tsv:
        parser.error("a TSV is required unless --selftest is given")
    rows = read_rows(args.tsv)
    family = FAMILIES[args.family]
    if args.rules:
        return rules_table(rows, family)
    return report(rows, family, args.rule)


if __name__ == "__main__":
    sys.exit(main())
