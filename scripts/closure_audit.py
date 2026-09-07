#!/usr/bin/env python3
"""Check that every import-closure figure quoted in this tree's comments is the figure the
imports actually give.

A module docstring that says *"reverse closure **2**"* is making a measurement, and `lake build`
cannot check it: the sentence compiles whatever the number is.  Worse, a **reverse**-closure
figure is invalidated by a leaf added anywhere above the module, in a pull request that touches
neither the file carrying the sentence nor any file it imports -- so it goes wrong with nothing in
the diff, nothing in the signature scan and nothing in `scripts/citation_audit.py` able to see it.
Every name in the sentence resolves; only the number is wrong.

Forward closures rot too, more slowly, and the tree has an instance of that as well: a module's
forward closure grows when a module it *already* imports gains an import, which is likewise not in
its own diff.  `FormalSchemes/TateInvNodeChartDescentIso.lean` said **250** where the walk gives
**253** without that file's own imports ever changing.  So "quote forward closures, they do not
rot" is not a fix; measuring is.

Usage, from the repository root -- no build needed, this reads `import` lines:

    python3 scripts/closure_audit.py --tree
    python3 scripts/closure_audit.py --selftest

There is deliberately **no `--diff` mode**.  A closure figure is falsified by an edit somewhere
else in the tree, so the population that matters is every claim in every file, not the claims in
the hunks; a diff-restricted run would be blind to the only way these figures ever go wrong.  That
is the same argument `citation_audit.py`'s `markdown_line_pointers` makes for reading whole
documents.

## The conventions, which are the tree's own

Stated the same way in a dozen `## Placement` paragraphs, and this script implements exactly them:

* the walk is over the files under `FormalSchemes/`, and the aggregator `FormalSchemes.lean` at the
  repository root is **outside** it;
* a module is **not** counted in its own closure -- the tree writes that as *"N project modules
  besides itself"*, and writes the other convention explicitly as *"(N counted with itself)"* or
  *"N with itself"*, which this script also checks, at N plus one;
* both `import FormalSchemes.Foo` and `public import FormalSchemes.Foo` are import lines.  A walker
  matching only `^import ` under-reports silently, which is the failure mode that looks plausible.

## Which module a claim is about

The only interesting question here.  A claim in file `A` is usually about `A` itself, but a
`## Placement` paragraph also quotes the closures of the modules it is *choosing between*, so
"the file it appears in" is wrong about a third of the tree's claims and "the module named nearby"
is wrong about the rest.  The rule implemented below is read off the prose that exists:

1. the text before the figure is scanned back to the start of the sentence-or-so (320 characters),
   with any `## Placement` opener -- *"A leaf over `X` and `Y`: forward closure N"* -- masked as a
   single **self** anchor, since the modules it names are the ones being imported and not the
   subject of the figure;
2. the **last** anchor before the figure decides.  A self anchor (*this leaf*, *this file*, *this
   module*, or a masked opener) means the file itself; a backticked `FormalSchemes.Foo` or
   `FormalSchemes/Foo.lean` means that module; an anaphor (*that file*, *its module*, *whose*)
   means the nearest module token before the anaphor;
3. and a claim is **declined** -- reported, not guessed at -- when it is plural (*"forward closures
   42 and 6"* is two claims about two modules), when the anaphor has no module token to resolve
   against (*"its module has reverse closure 9"*, where *its* is a declaration's), or when an
   indefinite leaf intervenes (*"a leaf whose own forward closure is 231"* is about a module that
   does not exist).

## The noun beside the figure

*"A leaf over `X` and `Y`: forward closure 39, reverse closure 7"* states its own contradiction:
`leaf` is the claim that the reverse closure is **0**, and it rots exactly like the numeral beside
it -- six openers on this tree said it of a file with consumers.  So a sentence that carries a
closure figure **and** calls the file it is in a leaf, either as a `## Placement` opener or as
*this leaf*, has that noun checked against the same walk, once per sentence however many figures
it quotes.  This buys coverage for nothing: only sentences that already carry a claim are read, so
no claim that was checked before is declined now, and the word's other senses stay out of range --
a `Mathlib-only leaf` is a *forward*-closure claim, *"a leaf whose own forward closure is 231"* is
hypothetical, and the 66 proof-tree leaves in the `GeneralFibreProductBothAlgebraData*` modules
carry no figure at all.  What is out of reach is the positional noun about **another** module,
*"`FormalSchemes.TateSeparated`, a Tate leaf"*: no figure in the sentence, nothing to attribute,
and no cheap way to tell that use from a hypothetical one.  That half is convention only, and
`CONTRIBUTING.md` says so.

Declined claims are printed, with the reason and the count, and do **not** fail the run: this
script's job is to keep the figures it can attribute honest, not to force prose into a template it
can parse.  The count is the honest coverage figure, and a run that suddenly declines more of them
than the last one is worth reading.
"""

from __future__ import annotations

import argparse
import collections
import glob
import os
import re
import sys

# An import line, in both spellings.  Only project imports matter here; a `import Mathlib...` line
# is not part of this walk.
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+(FormalSchemes\.[A-Za-z0-9_.]+)", re.M)

# The claim itself.  `closures` is matched too, in order to *decline* it: the plural is the tree's
# reliable marker of one sentence carrying two figures about two modules.
CLOSURE = re.compile(r"\b(forward|reverse)\s+closure(s?)\b", re.I)

# A figure, with the tree's `**bold**` markup optional.
FIGURE = re.compile(r"(?:\*\*)?(\d+)(?:\*\*)?")

# A sentence break.  A dot inside `FormalSchemes.Foo` is never followed by whitespace, which is
# what makes this safe to use as a bound.
BREAK = re.compile(r"[.;]\s")

# A backticked module, in the two spellings the tree uses for one.
MODULE_TOKEN = re.compile(r"`(FormalSchemes[./][A-Za-z0-9_./]+?)(?:\.lean)?`")

# The `## Placement` opener.  Everything from *A leaf* / *A new leaf* / *Over* up to the colon
# names the modules being imported, so the module tokens inside it are not what the figure after
# the colon is about.  Bounded and non-greedy, and honoured only for figures in the opener's own
# sentence -- see `_mask_openers`.
OPENER = re.compile(r"\b(?:A (?:new )?leaf|Over)\b[^:]{0,240}?:")

# `this leaf over the two has forward closure 44` -- the same construct without a colon.
SELF_PHRASE = re.compile(r"\b[Tt]his (?:leaf|file|module)(?:'s)?\b")

# *that file*, *whose*: a module is meant, and it is the last one named.
ANAPHOR = re.compile(r"\b(?:[Tt]hat (?:file|module|consumer|leaf)(?:'s)?|whose)\b")

# A bare possessive pronoun standing between the anchor and the figure **declines** the claim, and
# this is the one rule here worth its paragraph.  Twice on this tree a sentence runs *"Its reverse
# closure is 0 too"*, where the antecedent is the paragraph's subject -- a file argued about two
# sentences earlier -- while the last module actually named is a different one mentioned in
# passing.  Every rule that resolves by proximity gets both of them confidently wrong, and both
# claims are **correct** as they stand, so the wrong answer would be a repair request against
# correct prose.  A demonstrative (*that file*) names something that has just been the subject; a
# possessive pronoun does not, and nothing in the surface text recovers what it points at.
# `itself` is not a hit: there is no word boundary after `its` inside it.
DECLINER = re.compile(r"\b[Ii]ts\b")

# An indefinite leaf between the anchor and the figure: the figure is about a module that does not
# exist, so there is nothing to compare it against.
BLOCKER = re.compile(r"\ba (?:new )?leaf\b")

# The noun beside the figure is a measurement too.  A sentence that carries a closure figure and
# calls the file it is in a **leaf** -- as a `## Placement` opener (*A leaf over `X`:*) or as a
# self-reference (*against this leaf's 13*) -- asserts that the file's reverse closure is 0, and
# that assertion rots exactly like the numeral beside it: six openers on this tree contradicted
# themselves inside one sentence (row 1823).  Only sentences that already carry a claim are read,
# so this declines nothing that was checked before, and the *other* senses of the word are never
# seen: `Mathlib-only leaf` is a forward-closure claim, `a leaf whose ...` is hypothetical, and the
# 66 proof-tree leaves in the `GeneralFibreProductBothAlgebraData*` modules carry no figure at all.
# A positional noun about *another* module (*`FormalSchemes.TateSeparated`, a Tate leaf*) is out of
# reach for the same reason -- there is no figure in those sentences -- and stays a convention.
SELF_LEAF = re.compile(r"\b[Tt]his leaf\b|\bA (?:new )?leaf\b")

# Figures that ride along with a claim and are checkable against the same walk.  Each is looked for
# between the claim's figure and whichever comes first of the end of its sentence and the next
# closure claim, so a companion always belongs to the claim it is read under.  `offset` is added to
# the claim's own subject count, except for `total`, which is the number of modules under
# `FormalSchemes/`, and `self`, which is the *file's* closure rather than the subject's.
COMPANIONS = [
    (re.compile(r"\((\d+)(?: modules)?(?: counted)? with itself\)"), "subject", 1),
    (re.compile(r"\((\d+)(?: modules)?(?: counted)? besides itself\)"), "subject", 0),
    (re.compile(r"(\d+) with itself\b"), "subject", 1),
    (re.compile(r"(\d+) before this (?:leaf|file|module)"), "subject", -1),
    (re.compile(r"against this (?:leaf|file|module)'s \*{0,2}(\d+)"), "self", 0),
    (re.compile(r"of the project's (\d+) modules"), "total", 0),
    (re.compile(r"over the (\d+) modules under"), "total", 0),
]

# `forward closure 36 with itself` -- the other convention, inline.
WITH_ITSELF = re.compile(r"^\s*(?:project |modules? )*(?:counted )?(?:with itself|including it)")

WINDOW = 320
NUMERAL_REACH = 60
COMPANION_REACH = 400


def project_modules(root: str = ".") -> dict[str, str]:
    """Every module under `FormalSchemes/`, as `module name -> path`.  `FormalSchemes.lean` at the
    repository root is outside the walk, by the convention the tree's own paragraphs state."""
    out = {}
    for path in sorted(glob.glob(os.path.join(root, "FormalSchemes", "**", "*.lean"),
                                 recursive=True)):
        rel = os.path.relpath(path, root)
        out[rel[:-5].replace(os.sep, ".")] = os.path.normpath(path)
    return out


def closures(mods: dict[str, str]) -> tuple[dict[str, set], dict[str, set]]:
    """Forward and reverse closures, neither counting the module itself."""
    deps = {}
    for m, path in mods.items():
        text = open(path, encoding="utf-8").read()
        deps[m] = {d for d in IMPORT.findall(text) if d in mods}
    forward = {}
    for m in mods:
        seen, stack = set(), [m]
        while stack:
            for d in deps[stack.pop()]:
                if d not in seen:
                    seen.add(d)
                    stack.append(d)
        seen.discard(m)
        forward[m] = seen
    reverse = collections.defaultdict(set)
    for m in mods:
        for d in forward[m]:
            reverse[d].add(m)
    return forward, {m: reverse[m] for m in mods}


def _mask_openers(window: str) -> str:
    """Replace each `## Placement` opener by a self anchor of the same length.

    Same length so that positions in the window still line up with the file, and so that the
    module tokens the opener names stop being anchors -- they are the imports, not the subject.
    """
    out = window
    for m in OPENER.finditer(window):
        # Only while the opener's own sentence is still running: `A leaf over X and Y: forward
        # closure 52 ..., reverse closure 2` is two figures about the file, and the sentence after
        # it is about something else again.
        if BREAK.search(window, m.end()) is None and m.end() - m.start() >= len("this leaf"):
            out = out[:m.start()] + "this leaf".ljust(m.end() - m.start()) + out[m.end():]
    return out


def attribute(window: str, self_module: str) -> tuple[str | None, str | None]:
    """Which module the figure at the end of `window` is about, as `(module, declined reason)`."""
    masked = _mask_openers(window)
    anchors = [(m.start(), "self", None) for m in SELF_PHRASE.finditer(masked)]
    anchors += [(m.start(), "named", m.group(1).replace("/", ".")) for m in
                MODULE_TOKEN.finditer(masked)]
    anchors += [(m.start(), "anaphor", None) for m in ANAPHOR.finditer(masked)]
    if not anchors:
        return None, "no anchor"
    pos, kind, name = max(anchors)
    if DECLINER.search(masked[max(a[0] for a in anchors):]):
        return None, "possessive pronoun: its antecedent is the subject, not the last module named"
    if kind == "anaphor":
        before = [(m.start(), m.group(1).replace("/", ".")) for m in MODULE_TOKEN.finditer(masked)
                  if m.end() <= pos]
        if not before:
            return None, "anaphor with no module named before it"
        pos, name = before[-1]
    # An indefinite leaf between what the figure is attributed to and the figure means the figure
    # is about a module that does not exist -- `a leaf whose own forward closure is 231`.
    if BLOCKER.search(masked[pos:]):
        return None, "indefinite leaf between the anchor and the figure"
    return (self_module if kind == "self" else name), None


def claims(mods: dict[str, str]):
    """Yield every closure claim in the tree, as a dict.

    The scan is over the whole file rather than over its comment regions: the phrase *forward
    closure* / *reverse closure* occurs 62 times on this tree and every one of them is in a
    comment, since it is not Lean syntax.  A hit inside code would be reported as a declined claim,
    not silently mis-measured.  Newlines are replaced by spaces rather than removed, so every
    position still maps to a line of the file.
    """
    for module, path in sorted(mods.items()):
        raw = open(path, encoding="utf-8").read()
        flat = raw.replace("\n", " ")
        for m in CLOSURE.finditer(flat):
            line = raw[:m.start()].count("\n") + 1
            end = BREAK.search(flat, m.end())
            back = max(0, m.start() - WINDOW)
            start = max((b.end() for b in BREAK.finditer(flat, back, m.start())), default=back)
            bound = min(end.start() if end else len(flat), m.end() + NUMERAL_REACH)
            fig = FIGURE.search(flat, m.end(), bound)
            base = dict(path=path, line=line, module=module, kind=m.group(1).lower(),
                        text=" ".join(flat[m.start():m.start() + 90].split()),
                        sentence=start, self_leaf=bool(SELF_LEAF.search(
                            flat[start:end.start() if end else len(flat)])))
            if not fig:
                yield dict(base, stated=None, about=None, declined="no figure in the sentence")
                continue
            if m.group(2):
                yield dict(base, stated=int(fig.group(1)), about=None,
                           declined="plural: one sentence, several modules")
                continue
            # The window runs to the figure, not to the phrase: `the reverse closure of `M` is 5`
            # names its subject between the two, and that spelling is on the tree.
            about, why = attribute(flat[max(0, m.start() - WINDOW):fig.start()], module)
            # A companion figure belongs to the nearest claim before it, so the search stops at the
            # end of the sentence or at the next claim, whichever comes first.
            nxt = CLOSURE.search(flat, fig.end())
            stop = min(end.start() + 1 if end else len(flat),
                       nxt.start() if nxt else len(flat), fig.end() + COMPANION_REACH)
            tail = flat[fig.end():max(fig.end(), stop)]
            companions = [(kind, delta, int(c.group(1)), c.group(0))
                          for pat, kind, delta in COMPANIONS
                          for c in [pat.search(tail)] if c]
            yield dict(base, stated=int(fig.group(1)), about=about, declined=why,
                       offset=1 if WITH_ITSELF.match(tail) else 0, companions=companions)


def audit(root: str = ".") -> tuple[list, list]:
    """Every claim in the tree, split into `(mismatches, declined)`."""
    mods = project_modules(root)
    forward, reverse = closures(mods)
    mismatches, declined, called_leaf = [], [], set()
    for c in claims(mods):
        # One report per sentence: a `## Placement` opener carries two claims and one noun.
        seen_here = (c["path"], c["sentence"]) in called_leaf
        if c["self_leaf"] and reverse[c["module"]] and not seen_here:
            called_leaf.add((c["path"], c["sentence"]))
            mismatches.append(dict(
                c, stated=0, actual=len(reverse[c["module"]]),
                what="the reverse closure of `%s`, which this sentence calls a leaf" % c["module"]))
        if c["about"] is None:
            declined.append(c)
            continue
        if c["about"] not in mods:
            declined.append(dict(c, declined="`%s` is not a module of this tree" % c["about"]))
            continue
        size = lambda m: len(forward[m] if c["kind"] == "forward" else reverse[m])
        actual = size(c["about"])
        if c["stated"] != actual + c["offset"]:
            mismatches.append(dict(c, actual=actual + c["offset"]))
        for kind, delta, stated, quoted in c["companions"]:
            # A companion is read under the claim's own convention, so `against this leaf's N`
            # beside `forward closure 36 with itself` means 36's convention, not the other one.
            want = (len(mods) if kind == "total" else
                    size(c["module"]) + c["offset"] if kind == "self" else actual) + delta
            if stated != want:
                mismatches.append(dict(
                    c, stated=stated, actual=want, text="%s -- in `%s`" % (quoted, c["text"][:60]),
                    what=("the number of modules under `FormalSchemes/`" if kind == "total" else
                          "the %s closure of `%s`" % (c["kind"], c["module"]) if kind == "self"
                          else "the %s closure of `%s`" % (c["kind"], c["about"]))))
    return mismatches, declined


def selftest() -> int:
    """The attribution rule against the shapes it has to get right, and the walk against a tree
    built here.  No build and no repository state needed."""
    bad = 0

    def check(name, got, want):
        nonlocal bad
        ok = got == want
        bad += not ok
        print("%s  %s" % ("ok  " if ok else "FAIL", name))
        if not ok:
            print("        want %r\n        got  %r" % (want, got))

    S = "FormalSchemes.Self"
    cases = [
        ("a Placement opener is about the file, not the modules it imports",
         "## Placement A leaf over `FormalSchemes.Bot` and `FormalSchemes.Cmp`: forward closure ",
         (S, None)),
        ("`Over X and Y:` is the same opener",
         "## Placement Over `FormalSchemes.Bot` and `FormalSchemes.Cmp`: reverse closure ",
         (S, None)),
        ("a possessive names its module",
         "They are **not** put there: `FormalSchemes.AdicRing`'s reverse closure ",
         ("FormalSchemes.AdicRing", None)),
        ("a module named between the phrase and the figure is the subject",
         "and the reverse closure of `FormalSchemes.Cmp` is ",
         ("FormalSchemes.Cmp", None)),
        ("`whose` resolves to the module before it",
         "would sit naturally in `FormalSchemes.Completion`, whose reverse closure ",
         ("FormalSchemes.Completion", None)),
        ("`that file` resolves across the sentence break",
         "parked in `FormalSchemes.ActionQuotient`, which it completes. That file has a reverse "
         "closure ", ("FormalSchemes.ActionQuotient", None)),
        ("`this leaf` is the file even with modules named earlier",
         "`FormalSchemes.Bot` and `FormalSchemes.Cmp` are unreachable; this leaf over the two has "
         "forward closure ", (S, None)),
        ("the `.lean` spelling names the same module",
         "declared in `FormalSchemes/ActionInvariantExtension.lean` (forward closure ",
         ("FormalSchemes.ActionInvariantExtension", None)),
        ("a sentence naming no module and no leaf is declined",
         "nothing here attempts one, and a module has reverse closure ", (None, "no anchor")),
        ("a bare possessive is declined rather than resolved to the last module named",
         "*Adding this to `FormalSchemes.Cmp`* was the near miss. That file already imports "
         "`FormalSchemes.Bot`, recording the same cost. Its reverse closure ",
         (None, "possessive pronoun: its antecedent is the subject, not the last module named")),
        ("an indefinite leaf is declined",
         "reachable only through `FormalSchemes.Cmp`, a leaf whose own forward closure ",
         (None, "indefinite leaf between the anchor and the figure")),
    ]
    for name, window, want in cases:
        check(name, attribute(window, S), want)

    import tempfile
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        # `Top` is the only leaf of the three, so it is the only one that may say so.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **3**. -/\n")
        write("Mid", "public import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1** project modules\n"
                     "besides itself (2 counted with itself), reverse closure **1**. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! A leaf over `FormalSchemes.Mid`: `FormalSchemes.Base`'s reverse closure\n"
                     "is **9**. -/\n")
        write("Quiet", "import FormalSchemes.Base\n/-! Nothing measured here. -/\n")
        mis, dec = audit(d)
        check("the walk follows `public import` and both figures of the correct file pass",
              [(m["module"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Top", 9, 3)])
        check("a file with no closure claim reports nothing at all",
              [c for c in mis + dec if c["module"] == "FormalSchemes.Quiet"], [])
        with open(os.path.join(d, "FormalSchemes", "Mid.lean"), encoding="utf-8") as f:
            broken = f.read().replace("(2 counted with itself)", "(7 counted with itself)")
        write("Mid", broken)
        mis, _ = audit(d)
        check("a wrong `counted with itself` companion figure is caught",
              sorted((m["module"], m["stated"], m["actual"]) for m in mis),
              [("FormalSchemes.Mid", 7, 2), ("FormalSchemes.Top", 9, 3)])

    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        # `Base` is imported by both of the others and is called a leaf in neither of the two
        # senses that are not a reverse-closure claim; `Mid` calls itself one and has a consumer.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **2**. It is a\n"
                      "Mathlib-only leaf, and a leaf here would be no better. -/\n")
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! A leaf over `FormalSchemes.Base`: forward closure **1**, reverse\n"
                     "closure **1**. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! `FormalSchemes.Base`'s reverse closure is **2**, 1 before this\n"
                     "file. -/\n")
        mis, _ = audit(d)
        check("a file that calls itself a leaf and has a consumer is caught, once",
              [(m["module"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Mid", 0, 1)])
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! `FormalSchemes.Base`'s reverse closure is **2**, 5 before this\n"
                     "file. -/\n")
        mis, _ = audit(d)
        check("`N before this leaf` also reads `file` and `module`",
              sorted((m["module"], m["stated"], m["actual"]) for m in mis),
              [("FormalSchemes.Mid", 0, 1), ("FormalSchemes.Top", 5, 1)])
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**, and this file is not a leaf. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! `FormalSchemes.Base`'s reverse closure is **2**, 1 before this\n"
                     "module. -/\n")
        mis, _ = audit(d)
        check("neither `Mathlib-only leaf` nor an indefinite one is a reverse-closure claim",
              [(m["module"], m["stated"], m["actual"]) for m in mis], [])
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--tree", action="store_true", help="check every closure figure in the tree")
    g.add_argument("--selftest", action="store_true", help="check the attribution rule and walk")
    args = ap.parse_args()
    if args.selftest:
        return selftest()

    mods = project_modules()
    mismatches, declined = audit()
    attributed = [c for c in claims(mods) if c["about"] is not None]
    print("modules under FormalSchemes/ : %5d" % len(mods))
    print("closure claims attributed    : %5d" % len(attributed))
    print("  figures checked            : %5d   (the claims and their companion figures)"
          % (len(attributed) + sum(len(c["companions"]) for c in attributed)))
    print("  MISMATCH                   : %5d" % len(mismatches))
    print("  declined (see below)       : %5d" % len(declined))
    for c in sorted(mismatches, key=lambda c: (c["path"], c["line"])):
        what = c.get("what") or "the %s closure of `%s`" % (c["kind"], c["about"])
        print("  MISMATCH  %s:%d  %s: states %d, walk gives %d"
              % (c["path"], c["line"], what, c["stated"], c["actual"]))
        print("            %s" % c["text"])
    for c in sorted(declined, key=lambda c: (c["path"], c["line"])):
        print("  declined  %s:%d  %s -- %s" % (c["path"], c["line"], c["declined"], c["text"]))
    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
