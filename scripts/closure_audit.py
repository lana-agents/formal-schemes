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
    python3 scripts/closure_audit.py --sweep

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
* an `import` line inside a `/- ... -/` span is **not** one.  A walker that reads comments
  over-reports, and that is the worse of the two failures: an extra edge moves a *computed*
  closure, so a wrong sentence can be reported as matching and a right one as `MISMATCH`, with no
  warning either way.  The same regex shape run over Mathlib is wrong today for exactly this
  reason -- `Mathlib/Tactic/FunProp.lean:48` writes `import Mathlib.Analysis.Complex.Trigonometric`
  inside a fenced block in its module docstring, and a walk that follows it reports this project's
  Mathlib closure as 2727 where Lean loads 2650.  Under `FormalSchemes/` the population is **0** of
  1186 import lines, so `code_only` below moves nothing on this tree; it is here so that the first
  docstring to quote a Lean snippet does not move an audited figure with nothing in the diff.

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

## The spellings this script cannot read, and why they are counted rather than parsed

`CLOSURE` keys on the words *forward closure* / *reverse closure*, so a sentence that measures the
same thing in any other words is not declined -- it is **invisible**, which is worse, because a
declined claim is at least counted.  The tree has spelled one absolute project-closure figure as
*"the import closure of this file is 82 project modules"*, *"whose import closure of 25 modules"*,
*"its import closure is 214 modules"*, *"this file's transitive closure"*, *"a 31-module transitive
import closure"* and -- inverted -- *"`FormalSchemes.Gluing` being upstream of 272 of this tree's
496 modules"*, which is a **reverse** closure written from the far end.  When row 1832 first read
that population it found **twelve** wrong sentences in eleven files carrying **twenty** wrong
numerals, one of them a project-module total stale by 62.

Extending `CLOSURE` to those spellings was considered twice and declined twice, and the reason is
not cost: *"the closure of `A` is N"* and *"`A` is in the closure of N"* are **opposite** claims in
nearly the same words, so a second grammar has to carry the direction, and getting that wrong turns
a silent gap into confident mis-measurement.  What `--sweep` does instead is *count* them: every
sentence carrying a numeral together with the word `closure`, a project-module total or *upstream
of N*, and that `--tree` neither attributes nor declines.  The word alone is not the trigger --
the `Gluing` sentence quoted above does not contain it.
`--tree` prints the count in its header and never fails on it, so the invisible population stops
being invisible without the script pretending it can parse it.  Sentences naming Mathlib are left
out: they measure Mathlib's import graph, which this script does not walk.

Most of what `--sweep` reports is legitimately out of reach -- deltas whose second figure is
counterfactual, intersections of several closures, peak-RSS numbers, issue numbers.  It is a
reading list, not a failure list.  **A figure in it that is a plain measurement of the tree should
be rewritten in the checked spelling rather than left for the next sweep**, and one endpoint of
every delta is such a measurement: *"importing it would take this file's closure from 48 to 93"*
says the closure is 48 **now**.

## Size figures, and the history figure beside one that is out of reach

A `## Placement` paragraph that says *"appending to `X` was the alternative ... it is **3001** lines
with **84** declarations"* is making two measurements of **another** file, and they rot faster than
any closure figure here: every commit to `X` can move the first, and `X` need not be a module this
one imports or is imported by.  The tree spent three rows on one sentence's pair before this check
existed -- rows 1899, 1906 and 1911, the last of which found the stated count was the file's
declarations **plus** the nine `example`s the same sentence said it excluded.  So a figure
immediately followed by `lines` or `declarations` is attributed by exactly the rule above and
checked against the file it is attributed to:

* **lines** is what `wc -l` gives, the number of `\n`;
* **declarations** is the convention the tree's own gloss states -- `theorem`, `lemma`, `def`,
  `instance` or `class` at column zero with a word boundary after it, on a line **not** inside a
  `/- ... -/` span, nesting tracked.  An `example` is not a declaration: it is anonymous and puts
  nothing in the environment, and it is counted separately.

The comment exclusion is the whole check and not a detail.  Without it
`FormalSchemes/StructureSheafStalkPowerSeriesCounterexample.lean` reads **96** rather than **84**,
because twelve lines of that file's *prose* begin with one of the five keywords -- and a checker
that reads 96 is worse than none, because it would demand a repair against a correct sentence.
`--selftest` pins that with a fixture whose answer changes when the exclusion is dropped.

What is out of reach is the **history** figure in the same sentence, *"28 commits touching it
against 12 for the runner-up"*.  It needs `git`, which nothing else in this script does, and it has
the property no check survives: the commit that repairs it falsifies it.  It stays convention, like
the positional noun about another module above.

A size claim whose subject is an anaphor with no module named in range is **declined**, exactly as a
closure claim is, and the repair is in the prose rather than in `WINDOW`.  Widening the window to
reach the intended module makes a *nearer* one the anchor and turns a decline into a confident wrong
answer; `--selftest` pins that too, so a later widening fails the test instead of mis-measuring.

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

# A sentence naming Mathlib is measuring Mathlib's import graph, not this tree's, and no walk here
# can check it.  It is left out of `--sweep` rather than reported and dismissed every run.
MATHLIB = re.compile(r"Mathlib", re.I)

# What makes a sentence a candidate for `--sweep`.  The word `closure` is the obvious trigger, but
# it is not sufficient: *"`FormalSchemes.Gluing` being upstream of 272 of this tree's 496 modules"*
# is a **reverse**-closure measurement carrying two figures and does not contain the word at all.
# Two further markers are added for that shape -- a project-module total, and `upstream of N` --
# both of which are unambiguous assertions about the import graph however the sentence is worded.
SWEEPABLE = re.compile(r"closure"
                       r"|of (?:this|the) (?:tree|project|library)'s \*{0,2}\d+\*{0,2} modules?"
                       r"|\bupstream of \*{0,2}\d", re.I)

# A size figure: `**3001** lines`, `84 declarations`.  The noun is the trigger, so the figure has
# to be adjacent to it -- `**28** commits touching it` is a history claim and not one of these, and
# a bare numeral is nobody's measurement.
SIZE = re.compile(r"(?:\*\*)?(\d+)(?:\*\*)?\s+(lines|declarations)\b")

# A declaration, by the convention the tree's own gloss states: one of the five keywords at column
# zero with a word boundary after it.  `noncomputable def` and `@[simp] theorem` do not match, and
# that is the gloss's rule rather than an oversight -- but it is a prefix match on the first word of
# the line, so the first such spelling added to a file this tree measures will move the count.
DECLARATION = re.compile(r"(?:theorem|lemma|def|instance|class)\b")

# An `example` is counted, and separately: it is anonymous and puts nothing in the environment.
EXAMPLE = re.compile(r"example\b")

WINDOW = 320
NUMERAL_REACH = 60
COMPANION_REACH = 400


def code_only(text: str) -> str:
    """`text` with every comment blanked out, keeping line and column positions.

    `/- ... -/` spans nest, and `--` runs to end of line outside them; blanked rather than deleted
    so that a caller can compare a masked line against the raw one, and so that offsets and `\n`
    counts still refer to the file on disk.  Both walkers here read the result: the import walk,
    which must not follow a snippet in a docstring, and `file_size`, which must not count a
    declaration keyword that opens a line of prose.  String literals are **not** tracked, so a
    `/-` inside one would open a span that is not there; on this tree the population of that is
    zero, checked both by scanning for it and by comparing the import edges either way.
    """
    out = []
    depth = 0
    for line in text.split("\n"):
        buf = []
        i = 0
        while i < len(line):
            if depth == 0 and line.startswith("--", i):
                buf.append(" " * (len(line) - i))
                break
            if line.startswith("/-", i):
                depth += 1
                buf.append("  ")
                i += 2
                continue
            if line.startswith("-/", i) and depth:
                depth -= 1
                buf.append("  ")
                i += 2
                continue
            buf.append(line[i] if depth == 0 else " ")
            i += 1
        out.append("".join(buf))
    return "\n".join(out)


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
        text = code_only(open(path, encoding="utf-8").read())
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


def file_size(path: str) -> tuple[int, int, int, int]:
    """`(lines, declarations, examples, keyword_lines_in_prose)` for one file.

    `lines` is what `wc -l` gives.  The other three are comment-aware, through the same `code_only`
    mask the import walk uses: a keyword counts only at column zero on a line that is *outside*
    every `/- ... -/` span, with nesting tracked, because twelve lines of one file's prose on this
    tree begin with one of the five keywords and a walk that reads them over-counts by exactly
    that many.  The fourth figure is those lines, returned so that `--selftest` can assert the
    exclusion did something rather than merely that the total came out right.
    """
    raw = open(path, encoding="utf-8").read()
    declarations = examples = in_prose = 0
    for line, code in zip(raw.split("\n"), code_only(raw).split("\n")):
        if DECLARATION.match(code):
            declarations += 1
        elif DECLARATION.match(line):
            in_prose += 1
        elif EXAMPLE.match(code):
            examples += 1
    return raw.count("\n"), declarations, examples, in_prose


def size_claims(mods: dict[str, str]):
    """Yield every `N lines` / `M declarations` claim in the tree, as a dict.

    Same attribution as `claims()`, on the window ending at the figure -- the noun is the claim's
    marker and the figure is immediately before it, so the two coincide.  As there, a hit inside
    code would be reported rather than silently mis-measured.
    """
    for module, path in sorted(mods.items()):
        raw = open(path, encoding="utf-8").read()
        flat = raw.replace("\n", " ")
        for m in SIZE.finditer(flat):
            back = max(0, m.start() - WINDOW)
            start = max((b.end() for b in BREAK.finditer(flat, back, m.start())), default=back)
            about, why = attribute(flat[back:m.start()], module)
            yield dict(path=path, line=raw[:m.start()].count("\n") + 1, module=module,
                       noun=m.group(2).lower(), stated=int(m.group(1)), about=about, declined=why,
                       sentence=start, text=" ".join(flat[m.start():m.start() + 90].split()))


def sentences(raw: str):
    """`(offset, text)` for each sentence of `raw`, over the newline-flattened text."""
    flat = raw.replace("\n", " ")
    pos = 0
    for m in BREAK.finditer(flat):
        yield pos, flat[pos:m.end()]
        pos = m.end()
    yield pos, flat[pos:]


def invisible(mods: dict[str, str]):
    """Every sentence that carries a numeral together with a `SWEEPABLE` marker and that
    `claims()` cannot see at all -- neither attributed nor declined.  Counted, never failed on."""
    for module, path in sorted(mods.items()):
        raw = open(path, encoding="utf-8").read()
        for off, s in sentences(raw):
            if not SWEEPABLE.search(s) or not FIGURE.search(s):
                continue
            if CLOSURE.search(s) or MATHLIB.search(s):
                continue
            yield dict(path=path, line=raw[:off].count("\n") + 1, module=module,
                       text=" ".join(s.split()))


def audit(root: str = ".") -> tuple[list, list, list]:
    """Every claim in the tree, as `(mismatches, declined, size_declined)`.

    Mismatches are one list because `--tree` fails on any of them; the two declined populations are
    kept apart because they are different coverage figures and a reader watching one of them move
    should not have the other mixed into it.
    """
    mods = project_modules(root)
    forward, reverse = closures(mods)
    mismatches, declined, called_leaf = [], [], set()
    size_declined = []
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
    for c in size_claims(mods):
        if c["about"] is None:
            size_declined.append(c)
            continue
        if c["about"] not in mods:
            size_declined.append(dict(c, declined="`%s` is not a module of this tree" % c["about"]))
            continue
        lines, declarations, _examples, _prose = file_size(mods[c["about"]])
        actual = lines if c["noun"] == "lines" else declarations
        if c["stated"] != actual:
            mismatches.append(dict(c, actual=actual, what="the number of %s in `%s`"
                                   % (c["noun"], c["about"])))
    return mismatches, declined, size_declined


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
        mis, dec, _sz = audit(d)
        check("the walk follows `public import` and both figures of the correct file pass",
              [(m["module"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Top", 9, 3)])
        check("a file with no closure claim reports nothing at all",
              [c for c in mis + dec if c["module"] == "FormalSchemes.Quiet"], [])
        with open(os.path.join(d, "FormalSchemes", "Mid.lean"), encoding="utf-8") as f:
            broken = f.read().replace("(2 counted with itself)", "(7 counted with itself)")
        write("Mid", broken)
        mis, _, _sz = audit(d)
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
        mis, _, _sz = audit(d)
        check("a file that calls itself a leaf and has a consumer is caught, once",
              [(m["module"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Mid", 0, 1)])
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! `FormalSchemes.Base`'s reverse closure is **2**, 5 before this\n"
                     "file. -/\n")
        mis, _, _sz = audit(d)
        check("`N before this leaf` also reads `file` and `module`",
              sorted((m["module"], m["stated"], m["actual"]) for m in mis),
              [("FormalSchemes.Mid", 0, 1), ("FormalSchemes.Top", 5, 1)])
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**, and this file is not a leaf. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! `FormalSchemes.Base`'s reverse closure is **2**, 1 before this\n"
                     "module. -/\n")
        mis, _, _sz = audit(d)
        check("neither `Mathlib-only leaf` nor an indefinite one is a reverse-closure claim",
              [(m["module"], m["stated"], m["actual"]) for m in mis], [])

    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        # `Ghost` names `Base` three times and imports it none: in a `/-! -/` span, in a nested
        # one, and indented inside a fenced block, which is the shape a Lean snippet in this
        # tree's prose takes.  `Doc` names it in a `/-- -/` declaration docstring.  `Real` is the
        # only importer, and it carries a trailing `--`, so a mask that ate too much would lose
        # the one real edge here rather than merely keeping the four false ones.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **1**. -/\n")
        write("Ghost", "/-! This file imports nothing: forward closure **0**.  A snippet in\n"
                       "prose,\n"
                       "import FormalSchemes.Base\n"
                       "is not an import; nor is one in a nested span,\n"
                       "/-\n"
                       "import FormalSchemes.Base\n"
                       "-/\n"
                       "nor an indented one inside a fenced block:\n"
                       "  import FormalSchemes.Base\n"
                       "-/\n")
        write("Doc", "/-- A declaration docstring with a snippet in it:\n"
                     "import FormalSchemes.Base\n"
                     "and nothing else. -/\n"
                     "theorem d : True := trivial\n")
        write("Real", "import FormalSchemes.Base  -- with a trailing comment after the name\n"
                      "/-! Over `FormalSchemes.Base`: forward closure **1**. -/\n")
        forward, reverse = closures(project_modules(d))
        check("an `import` inside a comment span is not an edge, and a trailing `--` hides none",
              (sorted(forward["FormalSchemes.Ghost"]), sorted(forward["FormalSchemes.Doc"]),
               sorted(forward["FormalSchemes.Real"]), sorted(reverse["FormalSchemes.Base"])),
              ([], [], ["FormalSchemes.Base"], ["FormalSchemes.Real"]))
        mis, _, _sz = audit(d)
        check("the figures those files quote are the ones a comment-aware walk gives",
              [(m["module"], m["stated"], m["actual"]) for m in mis], [])

    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        # One file per shape `--sweep` has to sort, plus one file carrying both shapes at once:
        # invisibility is a property of the sentence, not of the file it sits in.
        write("Vis", "/-! Over nothing: forward closure **0**. -/\n")
        write("Blind", "/-! Its import closure is 3 modules. -/\n")
        write("Delta", "/-! Importing it would take this file's closure from 4 to 9. -/\n")
        write("Upstream", "/-! It is upstream of 5 of this tree's 6 modules. -/\n")
        write("Mathlib",
              "/-! Not in this project's Mathlib import closure, so 1 import. -/\n")
        write("Wordy", "/-! Its import closure is the two consumers and nothing else. -/\n")
        write("Both", "/-! Over nothing: forward closure **0**. Its import closure is 3. -/\n")
        blind = sorted((c["module"], c["text"][:24]) for c in invisible(project_modules(d)))
        check("--sweep reports every spelling `CLOSURE` cannot read",
              [m for m, _ in blind],
              ["FormalSchemes.Blind", "FormalSchemes.Both", "FormalSchemes.Delta",
               "FormalSchemes.Upstream"])
        check("--sweep reports the blind sentence of a file whose other sentence is checked",
              [t for m, t in blind if m == "FormalSchemes.Both"], ["Its import closure is 3."])

    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        # `Counted` is the shape the comment exclusion exists for: four of its lines begin with one
        # of the five keywords **inside** a comment, one of them inside a nested span, so a walk
        # that reads comments answers 6 where the tree's own convention answers 2.
        counted = ("/-! A note whose own lines begin with the keywords:\n"
                   "theorem is a word this paragraph starts a line with,\n"
                   "instance likewise, and inside a nested span\n"
                   "/-\n"
                   "class again\n"
                   "-/\n"
                   "lemma once more. -/\n"
                   "theorem a : True := trivial\n"
                   "def b : Nat := 0\n"
                   "example : True := trivial\n"
                   "example : True := trivial\n")
        write("Counted", counted)
        lines, declarations, examples, in_prose = file_size(
            os.path.join(d, "FormalSchemes", "Counted.lean"))
        check("the comment exclusion is what makes the count right, and it removes four lines here",
              (lines, declarations, examples, in_prose, declarations + in_prose),
              (counted.count("\n"), 2, 2, 4, 6))

        # The figure is attributed by the same rule as a closure claim, and checked against the
        # file it names rather than the file it is written in.
        write("Says", "/-! Appending to `FormalSchemes.Counted` was the alternative. It is\n"
                      "**%d** lines with **2** declarations. -/\n" % lines)
        mis, _dec, sdec = audit(d)
        check("a size claim about another module is attributed to it and passes",
              ([(m["module"], m["stated"], m["actual"]) for m in mis], sdec), ([], []))

        # The wrong answer to reject is the comment-blind one: 6 is what a walk that reads
        # docstrings returns, and it would demand a repair against correct prose.
        write("Says", "/-! Appending to `FormalSchemes.Counted` was the alternative. It is\n"
                      "**%d** lines with **6** declarations. -/\n" % lines)
        mis, _dec, _sdec = audit(d)
        check("the comment-blind count is reported as a MISMATCH against the checked one",
              [(m["about"], m["noun"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Counted", "declarations", 6, 2)])

        write("Says", "/-! Appending to `FormalSchemes.Counted` was the alternative. It is\n"
                      "**%d** lines with **2** declarations. -/\n" % (lines + 1))
        mis, _dec, _sdec = audit(d)
        check("a stale line count is caught by the same walk",
              [(m["about"], m["noun"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Counted", "lines", lines + 1, lines)])

        write("Says", "/-! Nothing here names a module, and something is 12 lines long. -/\n")
        mis, _dec, sdec = audit(d)
        check("a size claim with no anchor is declined rather than guessed at",
              (mis, [(c["noun"], c["declined"]) for c in sdec]),
              ([], [("lines", "no anchor")]))

        # The case this row exists for, and the one that has to outlive it.  `FormalSchemes.Other`
        # sits beyond `WINDOW` and is **not** the sentence's subject; the anaphor has nothing in
        # range, so the claim declines.  Widening `WINDOW` to reach it would resolve the anaphor to
        # the wrong module and turn this decline into a confident MISMATCH against correct prose --
        # which is what this case fails on, deliberately, rather than the repair being in the tool.
        write("Other", "theorem c : True := trivial\n")
        filler = ("`FormalSchemes.Other` is where the argument starts, and\n"
                  "everything between it and the figure is filler whose only job\n"
                  "is to be longer than the window the attribution rule reads back\n"
                  "over, so that the module named at the top of this paragraph is\n"
                  "out of reach by the time the figure arrives and cannot be taken\n"
                  "for the subject of it. Appending to that file was the one\n"
                  "alternative:\n")
        write("Says", "/-! %sit is **%d** lines with **2** declarations. -/\n" % (filler, lines))
        mis, _dec, sdec = audit(d)
        check("an anaphor whose nearest module token is out of range declines, and stays declined",
              (mis, sorted((c["noun"], c["declined"]) for c in sdec)),
              ([], [("declarations", "anaphor with no module named before it"),
                    ("lines", "anaphor with no module named before it")]))

    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--tree", action="store_true", help="check every closure figure in the tree")
    g.add_argument("--selftest", action="store_true", help="check the attribution rule and walk")
    g.add_argument("--sweep", action="store_true",
                   help="list the closure sentences this script cannot read (never fails)")
    args = ap.parse_args()
    if args.selftest:
        return selftest()

    mods = project_modules()
    if args.sweep:
        blind = list(invisible(mods))
        print("sentences carrying a numeral and a closure marker that --tree cannot see: %d"
              % len(blind))
        print("(Mathlib-closure sentences excluded; most of the rest are deltas, intersections or\n"
              " numerals that are not closure figures -- this is a reading list, not a failure\n"
              " list.  A plain measurement of this tree in here should be rewritten in the\n"
              " `forward closure` / `reverse closure` spelling, and one endpoint of every delta\n"
              " is such a measurement.)")
        for c in blind:
            print("  invisible %s:%d  %s" % (c["path"], c["line"], c["text"][:150]))
        return 0

    mismatches, declined, size_declined = audit()
    attributed = [c for c in claims(mods) if c["about"] is not None]
    sized = [c for c in size_claims(mods) if c["about"] is not None]
    print("modules under FormalSchemes/ : %5d" % len(mods))
    print("closure claims attributed    : %5d" % len(attributed))
    print("  figures checked            : %5d   (the claims and their companion figures)"
          % (len(attributed) + sum(len(c["companions"]) for c in attributed)))
    print("  MISMATCH                   : %5d" % len(mismatches))
    print("  declined (see below)       : %5d" % len(declined))
    print("  invisible (run --sweep)    : %5d   (not a failure: spellings `CLOSURE` cannot read)"
          % len(list(invisible(mods))))
    print("size claims attributed       : %5d   (`N lines` / `M declarations`; commit counts are"
          % len(sized))
    print("  declined (see below)       : %5d    out of reach -- see the module docstring)"
          % len(size_declined))
    for c in sorted(mismatches, key=lambda c: (c["path"], c["line"])):
        what = c.get("what") or "the %s closure of `%s`" % (c["kind"], c["about"])
        print("  MISMATCH  %s:%d  %s: states %d, walk gives %d"
              % (c["path"], c["line"], what, c["stated"], c["actual"]))
        print("            %s" % c["text"])
    for c in sorted(declined, key=lambda c: (c["path"], c["line"])):
        print("  declined  %s:%d  %s -- %s" % (c["path"], c["line"], c["declined"], c["text"]))
    for c in sorted(size_declined, key=lambda c: (c["path"], c["line"])):
        print("  size-declined  %s:%d  %s -- %s"
              % (c["path"], c["line"], c["declined"], c["text"]))
    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
