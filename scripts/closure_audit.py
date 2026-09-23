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
    python3 scripts/closure_audit.py --edge FormalSchemes.A:FormalSchemes.B

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
  Mathlib closure as 2727 where Lean loads 2650.  Under `FormalSchemes/` that population is **0**:
  no *project* import line on this tree sits inside a comment span.  Project import lines are the
  ones `IMPORT` below matches -- not every line beginning with `import`, which is a larger
  population this walk does not follow, and naming which of the two is meant is the point of this
  sentence: the **0** is true of the first and false of the second.  At `d178d6d`, where the
  sentence was written, it was 0 of **1186** project import lines, against 1332 `import` lines of
  any kind of which 1324 survive `code_only`; at `aa79516` it is 0 of **1243**, against 1394 and
  1382.  So `code_only` below moves nothing on this tree; it is here so that the first docstring
  to quote a Lean snippet does not move an audited figure with nothing in the diff.

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
3. a bare possessive pronoun standing between the last anchor and the figure normally **declines**
   the claim, because nothing in the surface text recovers what it points at -- with one
   exception, read off the grammar rather than off proximity: a pronoun in a later coordinate of
   a conjunction inherits the subject the **immediately preceding** coordinate states, when that
   coordinate names exactly one subject and none of its tokens is itself an anaphor.  Two tokens
   for the *same* module still name one subject, which is what keeps the tree's usual *"Over `X`:
   this file's forward closure is **1**, its reverse closure is **0**"* spelling readable rather
   than ambiguous.  *"So this file's forward closure stays **93**, its reverse closure is **3**"*
   is one sentence measuring one module twice, and the second coordinate drops the subject
   because the first just supplied it;
4. and a claim is **declined** -- reported, not guessed at -- when it is plural (*"forward closures
   42 and 6"* is two claims about two modules), when the anaphor has no module token to resolve
   against (*"its module has reverse closure 9"*, where *its* is a declaration's), when an
   indefinite leaf intervenes (*"a leaf whose own forward closure is 231"* is about a module that
   does not exist), or when the pronoun above has no unique subject one coordinate back.

### Why the pronoun was worth a rule

Row 2072 measured the hole with a positive control, and it is the worst-shaped one this script
has had: in *"this file's forward closure stays **93**, its reverse closure is **3**"* the
**forward** figure was checked and the **reverse** figure beside it was declined, so one sentence
had one audited numeral vouching for one unaudited one.  Breaking the forward figure gave
`MISMATCH : 1`; breaking the reverse figure gave `MISMATCH : 0` and a line in the declined list.
Reverse closures are the half this script exists for -- they rot with nothing in the owning file's
diff -- so the declined half was the expensive half.

The rule stays a reading and not a guess, and `--selftest` pins each way it could stop being one:
a subject two coordinates back is not inherited, a subject across a full stop is not inherited,
two coordinate-mates naming *different* modules are not inherited from (two naming the *same* one
are -- a masked `## Placement` opener beside a *this file's* is the tree's commonest spelling),
an anaphor is not chained into, and an indefinite leaf after the inherited anchor still blocks.
Each of those five is a separate case that fails under a separate loosening of the rule.

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

## `--edge`, which prices a tree that does not exist

The other endpoint of such a delta -- the counterfactual one -- is out of reach *as a parsing
problem*, for the reason above, and is not out of reach as a **computation**.  A hypothetical
import is one edge added to the graph this script already walks, so `--edge A:B` re-derives what
that edge would cost instead of trying to read the sentence that states it:

* the modules the edge brings into `A`'s closure;
* which forward closures actually move, over `A` and its consumers -- **and which do not**, because
  a consumer that already reaches everything the edge brings in is unmoved, and *reaches `A`* is
  necessary for a forward closure to move and **not sufficient**.  The tree has shipped that
  mistake in a docstring (issue 2195), and it is the reading this mode exists to make cheap;
* which of the brought-in modules' reverse closures move;
* the `MISMATCH` population the edge would create, against the population the tree has now, so the
  report is about the edge even on a red tree;
* that population partitioned by the three species an import edge can falsify -- `A`'s own forward
  closure, a consumer's forward closure, a brought-in module's reverse closure -- with an
  `unclassified` bucket.  The three are exhaustive as a matter of the graph, so `unclassified` is
  never a level: it is a claim shape nobody has thought about, or a bug here.  It has already been
  the second once -- a `## Placement` opener that calls its file a leaf states a forward closure
  and a reverse closure in one sentence, and the leaf finding read off the wrong one of the two.

If `A` already imports `B` the deletion is priced instead, which is the direction
`FormalSchemes/AwayCompletionAlgHomBasicOpen.lean`'s `## Placement` quotes.

**This mode does not read the counterfactual sentence and must not pretend to.**  It prints what
the tree would say; comparing that against what a paragraph does say is the author's job, exactly
as with `--sweep`.  Every run that produces a report exits **0** -- there is no tree here for a
gate to be about; an invocation this mode cannot make sense of, a name that is not a module of
this tree or a module asked to import itself, still fails as any other bad argument does.

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
#
# There is exactly one shape where the surface text *does* recover it, and `_inherited` below
# reads that one and no other: a pronoun in a later coordinate of a conjunction, whose subject is
# the one the preceding coordinate states.  *"So this file's forward closure stays **93**, its
# reverse closure is **3**"* is one sentence making two measurements of one module, and the second
# coordinate omits the subject precisely because the first just gave it.  That is not proximity
# reasoning -- the inherited anchor is the one the grammar supplies, and it is taken only when the
# preceding coordinate supplies exactly one.
DECLINER = re.compile(r"\b[Ii]ts\b")

# A coordinate boundary within one sentence.  The comma is the marker; a following conjunction is
# consumed with it so that the coordinate starts at its subject.  Backticked module names carry no
# comma, and `_mask_openers` has already run, so a `## Placement` opener listing three parents
# cannot be split here.
CONJUNCT = re.compile(r",\s*(?:(?:and|but|so|while|yet)\s+)?")

# A contrast marker standing between the coordinate boundary and the pronoun cancels the
# inheritance, because the tree writes contrasts with exactly this word and always against a
# *different* subject: `GeneralSeparatedHomLocal.lean` reads *"`FormalSchemes.GeneralSeparated\
# HomLocal` has reverse closure **0** and forward closure **182**, against `FormalSchemes.General\
# SeparatedHom`'s forward closure of **180**"*, and `StructureSheafStalkAlgebraic.lean` reads
# *"...'s reverse closure is 0, where this file's reverse closure is 10"*.  Both spell their
# second subject out today.  If either is ever shortened to *its*, the coordinate rule alone would
# inherit the first subject and report a confident MISMATCH against correct prose -- the one
# outcome that is worse than the decline it replaces.
CONTRAST = re.compile(r"\b(?:against|where|whereas|versus|compared\s+(?:to|with))\b")

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


def direct_imports(mods: dict[str, str]) -> dict[str, set]:
    """Each module's own project `import` lines.  Split out of `closures` so that `--edge` can
    hand back a graph with one edge that the files do not have."""
    deps = {}
    for m, path in mods.items():
        text = code_only(open(path, encoding="utf-8").read())
        deps[m] = {d for d in IMPORT.findall(text) if d in mods}
    return deps


def closures(mods: dict[str, str], deps: dict[str, set] | None = None
             ) -> tuple[dict[str, set], dict[str, set]]:
    """Forward and reverse closures, neither counting the module itself.

    `deps` overrides the graph read off the files, which is the whole of how `--edge` prices a
    tree that does not exist: no worktree, no copy, one entry changed."""
    deps = direct_imports(mods) if deps is None else deps
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


def _coordinates(masked: str) -> list[tuple[int, int]]:
    """The comma-separated coordinates of `masked`'s **last sentence**, as `(start, end)` offsets.

    Bounded by the sentence rather than by the window, because a conjunction is a within-sentence
    construction: a pronoun cannot inherit a subject across a full stop, and the one live decline
    this script has ever had to keep -- *"... was the near miss. That file already imports `Bot`,
    recording the same cost. Its reverse closure ..."* -- is exactly that shape.  Restricting to
    the last sentence leaves it with no preceding coordinate at all, which is why it stays
    declined for a reason rather than by accident.
    """
    start = max((b.end() for b in BREAK.finditer(masked)), default=0)
    out, pos = [], start
    for m in CONJUNCT.finditer(masked, start):
        out.append((pos, m.start()))
        pos = m.end()
    out.append((pos, len(masked)))
    return out


def _inherited(masked: str, anchors: list) -> tuple | None:
    """The anchor a possessive pronoun in the window's last coordinate inherits, or `None`.

    Three conditions, each of which is a way the inheritance could be a guess rather than a
    reading, and all three have to hold:

    * the pronoun is in the coordinate the figure is in, **that coordinate carries no anchor of
      its own** -- if it did, the ordinary last-anchor rule would already have resolved it -- and
      no `CONTRAST` word stands between the coordinate boundary and the pronoun.  A contrast is
      the one construction that *announces* a change of subject, so inheriting across one is
      inheriting exactly where the grammar says not to;
    * the **immediately preceding** coordinate names **exactly one subject**.  Not one anchor
      token: a `## Placement` opener is masked as a self anchor, so *"Over `X`: this file's
      forward closure is **1**, its reverse closure ..."* carries two tokens that designate the
      same module, and declining that would decline the tree's commonest spelling of this shape.
      Two tokens that designate *different* modules is a sentence comparing them and the pronoun
      could be either, so that declines; no token at all means the subject is further back than
      one coordinate, which is the proximity reasoning this script refuses;
    * every one of those tokens is `this file` / `this module` / `this leaf` or a named module --
      **not** an anaphor.  An anaphor is itself a resolution, and chaining one into a pronoun is
      two inferences deep.

    Every other shape returns `None` and declines exactly as before.
    """
    coords = _coordinates(masked)
    if len(coords) < 2:
        return None
    (prev_start, prev_end), (last_start, last_end) = coords[-2], coords[-1]
    pron = DECLINER.search(masked, last_start, last_end)
    if pron is None:
        return None
    if any(last_start <= a[0] < last_end for a in anchors):
        return None
    if CONTRAST.search(masked, last_start, pron.start()):
        return None
    inner = [a for a in anchors if prev_start <= a[0] < prev_end]
    if not inner or any(kind == "anaphor" for _pos, kind, _name in inner):
        return None
    if len({(kind, name) for _pos, kind, name in inner}) != 1:
        return None
    return max(inner)


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
    if DECLINER.search(masked[pos:]):
        inherit = _inherited(masked, anchors)
        if inherit is None:
            return None, ("possessive pronoun: its antecedent is the subject, "
                          "not the last module named")
        pos, kind, name = inherit
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


def audit(root: str = ".", deps: dict[str, set] | None = None) -> tuple[list, list, list]:
    """Every claim in the tree, as `(mismatches, declined, size_declined)`.

    Mismatches are one list because `--tree` fails on any of them; the two declined populations are
    kept apart because they are different coverage figures and a reader watching one of them move
    should not have the other mixed into it.

    `deps` overrides the import graph, for `--edge`.  The claims are still the tree's own -- a
    counterfactual edge changes what the figures should be, never what the prose says.

    Every mismatch carries `subject`, the module the figure is about: the claim's own `about` for
    a plain figure, the *claim's* module for a `self` companion, and `None` for a project total.
    Nothing prints it; `--edge` partitions on it, and reading it off `about` would be wrong for
    exactly the companions.
    """
    mods = project_modules(root)
    forward, reverse = closures(mods, deps)
    mismatches, declined, called_leaf = [], [], set()
    size_declined = []
    for c in claims(mods):
        # One report per sentence: a `## Placement` opener carries two claims and one noun.
        seen_here = (c["path"], c["sentence"]) in called_leaf
        if c["self_leaf"] and reverse[c["module"]] and not seen_here:
            called_leaf.add((c["path"], c["sentence"]))
            mismatches.append(dict(
                c, stated=0, actual=len(reverse[c["module"]]), subject=c["module"],
                # This finding is about a **reverse** closure whatever the claim carrying it was
                # about, and the sentence that triggers it usually states both: an opener reading
                # *"A leaf over `X`: forward closure N, reverse closure 0"* parses as two claims
                # and this fires from whichever comes first.  Inheriting `c["kind"]` therefore made
                # the species `--edge` reports depend on that parse order.
                kind="reverse",
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
            mismatches.append(dict(c, actual=actual + c["offset"], subject=c["about"]))
        for kind, delta, stated, quoted in c["companions"]:
            # A companion is read under the claim's own convention, so `against this leaf's N`
            # beside `forward closure 36 with itself` means 36's convention, not the other one.
            want = (len(mods) if kind == "total" else
                    size(c["module"]) + c["offset"] if kind == "self" else actual) + delta
            if stated != want:
                mismatches.append(dict(
                    c, stated=stated, actual=want, text="%s -- in `%s`" % (quoted, c["text"][:60]),
                    subject=(None if kind == "total" else
                             c["module"] if kind == "self" else c["about"]),
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
            mismatches.append(dict(c, actual=actual, subject=c["about"],
                                   what="the number of %s in `%s`" % (c["noun"], c["about"])))
    return mismatches, declined, size_declined


def _fingerprint(c: dict) -> tuple:
    """A mismatch, identified well enough to subtract one population from another.  The `actual`
    is deliberately **out**: the same wrong sentence is the same defect whatever the edge moves
    the right answer to, and leaving it in would report every pre-existing MISMATCH as new.

    The cost of that, said plainly: a figure that is wrong now and would be **right** under the
    edge is in neither population and is not reported.  `--edge` prices what the edge would
    break, not what it would happen to repair, and on a red tree `--tree` is what finds the
    second."""
    return (c["path"], c["line"], c["stated"],
            c.get("what") or "the %s closure of `%s`" % (c["kind"], c["about"]))


def edge_species(c: dict, importer: str, consumers: set, brought: set) -> int:
    """Which of the three species a mismatch belongs to, or **0**.

    An import edge moves a forward closure only for the importing module and the modules that
    reach it, and a reverse closure only for the modules it newly brings in -- so the three are
    exhaustive as a matter of the graph and **0 is never a level**.  A claim that lands there is
    a shape nobody has thought about, or a bug in this function, and either way it is the line
    the report exists to surface.  Keyed on `subject` rather than on `about`, because a `self`
    companion's `about` is the module the sentence is *comparing* against.
    """
    subject, kind = c.get("subject"), c.get("kind")
    if kind == "forward" and subject == importer:
        return 1
    if kind == "forward" and subject in consumers:
        return 2
    if kind == "reverse" and subject in brought:
        return 3
    return 0


def edge_cost(root: str = ".", importer: str = "", imported: str = "") -> dict:
    """Price `import imported` in `importer` -- adding it, or deleting it if it is already there.

    Nothing is written and no worktree is made: the graph is one entry different from the one the
    files give, and every figure below is that graph walked.
    """
    mods = project_modules(root)
    for name in (importer, imported):
        if name not in mods:
            raise SystemExit("`%s` is not a module under FormalSchemes/" % name)
    if importer == imported:
        raise SystemExit("`%s` cannot import itself" % importer)
    real = direct_imports(mods)
    adding = imported not in real[importer]
    hypo = {m: set(d) for m, d in real.items()}
    (hypo[importer].add if adding else hypo[importer].discard)(imported)

    fwd_real, rev_real = closures(mods, real)
    fwd_hypo, rev_hypo = closures(mods, hypo)
    # Uniform names for the two ends, so that nothing below has to branch on the direction.
    with_edge, without = ((fwd_hypo, fwd_real) if adding else (fwd_real, fwd_hypo))
    # Not `| {imported}`: an import of a module the tree already reaches from here brings in
    # nothing, moves nothing and costs nothing, and that case is the whole of why this mode
    # exists.  `CONTRIBUTING.md` names it -- *"reverse closure 0, so an import is free"* is not
    # the rule, and neither is *"one import, one figure"*.
    brought = with_edge[importer] - without[importer]
    consumers = rev_real[importer] | rev_hypo[importer]
    group = sorted(consumers | {importer})
    moved = [m for m in group if fwd_real[m] != fwd_hypo[m]]
    unmoved = [m for m in group if fwd_real[m] == fwd_hypo[m]]
    rev_moved = sorted(y for y in brought if rev_real[y] != rev_hypo[y])

    base = {_fingerprint(c) for c in audit(root, real)[0]}
    population = [c for c in audit(root, hypo)[0] if _fingerprint(c) not in base]

    def species(c: dict) -> int:
        return edge_species(c, importer, consumers, brought)

    return dict(importer=importer, imported=imported, adding=adding, brought=sorted(brought),
                moved=moved, unmoved=unmoved, rev_moved=rev_moved, baseline=len(base),
                population=sorted(population, key=lambda c: (c["path"], c["line"])),
                species={k: [c for c in population if species(c) == k] for k in (1, 2, 3, 0)},
                forward=(fwd_real, fwd_hypo), reverse=(rev_real, rev_hypo))


def report_edge(r: dict) -> None:
    """`--edge`'s report.  It prints what the tree would say; comparing that against what a
    paragraph does say is the reader's job, which is `--sweep`'s contract and for the same
    reason."""
    fwd_real, fwd_hypo = r["forward"]
    rev_real, rev_hypo = r["reverse"]
    own = [c for c in r["population"] if c["module"] == r["importer"]]
    files = {c["path"] for c in r["population"]}
    print("edge                         : `%s` %s `%s`"
          % (r["importer"], "gains" if r["adding"] else "drops", r["imported"]))
    print("  priced by                  : the import graph one entry different from this tree's;"
          " nothing written")
    # `brings in` / `takes out` are the same width, because every label in this report is
    # one column and a reader diffs two runs of it.
    print("modules the edge %s   : %5d"
          % ("brings in" if r["adding"] else "takes out", len(r["brought"])))
    for m in r["brought"]:
        print("    %s" % m)
    print("forward closures that move   : %5d   of %d walked: this module and its %d consumers"
          % (len(r["moved"]), len(r["moved"]) + len(r["unmoved"]),
             len(r["moved"]) + len(r["unmoved"]) - 1))
    for m in r["moved"]:
        print("    %-58s %4d -> %4d" % (m, len(fwd_real[m]), len(fwd_hypo[m])))
    if r["unmoved"]:
        print("  unmoved, because each already reaches everything the edge brings in -- *reaches"
              " this module* is")
        print("  necessary for a forward closure to move and not sufficient:")
        for m in r["unmoved"]:
            print("    %-58s %4d" % (m, len(fwd_real[m])))
    print("reverse closures that move   : %5d" % len(r["rev_moved"]))
    for m in r["rev_moved"]:
        print("    %-58s %4d -> %4d" % (m, len(rev_real[m]), len(rev_hypo[m])))
    print("figure repairs the edge costs: %5d   in %d files (%d in `%s`, %d in %d others)"
          % (len(r["population"]), len(files), len(own), r["importer"],
             len(r["population"]) - len(own), len(files - {c["path"] for c in own})))
    print("  by species                 : %d / %d / %d, unclassified %d   (this module's own"
          " forward closure /"
          % tuple(len(r["species"][k]) for k in (1, 2, 3, 0)))
    print("                                a consumer's forward closure / a brought-in module's"
          " reverse closure)")
    print("  MISMATCHes already on this tree, excluded above : %d" % r["baseline"])
    for k, what in ((1, "species 1"), (2, "species 2"), (3, "species 3"),
                    (0, "UNCLASSIFIED -- the three are exhaustive, so this is a claim shape "
                        "nobody has thought about, or a bug here")):
        for c in r["species"][k]:
            print("  %s  %s:%d  %s: states %d, the edge would give %d"
                  % (what, c["path"], c["line"],
                     c.get("what") or "the %s closure of `%s`" % (c["kind"], c["about"]),
                     c["stated"], c["actual"]))


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
        ("a possessive in a later coordinate inherits the subject of the preceding one",
         "arrives with the third. So this file's forward closure stays **93**, its reverse "
         "closure ", (S, None)),
        ("the inherited subject can be a named module rather than the file",
         "So `FormalSchemes.AdicRing`'s forward closure is **12**, and its reverse closure ",
         ("FormalSchemes.AdicRing", None)),
        ("a preceding coordinate naming two modules is not inherited from",
         "So `FormalSchemes.Bot` reaches `FormalSchemes.Cmp` already, and its reverse closure ",
         (None, "possessive pronoun: its antecedent is the subject, not the last module named")),
        ("two anchors in the preceding coordinate that designate one module are inherited",
         "## Placement Over `FormalSchemes.Bot`: this file's forward closure is **1**, its "
         "reverse closure ", (S, None)),
        ("a self anchor beside a named one in the preceding coordinate is not inherited from",
         "So this file already imports `FormalSchemes.Bot`, and its reverse closure ",
         (None, "possessive pronoun: its antecedent is the subject, not the last module named")),
        ("a pronoun opening its own sentence inherits nothing across the full stop",
         "This file's forward closure is **4**, measured. Its reverse closure ",
         (None, "possessive pronoun: its antecedent is the subject, not the last module named")),
        ("a coordinate two back is not the one inherited from",
         "So this file's forward closure is **4**, the tree does not move, and its reverse "
         "closure ",
         (None, "possessive pronoun: its antecedent is the subject, not the last module named")),
        ("a contrast between the coordinate boundary and the pronoun cancels the inheritance",
         "`FormalSchemes.Bot` has reverse closure **0** and forward closure **182**, against its "
         "forward closure ",
         (None, "possessive pronoun: its antecedent is the subject, not the last module named")),
        ("`where` is a contrast too, in this tree's prose",
         "`FormalSchemes.Bot`'s reverse closure is **0**, where its reverse closure ",
         (None, "possessive pronoun: its antecedent is the subject, not the last module named")),
        ("an indefinite leaf between the inherited anchor and the figure still blocks",
         "So this file's forward closure is **4**, and a new leaf above it would raise its "
         "reverse closure ", (None, "indefinite leaf between the anchor and the figure")),
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

        # End to end, and the shape row 2072 was filed for: one sentence makes two measurements of
        # one module and names the subject once.  Before the coordinate rule the **reverse** half
        # was declined while the forward half beside it was checked, so a stale reverse figure --
        # the kind that goes wrong with nothing in its own file's diff -- passed silently.  The
        # `attribute` case above pins the resolver; this pins that `audit` reports it, which is a
        # different claim and the one that matters.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **3**. -/\n")
        write("Mid", "public import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: this file's forward closure is **1**, its\n"
                     "reverse closure is **9**. -/\n")
        write("Top", "import FormalSchemes.Mid\n/-! Nothing measured here. -/\n")
        mis, dec, _sz = audit(d)
        check("a stale figure behind a possessive in a later coordinate is now a MISMATCH",
              ([(m["module"], m["kind"], m["stated"], m["actual"]) for m in mis],
               [c["declined"] for c in dec]),
              ([("FormalSchemes.Mid", "reverse", 9, 1)], []))

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

    # `--edge`, on a tree small enough to read.  `Fat` is the case the mode exists for: it reaches
    # `Mid`, so a leaf-property argument says its forward closure moves, and it already reaches
    # `Extra`, so the edge moves it by nothing.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **4**. -/\n")
        write("Extra", "import FormalSchemes.Base\n"
                       "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse\n"
                       "closure **1**. -/\n")
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse\n"
                     "closure **2**. -/\n")
        write("Cons", "import FormalSchemes.Mid\n"
                      "/-! A leaf over `FormalSchemes.Mid`: forward closure **2**, reverse\n"
                      "closure **0**. -/\n")
        write("Fat", "import FormalSchemes.Mid\npublic import FormalSchemes.Extra\n"
                     "/-! Over `FormalSchemes.Mid` and `FormalSchemes.Extra`: this file's\n"
                     "forward closure is **3**, its reverse closure is **0**. -/\n")
        check("the tree the --edge cases are read against is itself green", audit(d)[0], [])

        r = edge_cost(d, "FormalSchemes.Mid", "FormalSchemes.Extra")
        check("an added edge brings in what the tree did not already reach from there",
              (r["adding"], r["brought"]), (True, ["FormalSchemes.Extra"]))
        check("a consumer that already reaches everything the edge brings in is unmoved, and a "
              "consumer that does not is moved",
              (r["moved"], r["unmoved"]),
              (["FormalSchemes.Cons", "FormalSchemes.Mid"], ["FormalSchemes.Fat"]))
        check("the reverse closure of a brought-in module moves",
              r["rev_moved"], ["FormalSchemes.Extra"])
        check("the population is the figures the edge falsifies, and `Fat`'s is not one of them",
              sorted((c["path"].split(os.sep)[-1], c["stated"], c["actual"])
                     for c in r["population"]),
              [("Cons.lean", 2, 3), ("Extra.lean", 1, 3), ("Mid.lean", 1, 2)])
        check("and they partition into the three species with nothing over",
              ({k: len(v) for k, v in r["species"].items()}, r["baseline"]),
              ({1: 1, 2: 1, 3: 1, 0: 0}, 0))

        # The same edge in reverse is the same edge: `--edge` prices the deletion when the import
        # is already there, and the figures are the mirror image.
        write("Mid", "import FormalSchemes.Base\nimport FormalSchemes.Extra\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **2**, reverse\n"
                     "closure **2**. -/\n")
        write("Extra", "import FormalSchemes.Base\n"
                       "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse\n"
                       "closure **3**. -/\n")
        write("Cons", "import FormalSchemes.Mid\n"
                      "/-! A leaf over `FormalSchemes.Mid`: forward closure **3**, reverse\n"
                      "closure **0**. -/\n")
        check("the mirrored tree is green too", audit(d)[0], [])
        r = edge_cost(d, "FormalSchemes.Mid", "FormalSchemes.Extra")
        check("an import already present is priced as a deletion, and by the same graph",
              (r["adding"], r["brought"], r["moved"], r["unmoved"], r["rev_moved"]),
              (False, ["FormalSchemes.Extra"],
               ["FormalSchemes.Cons", "FormalSchemes.Mid"], ["FormalSchemes.Fat"],
               ["FormalSchemes.Extra"]))
        check("and the deletion falsifies the same three figures, downwards",
              sorted((c["path"].split(os.sep)[-1], c["stated"], c["actual"])
                     for c in r["population"]),
              [("Cons.lean", 3, 2), ("Extra.lean", 3, 1), ("Mid.lean", 2, 1)])

        # An import of something the tree already reaches from there is free, and this is the
        # claim `CONTRIBUTING.md` says is not *"one import, one figure"*.
        r = edge_cost(d, "FormalSchemes.Fat", "FormalSchemes.Base")
        check("an edge to an already-reachable module brings in nothing and costs nothing",
              (r["brought"], r["moved"], r["rev_moved"], r["population"]), ([], [], [], []))

        # A red tree is the normal case for a reader who is mid-repair, and the report has to be
        # about the edge and not about the mess.  `Base`'s figure is wrong whatever `Mid` imports.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **9**. -/\n")
        check("the baseline is a real MISMATCH now",
              [(c["module"], c["stated"], c["actual"]) for c in audit(d)[0]],
              [("FormalSchemes.Base", 9, 4)])
        r = edge_cost(d, "FormalSchemes.Mid", "FormalSchemes.Extra")
        check("a MISMATCH the tree already has is counted as the baseline, not as the edge's",
              (r["baseline"], sorted((c["path"].split(os.sep)[-1], c["stated"], c["actual"])
                                     for c in r["population"])),
              (1, [("Cons.lean", 3, 2), ("Extra.lean", 3, 1), ("Mid.lean", 2, 1)]))

    # `unclassified` is reachable, and the shape that reaches it is the one this case is built
    # from: a `## Placement` opener that calls its file a leaf states a **forward** closure and a
    # **reverse** closure in one sentence, so the leaf finding fires from whichever of the two
    # parses first -- while the finding itself is about the reverse closure either way.  Reading
    # its species off the carrying claim therefore made the answer depend on parse order, and six
    # of the seven leaf sentences on this tree parse forward-first.  This case fails without the
    # `kind="reverse"` in `audit`.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        write("Root", "/-! Over nothing: forward closure **0**, reverse closure **1**. -/\n")
        write("Leaf", "import FormalSchemes.Root\n"
                      "/-! ## Placement\n\n"
                      "A leaf over `FormalSchemes.Root`: this file's forward closure is **1**\n"
                      "project module besides itself, and its reverse closure is **0**. -/\n")
        write("Other", "/-! Over nothing: forward closure **0**. -/\n")
        check("the leaf tree is green before the edge", audit(d)[0], [])

        r = edge_cost(d, "FormalSchemes.Other", "FormalSchemes.Leaf")
        check("an edge into a leaf brings in the leaf and everything under it",
              (r["adding"], r["brought"]),
              (True, ["FormalSchemes.Leaf", "FormalSchemes.Root"]))
        check("a sentence calling its file a leaf is reported twice and **both** are species 3, "
              "the plain reverse claim and the leaf finding",
              sorted((c["path"].split(os.sep)[-1], c.get("what", ""))
                     for c in r["species"][3]),
              [("Leaf.lean", ""),
               ("Leaf.lean", "the reverse closure of `FormalSchemes.Leaf`, which this sentence"
                             " calls a leaf"),
               ("Root.lean", "")])
        check("and nothing the edge falsifies is left unclassified",
              ({k: len(v) for k, v in r["species"].items()},
               [c["path"].split(os.sep)[-1] for c in r["species"][1]]),
              ({1: 1, 2: 0, 3: 3, 0: 0}, ["Other.lean"]))

    # The bucket is exercised on the classifier too, over shapes no tree has to produce.  A
    # project total is the one that comes closest to reaching it: it has no subject at all.
    check("a figure with no subject is unclassified rather than forced into a species",
          [edge_species(c, "FormalSchemes.Mid", {"FormalSchemes.Cons"}, {"FormalSchemes.Extra"})
           for c in ({"subject": None, "kind": "forward"},
                     {"subject": "FormalSchemes.Quiet", "kind": "forward"},
                     {"subject": "FormalSchemes.Quiet", "kind": "reverse"},
                     {"subject": "FormalSchemes.Extra", "kind": "forward"},
                     {"subject": "FormalSchemes.Mid", "kind": "forward"},
                     {"subject": "FormalSchemes.Cons", "kind": "forward"},
                     {"subject": "FormalSchemes.Extra", "kind": "reverse"})],
          [0, 0, 0, 0, 1, 2, 3])

    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--tree", action="store_true", help="check every closure figure in the tree")
    g.add_argument("--selftest", action="store_true", help="check the attribution rule and walk")
    g.add_argument("--sweep", action="store_true",
                   help="list the closure sentences this script cannot read (never fails)")
    g.add_argument("--edge", metavar="A:B",
                   help="price adding `import B` to module A -- or deleting it, if A already has"
                        " it.  Reports a tree that does not exist, so it never fails")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if args.edge:
        if args.edge.count(":") != 1:
            raise SystemExit("--edge takes `FormalSchemes.A:FormalSchemes.B`")
        report_edge(edge_cost(".", *args.edge.split(":")))
        return 0

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
