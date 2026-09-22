#!/usr/bin/env python3
"""Flag a docstring paragraph that has been left with a word or two stranded on a line of its own.

A figure repair that lengthens a word -- `two` to `three`, `three` to `four` -- re-fills the
paragraph it sits in, and can push the tail of a sentence onto a line by itself:

    ...the root module list and nothing else, and moves
    no
    stated figure anywhere on the tree. ...

**Nothing standing on this tree reads that.**  `lake build --wfail` is silent, `closure_audit.py`
reads figures and not fills, `citation_audit.py` resolves names, and the width check is silent
because the line is *short* rather than long.  The board has named two classes of figure defect --
digits, which `closure_audit --tree` catches, and word-spellings, which only a hand-written scan
catches -- and this is a third.  Issue 2139's forty-one-site figure repair introduced two of them
and issue 2154 repaired them by hand; this is the instrument.

Usage, from the repository root.  No `lake`, no build, no environment.

    python3 scripts/reflow_widow_scan.py --diff upstream/master...HEAD
    python3 scripts/reflow_widow_scan.py --tree
    python3 scripts/reflow_widow_scan.py --selftest

**`--diff` is the mode that earns this script.**  The useful question is *"did this diff strand a
word?"*, not *"how many are on the tree?"* -- the standing population is a wart with precedent, and
issue 2159 argues on measurement that it should not be swept.  `--tree` exists so that the number
can be seen not to grow, and it prints no verdict: a flag here is a **question**, exactly as in
`docstring_signature_scan.py`, and this script is deliberately **not** in
`.orchestra/validation.sh`.

## What `--diff` reads: the two git shapes that got it wrong, and what the second fix rests on

`--diff` scans both ends of a range and reports a stranded line the head has and the base does
not, keyed by the line's *text* rather than by its number.  Two facts about `git diff` decide
which bytes each end is read from, and both were wrong here first; a third decides whether the
second fix is switched on at all:

* **A range's `-` side is not always the ref on its left.**  `git diff A...B` reports the changes
  on `B` since `merge-base(A, B)`, so a three-dot base has to go through `git merge-base` before
  anything is read out of it.  Read at `A` instead, a branch whose base has moved is told about
  every widow that landed on *master* since it forked: at `4873811` plus one trivial commit, with
  `upstream/master` at `b3c6e7d`, three commits further on, `--diff upstream/master...HEAD` blamed
  that commit for `four imports`, the widow issue 2139 introduced and issue 2154 repaired.  The
  distance is quoted against a named commit rather than on its own, because `4873811` to master's
  tip was two commits when this control was first run and is three now.  `A..B` is `git diff A B`
  and its base really is `A`; `range_ends` pins all four spellings.
* **A diff names two paths and either may be absent.**  A rename names the old path on the `-`
  side and the new one on the `+` side, and `git show <base>:<new path>` finds nothing there, so
  a renamed module's whole standing population reads as introduced.  On `befe0fd`, ten modules
  renamed in one commit, that was **five** reported of which **four** were pre-existing at the old
  path -- three of them at the very same line number and `rest. -/` at `:328` there against `:332`
  here, which is why the comparison is keyed to the line's **text** and never to its number.  With
  both paths kept the same range reports **one**, and that one is
  real: the rename lengthened a backticked name, the paragraph around it re-filled, and `it.` is
  stranded at `BasicOpenCoverSeparatedScheme.lean:32`.  A name-lengthening refactor stranding a
  word is exactly this scan's subject, and four false positives were hiding it.
* **The rename half rests on `-M`'s own detection, which is switchable from outside.**  Every
  `.lean` rename in this tree's history is *inexact* -- ten records, scoring `R068` to `R096`, none
  `R100` -- so each is found by the exhaustive pass, which git **skips, with a warning on stderr
  that this script discards**, once `diff.renameLimit` is exceeded.  With the pin removed and
  `diff.renameLimit=1` injected, the rejected behaviour **would** come back in full and in
  silence: `befe0fd` then reads as **38** files touched rather than 28 and **five** reported
  rather than one.  It does not come back through the call as it stands, which carries
  `-c diff.renameLimit=0` -- run under that same injected configuration it still reads 28 and one,
  because `-c` outranks every repository, user and system setting.
  A rename whose similarity falls *under* `-M`'s 50% default is a different shape: git reports it
  as a delete plus an add, an add has no old path, and that module's whole standing population then
  reads as introduced.  The worst real case on this tree is `R068`, eighteen points of margin, so
  the threshold is left at its default -- this bullet is the record of what that rests on.

## The predicate, and the four rejected alternatives that are the argument for it

Issue 2154 proposed *"non-indented lines of at most two words inside a doc span"*.  Run it and
it is useless, because the last line of every filled paragraph is short.  Each refinement below was
measured on this tree rather than reasoned about; the figures are at `4873811` under **this file's
own paragraph segmentation**, and a pull request that adds a module moves all of them, so
re-measure rather than quoting them.

    population  predicate, each row adding a conjunct to the one above
    ----------  --------------------------------------------------------------------------
    2089 lines  a <=2-word line inside a doc span -- the last line of every filled
                paragraph, so this is every paragraph
     209 lines  ... and its first word fits on the line above -- **rejected, and not
                because 209 is small**: the count is monotone in the width (132 / 209 /
                322 / 434 at 98 / 99 / 100 / 101), so it cannot discriminate one width
                from another and is no evidence about either
    2989 paras  a greedy refill of the paragraph at 99 differs from what is there --
                **this tree is not greedily filled**, and that is deliberate: authors break
                before long backticked names
     555 paras  ... and the refill **saves at least one line** -- still mostly sense-breaks
                that happen to be compressible, with nothing short stranded in them
     162 paras  ... and the paragraph holds a <=2-*plain*-word line -- close
    **160/164** ... and that line is not forced short by an unbreakable neighbour, and is
                not the paragraph's first -- **the predicate**

The two conjuncts do different jobs and neither works alone.  *Saves a line* rules out the
thousands of paragraphs this tree breaks for sense at no cost in lines.  *Holds a short plain line*
rules out the several hundred whose only compressible line is a long backticked name the author put
on a line of its own on purpose -- **plain** means every word on it is backtick-free and at most
`--max-token` characters.

## The fill width, and why it is 99

**A width is a claim about the convention of the text the scan reads, so it is checkable** -- and
the first default here was 100, argued for by the rejected row above and never checked against the
tree.  It is checked now, twice, over the 7863 paragraphs at `4873811`.  *Exact-fill* below counts
paragraphs that are **byte-identical** to a greedy fill at `w`, by a fill written from the
definition rather than by calling `refill`:

    w     exact-fill paragraphs (of 7863)   flagged paragraphs
    ---   -------------------------------   ------------------
     96                              2386                   78
     97                              3393                   93
     98                              4465                  119
    **99**                       **4874**              **160**
    100                               4022                  226
    101                               2734                  309
    102                               1906                  383

**The curve is single-peaked and the peak is at 99**, by 409 paragraphs over 98 and by 852 over
100.  That is the signature of a fill width: at the true width the fill reproduces the file and one
column either side it does not.  (The peak is 62 % and not 100 % because of the deliberate breaks
the row above measures; the *location* is the signal, not the height.)  Note the second column:
**the flagged count rises monotonically in `w`**, so a wider default is strictly more sensitive and
"when in doubt take the larger number" is the wrong instinct here.

**The cleaner test is head-to-head.**  Restrict to the paragraphs where a 99-fill and a 100-fill
actually disagree -- 2690 of them -- and ask which one the file matches: **1221 the 99-fill, 369
the 100-fill**, 1100 neither.  **3.3 : 1**, with every undecidable paragraph excluded by
construction.  Against the neighbours, 99 beats 98 by **1090 : 681** and 101 by **2406 : 266**.

**What the old default bought, on the instrument's own census.**  The two flag sets are nested:
**66** paragraphs are flagged at 100 and not at 99, and **0** the other way round.  So the width
never traded one population for another -- widening it only ever added, and it added 29 % of its
own headline figure.  Of the 66:

* **38 are byte-identical to a greedy fill at 99** and **0** to a fill at 100 -- correctly filled
  prose by this tree's own practice, flagged for not being packed tighter.
* **65 of the 66 have no repair at 99 at all.**  Take the smallest window ending at the paragraph's
  end whose refill is shorter: at 99 there is none, and at 100 there is one whose longest line is
  **exactly 100 columns**, in every one of the 65.  **The old default's extra flags were requests
  to emit a 100-column line**, which is inside `CONTRIBUTING.md`'s limit and outside this tree's
  fill.  An instrument whose repair violates the convention it measures is asking a question with
  no admissible answer.

**The one flag a 99 default really does lose, and it is not free.**  The sixty-sixth is
`AwayBaseChangeChartTransition.lean:92`, which strands `would carry:` and *has* a 99-safe repair --
a four-line window refilling to three at 98 columns -- yet `widows` misses it at 99, because the
paragraph holds a line of exactly **100** columns and a greedy 99-fill must re-break it, spending
the line the repair would save.  **That is the class: a paragraph holding a line wider than the
fill width.**  549 paragraphs here hold one; exactly **1** of them becomes a missed widow, and
`--width 100` still finds it.  The class is named rather than repaired because repairing it means
changing the first conjunct, and the conjuncts are issue 2159's.

## The two exclusions, and the case an instrument must not flag

A short line can be short because **what follows it cannot fit beside it**, and a short line can be
the **first** of its paragraph, with nothing above it to be pulled onto.  Neither is a widow, so a
line is not reported in either case.

**Start with the tree's famous negative, and with the conjunct that actually excludes it.**  Issue
2154 named `GeneralSeparatedBaseChange.lean`'s bare `and` as a widow and it is not one -- and the
reason is the **first conjunct**, not either exclusion.  Its paragraph is thirteen lines and
refills into thirteen, saving nothing, so `widows` returns at its opening
`len(lines) - len(refill(...)) < 1` and no exclusion is ever consulted.  That is exactly the reason
issue 2159 gave.  An earlier version of this paragraph credited the successor exclusion instead,
understandably: the `and` *is* wedged between long backticked names, `3 + 1 + 97` columns, so that
test would fire too **if it were reached**.  **A line can meet two rules and be excluded by only
one of them, and the prose has to name the one that runs first.**

**So the exclusions are justified on their own instances, and there are three of those.**
Measured at `90be36d`, over the 165 short-plain lines living in paragraphs that refill shorter:

    excluded by                                  lines  which
    -------------------------------------------  -----  -------------------------------------
    the next line is a single unfittable token       1  `AwayBaseChangeSeparated.lean:892`,
                                                        `discharged here:`
    the line is its paragraph's first                1  `TateInvNodeChartQuotientSpf.lean:216`,
                                                        `This is`
    both                                             1  `TateInvNodeChartDescent.lean:257`,
                                                        `This is`
    reported                                       162

**The second exclusion is not the first in disguise, and the two `This is` lines are the proof.**
Both read `This is` at 7 columns, both are their paragraph's first line, and they differ only in
the width of the backticked name below.  At `TateInvNodeChartQuotientSpf.lean:217` that name is 89
columns, so `7 + 1 + 89` fits at 99 and the successor rule genuinely does not reach the line --
only the first-line rule excludes it.  At `TateInvNodeChartDescent.lean:258` it is 94, so
`7 + 1 + 94` does not fit and both rules fire.  So each rule has **one line it excludes alone and
one it shares**, which is the figure to weigh before loosening either, and none of the three is the
`and`.

`--selftest` pins both on **synthetic** paragraphs rather than on those three lines.  The successor
fixture's paragraph deliberately *does* refill shorter, so that it tests the exclusion and not the
first conjunct; the `and`'s own shape -- a short line in a paragraph that refills to the same
length -- is pinned separately, by the fixture that has no exclusion in it at all.

**And the `and`'s line number is the best advertisement in this file for `--diff` over `--tree`.**
Issue 2154 quoted it as `:1030`, which was right at issue 2154's tree.  Issue 2159 quoted `:1030`
at a base it defines as *"`4873811` plus row 2154's own two reflows"*, where it is `:1029` -- moved
by one because the second of those reflows refilled the `four imports` widow **above** it from four
lines into three.  *Above*, at no particular distance: that widow is at `:181` and the `and` at
`:1030`, eight hundred and forty-nine lines apart at `4873811`.  A figure about a line number
goes stale when the line above it is repaired, which is this scan's own subject landing on the
prose about this scan.

## Where the population comes from, and why it is wider than issue 2159 measured

Every `/-! ... -/` **and** `/-- ... -/` block, with fenced blocks, lists, tables, headings and
indented lines excluded -- they are not filled prose and must never be rewrapped.  Declaration
docstrings are in scope because two of the three standing instances issue 2159 names are in one
(`StructureSheaf.lean`'s `one.` and `StructureSheafStalkPowerSeriesCounterexample.lean`'s `it.`);
a module-docstring-only population reads 85 paragraphs here and **contains neither**.

**The closing `-/` counts as one of the two words.**  A line *beginning* `-/` is structural and
is never rewrapped; a line *ending* ` -/` is ordinary filled prose whose last word happens to be
the delimiter.  Of the 162 lines reported at `90be36d`, **46** are of that shape -- `rest. -/`,
`injective. -/` -- so for 28 % of the population the predicate reads *one* prose word plus the
delimiter.  They are widows all the same, and a refill leaves the `-/` at the end where it was;
the figure is here so that anyone loosening `is_short_plain` knows how much of the population
turns on it.

**The gap to issue 2159's 136 / 139 is unexplained, and this file does not claim to explain it.**
The conjuncts are that row's and reproduce; the segmentation is what differs, and sweeping it at
`4873811` lands nowhere near that row's intermediate figures of 3193 and 493 either:

    segmentation                      refill differs   saves a line   reported
    --------------------------------  --------------  -------------  ----------
    this file (`/-!` and `/--`)                 2989            555   160 / 164
    `/-!` only                                  1549            282    85 /  87
    `/--` only                                  1440            273    75 /  77
    structural-line rule dropped                6006           2537  1122 / 1189
    fenced-block rule dropped                   3001            559   160 / 164

The three ratios against 3193 / 493 / 136 are 0.94, 1.13 and 1.18 -- not constant, so it is not
one uniform scope difference either.  The fourth row is the only one the structural-line repair
below could not move, and that is by construction: it drops the rule the repair changed.  A sweep
whose every row moves is not measuring the rule it names.  What **is** established is narrower
and is enough to fix the population: any module-docstring-only reading is wrong, because two of
that row's own ground-truth widows are in `/--` blocks.  The lesson is the general one -- *a
prose specification can pin a predicate and cannot pin a population.*  Both of 2159's conjuncts
transferred without ambiguity and its segmentation did not.  **Publish the segmentation rule, or
a ground-truth list the next reader can check theirs against**; 2159 named five specific lines,
and those five are what settled this.

**And the rule this file publishes is the second one it had.**  The first required a bullet with
no space after it -- `^[*\-|#>+]` -- which also matches `**a bold lead-in**` and `*an italic
one*`, and `^\d+\.` with no space, which also matches a continuation line opening `10.12's`.  All
three are filled prose that this tree's own authors re-fill, so a paragraph holding one was split
at it and its fill test ran on a fragment.  Censused over the unindented lines inside doc spans
at `b3c6e7d`: **937** `**`-led lines, **149** `*`-led ones and **18** opening `<digits>.` without
a space were read as structure, while everything the rule is *for* keeps the space -- 4001 `* `
items, one `+ ` item, 78 numbered items, and every one of the 799 `-`-leading lines is a `-/`
already covered by its own alternative.  **1104 classifications corrected, 0 lost**, and the
population went 148 / 152 to 160 / 164 at `4873811` -- 12 stranded lines the scan could not see,
and not one spurious.  *A structural-line rule must require the space that makes a list marker*;
the shape that hid this is that no fixture and none of the pinned `--diff` ranges contained an
emphasis-led line, so twelve green runs said nothing.

**This is not an autoformatter.**  It reports a line and the refill that would absorb it; it never
rewrites a file.  Repairing a widow is a judgement about the smallest window that removes it --
issue 2154's two repairs are two lines into one and four into three -- and a full greedy refill
of a paragraph routinely destroys breaks the author chose.
"""

from __future__ import annotations

import argparse
import glob
import os
import re
import subprocess
import sys
import unicodedata


# The fill width this tree is written at, which is **not** the 100-column limit `CONTRIBUTING.md`
# sets: the limit is *at most 100* and the practice is *fill at 99*, and both hold at once.  99 is
# measured rather than chosen -- see the `## The fill width` section of the docstring -- and it is
# the number every figure above and below is taken at.  `--width` overrides it and both report
# paths print it, so no figure from this instrument can be quoted without the width beside it.
WIDTH = 99
MAX_TOKEN = 14

# Both report paths print the width on their summary line, so no figure taken from this instrument
# can be quoted without it being visible in the same output.  One constant, pinned by `--selftest`,
# because the default moved once (issue 2167) and the figures it moved were quoted without it.
WIDTH_LINE = "fill width / max plain word       : %5d / %d"

# A line that is not filled prose.  Indented text, a list item, a table row, a heading, a block
# quote, a fence, and the `/-` and `-/` delimiters themselves: rewrapping any of them is wrong, so
# none of them may be inside a paragraph this script considers.
#
# **A list marker is `*`, `-` or `+` followed by a space**, and a numbered item is digits, a dot
# and a space.  Requiring that space is the whole difference between this rule and the one that
# shipped first, which required none and so read `**a bold lead-in**`, `*an italic one*` and a
# continuation line opening `10.12's` as structure.  All three are filled prose and this tree
# re-fills them; see the segmentation section of the docstring for what the omission cost.
STRUCTURAL = re.compile(r"^\s|^[*\-+]\s|^[|#>]|^\d+\.\s|^```|^/-|^-/")


def cols(text: str) -> int:
    """Display width, with combining marks at zero and East Asian wide characters at two."""
    return sum(0 if unicodedata.combining(c) else
               (2 if unicodedata.east_asian_width(c) in ("W", "F") else 1) for c in text)


def refill(lines: list[str], width: int) -> list[str]:
    """`lines` re-flowed greedily at `width`, which is what a fill would have produced."""
    out: list[str] = []
    current = ""
    for word in " ".join(lines).split():
        trial = word if not current else current + " " + word
        if cols(trial) > width and current:
            out.append(current)
            current = word
        else:
            current = trial
    if current:
        out.append(current)
    return out


def doc_spans(text: str, opener: str) -> list[tuple[int, int]]:
    """Inclusive 1-based line ranges of `opener ... -/` blocks, nesting-aware.

    Scanned directly rather than recovered by comparing a stripped copy against the original: the
    two disagree by two characters at every `-/`, and aligning them is where sessions have lost
    time.
    """
    spans: list[tuple[int, int]] = []
    depth, start = 0, 0
    for number, line in enumerate(text.split("\n"), 1):
        i = 0
        while i < len(line):
            if depth and line.startswith("-/", i):
                depth -= 1
                i += 2
                if depth == 0:
                    spans.append((start, number))
                continue
            if depth == 0 and line.startswith(opener, i):
                depth, start = 1, number
                i += len(opener)
                continue
            if depth and line.startswith("/-", i):
                depth += 1
                i += 2
                continue
            i += 1
    return spans


def paragraphs(text: str,
               openers: tuple[str, ...] = ("/-!", "/--")) -> list[list[tuple[int, str]]]:
    """Every run of two or more consecutive filled-prose lines inside a block docstring."""
    inside: set[int] = set()
    for opener in openers:
        for first, last in doc_spans(text, opener):
            inside |= set(range(first, last + 1))
    return _paragraphs_of(text.split("\n"), lambda n: n in inside)


def _paragraphs_of(lines: list[str], is_doc) -> list[list[tuple[int, str]]]:
    out: list[list[tuple[int, str]]] = []
    current: list[tuple[int, str]] = []
    fenced = False
    for number, line in enumerate(lines, 1):
        usable = bool(line.strip()) and is_doc(number)
        if usable and line.strip().startswith("```"):
            fenced = not fenced
            if current:
                out.append(current)
                current = []
            continue
        if usable and not fenced and not STRUCTURAL.match(line):
            current.append((number, line))
        elif current:
            out.append(current)
            current = []
    if current:
        out.append(current)
    return [p for p in out if len(p) >= 2]


def is_short_plain(line: str, max_token: int = MAX_TOKEN) -> bool:
    """At most two words, none backticked and none longer than `max_token` characters."""
    words = line.split()
    return 1 <= len(words) <= 2 and all("`" not in w and len(w) <= max_token for w in words)


def widows(paragraph: list[tuple[int, str]], width: int = WIDTH,
           max_token: int = MAX_TOKEN) -> list[tuple[int, str]]:
    """The stranded lines of `paragraph`, or `[]` if there are none.

    Both conjuncts, then the two exclusions.  See the module docstring for what each rules out and
    what breaks if it is dropped.
    """
    lines = [line for _, line in paragraph]
    if len(lines) - len(refill(lines, width)) < 1:
        return []
    out = []
    for index, (number, line) in enumerate(paragraph):
        if not is_short_plain(line, max_token):
            continue
        if index == 0:
            continue
        if index + 1 < len(paragraph):
            following = paragraph[index + 1][1].split()
            if len(following) == 1 and cols(line) + 1 + cols(following[0]) > width:
                continue
        out.append((number, line))
    return out


def lean_files(root: str) -> list[str]:
    """Every module under `FormalSchemes/`, by a filesystem walk rather than `git ls-files`.

    A `git archive` extraction is not a repository, and both ends of a `--diff` comparison are
    routinely read out of one.
    """
    out = []
    for base, _, entries in os.walk(os.path.join(root, "FormalSchemes")):
        for entry in entries:
            if entry.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(base, entry), root))
    return sorted(out)


def scan_text(text: str, width: int, max_token: int):
    found = []
    for paragraph in paragraphs(text):
        stranded = widows(paragraph, width, max_token)
        if stranded:
            found.append((paragraph, stranded))
    return found


def scan_tree(root: str, width: int, max_token: int):
    out = []
    for path in lean_files(root):
        with open(os.path.join(root, path), encoding="utf-8") as handle:
            text = handle.read()
        for paragraph, stranded in scan_text(text, width, max_token):
            out.append((path, paragraph, stranded))
    return out


def show(path: str, paragraph, stranded, width: int) -> None:
    lines = [line for _, line in paragraph]
    print("  %s:%d  paragraph of %d lines, refills to %d"
          % (path, paragraph[0][0], len(lines), len(refill(lines, width))))
    for number, line in stranded:
        print("      :%d  %r" % (number, line.strip()))


def report_tree(root: str, width: int, max_token: int) -> int:
    hits = scan_tree(root, width, max_token)
    modules = len(lean_files(root))
    stranded = sum(len(s) for _, _, s in hits)
    print("modules under FormalSchemes/      : %5d" % modules)
    print(WIDTH_LINE % (width, max_token))
    print("FLAGGED: paragraphs with a stranded line : %5d   (%d lines)" % (len(hits), stranded))
    for path, paragraph, s in hits:
        show(path, paragraph, s, width)
    print()
    print("A flag is a question, not a finding: re-fill the paragraph by the smallest window that")
    print("absorbs the line, or decline it by name with a reason.  This scan has no verdict or")
    print("exit code of its own -- the standing population is a wart with precedent (issue 2159),")
    print("and `--diff` is the mode that keeps it from growing.")
    return 0


def range_ends(diff_range: str) -> tuple[str, str, bool]:
    """`(base spelling, head spelling, is the base a merge-base?)` for a `git diff` range.

    `git diff A...B` reports the changes on `B` **since `merge-base(A, B)`**, so the `-` side of
    that diff describes the file at the merge-base and not at `A`; reading it at `A` is what made
    a widow that master had already repaired look freshly introduced.  `A..B` is `git diff A B`
    and its base really is `A`.  A bare `A` is `git diff A`, whose other end is the worktree, and
    the empty head spelling reads it out of the index.
    """
    base, sep, head = diff_range.partition("...")
    if sep:
        return base, head or "HEAD", True
    base, sep, head = diff_range.partition("..")
    return base, head if sep else "", False


def changed_paths(records: str) -> list[tuple[str | None, str | None]]:
    """`(old path, new path)` pairs from `git diff --name-status -M -z` output.

    **A diff names two paths, not one, and either may be absent.**  A rename names the old path on
    the `-` side and the new one on the `+` side, and `git show <base>:<new path>` cannot find a
    file that did not exist there yet: read at the new path, a renamed module's whole standing
    widow population reads as introduced by the range.  On `befe0fd`, which renames ten modules in
    one commit, that is five pre-existing lines reported out of six.

    `-z` rather than newlines because it is unambiguous: a rename record is three NUL-separated
    fields and every other record is two.
    """
    fields = [f for f in records.split("\0") if f]
    out: list[tuple[str | None, str | None]] = []
    i = 0
    while i < len(fields):
        status = fields[i][:1]
        if status in ("R", "C") and i + 2 < len(fields):
            out.append((fields[i + 1], fields[i + 2]))
            i += 3
        elif status == "A" and i + 1 < len(fields):
            out.append((None, fields[i + 1]))
            i += 2
        elif status == "D" and i + 1 < len(fields):
            out.append((fields[i + 1], None))
            i += 2
        elif i + 1 < len(fields):
            out.append((fields[i + 1], fields[i + 1]))
            i += 2
        else:
            break
    return out


def report_diff(diff_range: str, root: str, width: int, max_token: int) -> int:
    base, head, from_merge_base = range_ends(diff_range)
    if from_merge_base:
        base = subprocess.run(["git", "-C", root, "merge-base", base, head],
                              capture_output=True, text=True, check=True).stdout.strip()
    records = subprocess.run(["git", "-C", root, "-c", "diff.renameLimit=0", "diff",
                              "--name-status", "-M", "-z", diff_range, "--", "*.lean"],
                             capture_output=True, text=True, check=True).stdout
    pairs = changed_paths(records)
    print("range                             : %s" % diff_range)
    print("its `-` side is read at           : %s" % (base or "(the index)"))
    print("`.lean` files it touches          : %5d" % len(pairs))
    print(WIDTH_LINE % (width, max_token))
    introduced = []
    for old_path, new_path in pairs:
        if new_path is None:
            continue
        after = subprocess.run(["git", "-C", root, "show", "%s:%s" % (head, new_path)],
                               capture_output=True, text=True)
        if after.returncode:
            continue
        was = set()
        if old_path is not None:
            before = subprocess.run(["git", "-C", root, "show", "%s:%s" % (base, old_path)],
                                    capture_output=True, text=True)
            if before.returncode == 0:
                for _, stranded in scan_text(before.stdout, width, max_token):
                    was |= {line.strip() for _, line in stranded}
        for paragraph, stranded in scan_text(after.stdout, width, max_token):
            fresh = [(n, l) for n, l in stranded if l.strip() not in was]
            if fresh:
                introduced.append((new_path, paragraph, fresh))
    print("FLAGGED: stranded lines this range introduces : %5d"
          % sum(len(s) for _, _, s in introduced))
    for path, paragraph, s in introduced:
        show(path, paragraph, s, width)
    print()
    print("A flag is a question, not a finding: re-fill the paragraph by the smallest window that")
    print("absorbs the line, or decline it by name.  Comparison is by the stranded line's *text*,")
    print("not its number, so a paragraph that merely moved down the file is not reported, and a")
    print("renamed one is compared against its own old path.")
    return 0


def selftest() -> int:
    """Pin both conjuncts, both exclusions, and this file's own docstring.  No build, no tree."""
    ok = fail = 0

    def check(label, got, want):
        nonlocal ok, fail
        if got == want:
            ok += 1
            print("ok    %s" % label)
        else:
            fail += 1
            print("FAIL  %s: got %r, wanted %r" % (label, got, want))

    def doc(*body):
        return "/-!\n" + "\n".join(body) + "\n-/\n"

    def numbers(text):
        return [n for p, s in scan_text(text, WIDTH, MAX_TOKEN) for n, _ in s]

    long_word = "a" * 96

    # --- the two real shapes, from issue 2139's diff ------------------------------------------
    check("a stranded word after a full line is reported (issue 2139's `no`)",
          numbers(doc("x" * 97, "no", "stated figure anywhere on the tree, and more besides.")),
          [3])
    check("a stranded pair at the end of a paragraph is reported",
          numbers(doc("y" * 80, "four imports")), [3])

    # --- the first conjunct alone is not enough, and this is issue 2154's `:1029` shape --------
    # A short plain line in a paragraph that refills to the same length.  That -- and not either
    # exclusion -- is what keeps `GeneralSeparatedBaseChange.lean`'s bare `and` out: see the
    # module docstring.  This fixture is what stands between a loosening and flagging it.
    sense_break = doc("z" * 95, "index pairs.")
    check("a short last line whose paragraph does not refill shorter is NOT reported"
          " (the `and`'s shape)", numbers(sense_break), [])
    check("... and that paragraph really does contain a short plain line, so only the refill"
          " conjunct is keeping it out", is_short_plain("index pairs."), True)

    # --- the second conjunct alone is not enough: a saved line with nothing short in it --------
    saves_but_long = doc("z" * 40, "w" * 40, "`" + "q" * 30 + "`")
    check("a paragraph that refills shorter but strands nothing short is NOT reported",
          numbers(saves_but_long), [])
    check("... and that paragraph really does refill shorter",
          len(refill([l for _, l in paragraphs(saves_but_long)[0]], WIDTH)) < 3, True)

    # --- exclusion 1: the successor is a single token that will not fit beside the line --------
    # Synthetic, and deliberately NOT issue 2154's `:1029` shape: this paragraph *does* refill
    # shorter, so it reaches the exclusion instead of stopping at the first conjunct.  Its one
    # instance on the tree is `AwayBaseChangeSeparated.lean:892`.
    unbreakable = doc("`" + long_word + "`", "and", "`" + long_word + "`",
                      "and the rest of it", "which continues here.")
    check("a short line whose successor is a single unfittable token is NOT reported",
          numbers(unbreakable), [])
    # Sightedness: the paragraph really does save a line, so the exclusion -- and not the first
    # conjunct -- is what keeps `and` out of the report.
    wedged = paragraphs(unbreakable)[0]
    check("... and the fixture is sighted: the refill does save a line there",
          len([l for _, l in wedged]) - len(refill([l for _, l in wedged], WIDTH)), 1)
    check("... and dropping the successor exclusion would report `and`",
          [n for i, (n, l) in enumerate(wedged) if i and is_short_plain(l)], [3])

    # --- exclusion 2: a paragraph's first line has nothing above it ----------------------------
    # Independent of exclusion 1, as its one tree instance is: at
    # `TateInvNodeChartQuotientSpf.lean:216` the successor fits beside the line and only this
    # exclusion applies.
    first_line = doc("This is", "`" + long_word + "`", "with a tail that shortens the refill.")
    check("a short FIRST line of a paragraph is NOT reported", numbers(first_line), [])
    check("... and the fixture is sighted: that line really is short and plain",
          is_short_plain("This is"), True)
    check("... and dropping the first-line exclusion would report it",
          [n for i, (n, l) in enumerate(paragraphs(first_line)[0]) if is_short_plain(l)], [2])

    # --- what must never be rewrapped ----------------------------------------------------------
    check("a list item is not filled prose",
          numbers(doc("x" * 97, "* no", "stated figure anywhere on the tree, and more besides.")),
          [])
    check("a table row is not filled prose",
          numbers(doc("| a | b |", "| - | - |", "| c | d |")), [])
    check("a heading is not filled prose", numbers(doc("## no", "x" * 97)), [])
    check("an indented line is not filled prose",
          numbers(doc("x" * 97, "  no", "stated figure anywhere on the tree, and more besides.")),
          [])
    check("a fenced block is not filled prose",
          numbers(doc("```", "x" * 97, "no", "```")), [])

    # --- emphasis at the start of a line IS filled prose ---------------------------------------
    # A list marker is a bullet *followed by a space*.  Requiring none also matched
    # `**a bold lead-in**`, `*an italic one*` and a continuation line opening `10.12's`, which
    # split the paragraph at them and ran the fill test on a fragment: 1104 misclassified lines on
    # this tree and 16 stranded lines the scan could not see.  No fixture had the shape, which is
    # why twelve green runs said nothing.  The first three below are the shape and each returns
    # `[]` under the rule that shipped first; the `1. `, `- ` and `>` cases return `[]` under both
    # and are regression guards on the tightening, not sightedness checks -- said here rather than
    # implied, because a fixture that cannot fail is worth only what its label claims.
    check("a `**bold**` lead-in is filled prose, so the paragraph is not broken at it",
          numbers(doc("**Bold lead-in.**  " + "x" * 78, "no",
                      "stated figure anywhere on the tree, and more besides.")), [3])
    check("an `*italic*` lead-in is filled prose too",
          numbers(doc("*italic* " + "x" * 88, "no",
                      "stated figure anywhere on the tree, and more besides.")), [3])
    check("a continuation line opening `10.12's` is prose, not a numbered item",
          numbers(doc("x" * 97, "10.12's",
                      "statement outright, and a tail that shortens the refill.")), [3])
    # Sightedness, as a pair that differs by exactly the space: the rule must reject one spelling
    # and accept the other, and these are the four leaders it decides between.
    check("... and `STRUCTURAL` does not match an emphasis-led line",
          [bool(STRUCTURAL.match(l)) for l in ("**Bold lead-in.**", "*italic* text", "10.12's")],
          [False, False, False])
    check("... while the same leaders followed by a space are still structure",
          [bool(STRUCTURAL.match(l)) for l in ("* item", "- item", "+ item", "1. item")],
          [True, True, True, True])
    check("a `1. ` numbered item is not filled prose",
          numbers(doc("x" * 97, "1. no", "stated figure anywhere on the tree, and more.")), [])
    check("a `- ` list item is not filled prose",
          numbers(doc("x" * 97, "- no", "stated figure anywhere on the tree, and more.")), [])
    check("a `> ` block quote is not filled prose, with or without the space",
          numbers(doc("x" * 97, ">no", "stated figure anywhere on the tree, and more.")), [])

    # --- the population -----------------------------------------------------------------------
    declaration = "/--\n" + "x" * 95 + "\none\nand a tail to make the refill shorter.\n-/\n"
    check("a declaration docstring is in scope, because two standing instances live in one",
          [n for p, s in scan_text(declaration, WIDTH, MAX_TOKEN) for n, _ in s], [3])
    check("a `--` comment is not scanned: it is not filled prose and is code-adjacent",
          numbers("-- " + "x" * 94 + "\n-- no\n-- stated figure anywhere, and more.\n"), [])
    check("a backticked word is not plain, however short",
          is_short_plain("`no`"), False)
    check("a long unbacked word is not plain either",
          is_short_plain("a" * 15), False)

    # --- the fill width ------------------------------------------------------------------------
    # The default is measured (see `## The fill width` in the docstring) and nothing else in here
    # would notice it moving back, so it is pinned by its value *and* by the behaviour it buys.
    check("the default fill width is this tree's, and it is 99", WIDTH, 99)

    # The 38-of-66 shape: prose that is a byte-exact greedy fill at 99, which the old default
    # flagged and this one does not.  Sighted from both sides -- `[]` alone would also be what a
    # broken predicate returns.
    filled_at_99 = doc("x" * 97, "ab")
    check("a paragraph correctly filled at 99 is NOT reported at the default",
          numbers(filled_at_99), [])
    check("... and it is sighted: the old default did report it", [n for p, s in
          scan_text(filled_at_99, 100, MAX_TOKEN) for n, _ in s], [3])
    check("... and the repair it asked for is a line of exactly 100 columns",
          cols("x" * 97 + " ab"), 100)

    # The one class the default loses, named in the docstring: a paragraph holding a line WIDER
    # than the fill width.  A greedy refill must re-break that line, spending the line the repair
    # would save, so `widows` cannot see the widow even though a window repair at 99 exists.
    over_width = doc("a" * 50 + " " + "b" * 49, "c" * 90, "no")
    check("a widow under a line wider than the fill width is missed at the default",
          numbers(over_width), [])
    check("... and it is a real miss, not an absent widow: `--width 100` reports it",
          [n for p, s in scan_text(over_width, 100, MAX_TOKEN) for n, _ in s], [4])
    check("... and the window that repairs it stays inside 99",
          [cols(l) for l in refill(["c" * 90, "no"], WIDTH)], [93])

    # Goal 4 of issue 2167: `--width` stays a flag and the width stays on the summary line of both
    # report paths, so a figure cannot be quoted without it.  One constant, used by both.
    check("the width is on the summary line, at the width actually used",
          WIDTH_LINE % (99, MAX_TOKEN),
          "fill width / max plain word       :    99 / 14")

    # --- the lexer ----------------------------------------------------------------------------
    check("a nested `/- ... -/` does not close the docstring early",
          doc_spans("/-!\n/- inner -/\ntail\n-/\n", "/-!"), [(1, 4)])
    check("`/--` and `/-!` are found separately",
          (doc_spans("/-- a -/\n/-!\nb\n-/\n", "/--"), doc_spans("/-- a -/\n/-!\nb\n-/\n", "/-!")),
          ([(1, 1)], [(2, 4)]))

    # --- what `--diff` reads: the two git shapes that broke it --------------------------------
    # A three-dot range's `-` side is the merge-base, not the left-hand spelling.  Reading it at
    # the spelling is what made a widow master had already repaired read as freshly introduced.
    check("`A...B` takes its base from the merge-base", range_ends("A...B"), ("A", "B", True))
    check("`A..B` takes its base from `A`", range_ends("A..B"), ("A", "B", False))
    check("`A...` is `A...HEAD` to git, so it is still a merge-base",
          range_ends("A..."), ("A", "HEAD", True))
    check("a bare `A` is `git diff A`, whose other end is read out of the index",
          range_ends("A"), ("A", "", False))

    # A diff names two paths and either may be absent; a rename's `-` side lives at the OLD one.
    check("a modification names the same path on both sides",
          changed_paths("M\0FormalSchemes/A.lean\0"),
          [("FormalSchemes/A.lean", "FormalSchemes/A.lean")])
    check("an addition has no old side", changed_paths("A\0FormalSchemes/A.lean\0"),
          [(None, "FormalSchemes/A.lean")])
    check("a deletion has no new side", changed_paths("D\0FormalSchemes/A.lean\0"),
          [("FormalSchemes/A.lean", None)])
    check("a rename keeps both paths, and the old one is where `git show <base>:` can find it",
          changed_paths("R100\0FormalSchemes/Old.lean\0FormalSchemes/New.lean\0"),
          [("FormalSchemes/Old.lean", "FormalSchemes/New.lean")])
    check("a rename whose similarity score is not 100 parses the same way",
          changed_paths("R087\0FormalSchemes/Old.lean\0FormalSchemes/New.lean\0"),
          [("FormalSchemes/Old.lean", "FormalSchemes/New.lean")])
    check("a rename in the middle of a diff does not swallow the record after it",
          changed_paths("M\0A.lean\0R100\0Old.lean\0New.lean\0M\0B.lean\0"),
          [("A.lean", "A.lean"), ("Old.lean", "New.lean"), ("B.lean", "B.lean")])

    # --- dogfooding: this script's own docstring ------------------------------------------------
    own = [n for p, s in
           [(p, widows(p)) for p in _paragraphs_of(__doc__.split("\n"), lambda _n: True)]
           for n, _ in s]
    check("this script's own module docstring strands nothing", own, [])

    print("\n%d ok / %d FAIL" % (ok, fail))
    return 1 if fail else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tree", action="store_true", help="the standing population")
    parser.add_argument("--diff", metavar="RANGE", help="stranded lines a `git diff` range adds")
    parser.add_argument("--root", default=".", help="tree to scan; may be an extraction")
    parser.add_argument("--width", type=int, default=WIDTH, help="the fill width this tree uses")
    parser.add_argument("--max-token", type=int, default=MAX_TOKEN,
                        help="longest word a line may hold and still count as plain")
    parser.add_argument("--selftest", action="store_true", help="needs no build and no tree")
    args = parser.parse_args()

    if args.selftest:
        return selftest()
    if args.diff:
        return report_diff(args.diff, args.root, args.width, args.max_token)
    if args.tree:
        return report_tree(args.root, args.width, args.max_token)
    parser.error("one of --tree, --diff or --selftest is required")


if __name__ == "__main__":
    sys.exit(main())
