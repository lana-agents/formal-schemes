#!/usr/bin/env python3
"""Flag a docstring paragraph a re-fill left ragged: a stranded word, or a stub in the middle.

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

**This file reports two species and they are separate populations.**  A *stranded line* -- a widow
-- is the shape above: a word or two left at a paragraph's end.  A *stub* is the commoner one,
filed as issue 2236 after #826 shipped a 58-column line in the middle of a thirty-one-line
paragraph: a re-fill that stops partway leaves a short line where it stopped, and
`is_short_plain`'s two-word cutoff cannot see it.  Both report paths print each species under its
own `FLAGGED:` line, `--diff` compares each against its own population at the base, and `## The
stub species` below is where the second one is derived and priced.

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
     561 paras  ... and **some suffix of it refills into fewer lines** -- still mostly
                sense-breaks that happen to be compressible, with nothing short stranded
     163 paras  ... and the paragraph holds a <=2-*plain*-word line -- close
    **161/165** ... and that line is not forced short by an unbreakable neighbour, and is
                not the paragraph's first -- **the predicate**

The two conjuncts do different jobs and neither works alone.  *Some suffix refills shorter* rules
out the thousands of paragraphs this tree breaks for sense at no cost in lines.  *Holds a short
plain line* rules out the several hundred whose only compressible line is a long backticked name
the author put on a line of its own on purpose -- **plain** means every word on it is
backtick-free and at most `--max-token` characters.

**The first conjunct is a suffix window and not the whole paragraph.**  Whole-paragraph was the
first spelling and it is blind in exactly one place: a paragraph holding a line *wider* than the
fill width fails it even when the tail is compressible, because the greedy fill has to re-break
the long line and spends the line the repair would save.  `start = 0` is the whole paragraph, so
the window is a strict generalisation and nothing that was reported stopped being.  What it buys,
on these 7863 paragraphs: **555 -> 561** past the first conjunct, **six** of them new, and **one**
flag -- `AwayBaseChangeChartTransition.lean`'s `would carry:`.  The other five hold no short plain
line at all, so the *second* conjunct rejects them unaided.  **+1 true positive, +0 false
positives**, and that tally is exact rather than sampled for the reason `## The fill width` gives.

## The fill width, and why it is 99

**A width is a claim about the convention of the text the scan reads, so it is checkable** -- and
the first default here was 100, argued for by the rejected row above and never checked against the
tree.  It is checked now, twice, over the 7863 paragraphs at `4873811`.  *Exact-fill* below counts
paragraphs that are **byte-identical** to a greedy fill at `w`, by a fill written from the
definition rather than by calling `refill`:

    w     exact-fill paragraphs (of 7863)   flagged paragraphs
    ---   -------------------------------   ------------------
     96                              2386                   88
     97                              3393                  102
     98                              4465                  121
    **99**                       **4874**              **161**
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
**65** paragraphs are flagged at 100 and not at 99, and **0** the other way round.  So the width
never traded one population for another -- widening it only ever added, and it added 29 % of its
own headline figure.  Of the 65:

* **38 are byte-identical to a greedy fill at 99** and **0** to a fill at 100 -- correctly filled
  prose by this tree's own practice, flagged for not being packed tighter.
* **not one of the 65 has a repair at 99 at all.**  Take the smallest window ending at the
  paragraph's end whose refill is shorter: at 99 there is none, and at 100 there is one whose
  longest line is **exactly 100 columns**, in every one of the 65.  **The old default's extra
  flags were requests to emit a 100-column line**, which is inside `CONTRIBUTING.md`'s limit and
  outside this tree's fill.  An instrument whose repair violates the convention it measures is
  asking a question with no admissible answer.

**The one flag a 99 default did lose, and how the window bought it back.**  The sixty-sixth was
`AwayBaseChangeChartTransition.lean:92`, which strands `would carry:` and *has* a 99-safe repair --
a four-line window refilling to three at 98 columns -- yet the *whole-paragraph* first conjunct
missed it at 99, because the paragraph holds a line of exactly **100** columns and a greedy 99-fill
must re-break it, spending the line the repair would save.  **That is the class: a paragraph
holding a line wider than the fill width.**  549 paragraphs here hold one and exactly **1** of them
became a missed widow.  That is why the list above reads 65 and not 66: the sixty-sixth is now
flagged at 99 as well as at 100, by the suffix window of the first conjunct.  **The class does not
go away; what changed is that the instrument can see into it** -- an over-width paragraph in which
no window saves a line is still not reported, and `--selftest` pins that negative beside the
positive, because otherwise *over-width* and *flagged* would be indistinguishable in the fixtures.

## The two exclusions, and the case an instrument must not flag

A short line can be short because **what follows it cannot fit beside it**, and a short line can be
the **first** of its paragraph, with nothing above it to be pulled onto.  Neither is a widow, so a
line is not reported in either case.

**Start with the tree's famous negative, and with the conjunct that actually excludes it.**  Issue
2154 named `GeneralSeparatedBaseChange.lean`'s bare `and` as a widow and it is not one -- and the
reason is the **first conjunct**, not either exclusion.  Its paragraph is thirteen lines and **not
one of its twelve suffix windows refills into fewer lines**, at 99 or at 100, so `widows` returns
at its opening conjunct and no exclusion is ever consulted.  That is exactly the reason issue 2159
gave, and the window spelling of that conjunct is the stronger form of it: *no* part of the
paragraph is compressible, not merely the whole of it.  An earlier version of this paragraph
credited the successor exclusion instead, understandably: the `and` *is* wedged between long
backticked names, `3 + 1 + 97` columns, so that test would fire too **if it were reached**.  **A
line can meet two rules and be excluded by only one of them, and the prose has to name the one
that runs first.**

**So the exclusions are justified on their own instances, and there are three of those.**
Measured at `90be36d`, over the 166 short-plain lines living in paragraphs some suffix of which
refills shorter:

    excluded by                                  lines  which
    -------------------------------------------  -----  -------------------------------------
    the next line is a single unfittable token       1  `AwayBaseChangeSeparated.lean:892`,
                                                        `discharged here:`
    the line is its paragraph's first                1  `TateInvNodeChartQuotientSpf.lean:216`,
                                                        `This is`
    both                                             1  `TateInvNodeChartDescent.lean:257`,
                                                        `This is`
    reported                                       163

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
a module-docstring-only population reads 86 paragraphs here and **contains neither**.

**The closing `-/` counts as one of the two words.**  A line *beginning* `-/` is structural and
is never rewrapped; a line *ending* ` -/` is ordinary filled prose whose last word happens to be
the delimiter.  Of the 163 lines reported at `90be36d`, **46** are of that shape -- `rest. -/`,
`injective. -/` -- so for 28 % of the population the predicate reads *one* prose word plus the
delimiter.  They are widows all the same, and a refill leaves the `-/` at the end where it was;
the figure is here so that anyone loosening `is_short_plain` knows how much of the population
turns on it.

**The gap to issue 2159's 136 / 139 is unexplained, and this file does not claim to explain it.**
The conjuncts are that row's and reproduce; the segmentation is what differs, and sweeping it at
`4873811` lands nowhere near that row's intermediate figures of 3193 and 493 either:

    segmentation                      refill differs   window saves   reported
    --------------------------------  --------------  -------------  ----------
    this file (`/-!` and `/--`)                 2989            561   161 / 165
    `/-!` only                                  1549            287    86 /  88
    `/--` only                                  1440            274    75 /  77
    structural-line rule dropped                6006           2549  1125 / 1192
    fenced-block rule dropped                   3001            565   161 / 165

The three ratios against 3193 / 493 / 136 are 0.94, 1.14 and 1.18 -- not constant, so it is not
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
population went 149 / 153 to 161 / 165 at `4873811` -- 12 stranded lines the scan could not see,
and not one spurious.  *A structural-line rule must require the space that makes a list marker*;
the shape that hid this is that no fixture and none of the pinned `--diff` ranges contained an
emphasis-led line, so twelve green runs said nothing.

**This is not an autoformatter.**  It reports a line and the refill that would absorb it; it never
rewrites a file.  Repairing a widow is a judgement about the smallest window that removes it --
issue 2154's two repairs are two lines into one and four into three -- and a full greedy refill
of a paragraph routinely destroys breaks the author chose.

**And the window it prints is the smallest one that absorbs the stranded line, which it did not
used to be.**  `show` printed the *whole-paragraph* refill while both footers told the reader to
re-fill by the smallest window that absorbs the line -- so for any paragraph whose compressible
part was a proper suffix, the report named a repair its own footer forbids.  At `f8a2b41`, of the
**159** flags on `--tree` at 99, **110** -- 69 % -- get a window shorter than the whole paragraph,
and at `--width 100` it is **171** of 226.

**The report's window is not the first conjunct's window, and that distinction is the whole of
`repair_window`'s `covering` argument.**  The conjunct asks *is any suffix compressible*, and
takes the smallest such suffix wherever it is; the report asks *what is the smallest window that
absorbs this line*, and must start its search at the line.  The two differ whenever the smallest
compressible suffix begins **below** the flagged line, and on this tree that is **3** of the 159
at 99 and **3** of the 226 at 100 -- `GlueHomToSpf.lean:519`, `LocallyRingedSpaceRange.lean:43`
and `SpfGammaBase.lean:39`, the worst of them a two-line window thirteen lines under its widow.
Printing the conjunct's answer there names a repair that provably cannot remove the line it is
printed under: apply it and the flag comes back.  *A repair is named by the line it has to
absorb, not by where the saving happens to be.*

**What the printed window does not promise.**  It removes the line it is printed against -- all
159 of them at 99 and all 226 at 100, checked by applying each one and re-running the predicate --
but a greedy refill can strand a *different* word, and in **1** of the 159 at 99
(`SpfGammaBase.lean:39`) and **1** of the 226 at 100 (`GeneralFibreProductBaseChange.lean:297`) it
does.  The whole-paragraph refill leaves none, which is not an argument for printing it: it is the
repair both footers forbid, because it destroys breaks the author chose.  A flag is a question and
so is its successor -- widen the window, or decline it by name.  **Naming the smallest window that
strands nothing is a second predicate**; this one names the smallest window that absorbs the line,
and the two paragraphs below are that second predicate measured (issue 2185) rather than the row
they used to promise.

**So the scan is not a fixed point, and this is the whole of how far from one it is.**  Follow the
printed window on `SpfGammaBase.lean:39` at 99 -- `--tree` prints `paragraph of 11 lines; 9 of them
refill to 7` under `:41 'This'` and `:44 'weaker.'` -- and it flags the paragraph again, at
`:47 'general fact.'`, a refilled last line of 13 columns.  At 100 on
`GeneralFibreProductBaseChange.lean:297` the same: `:309 '(issue 1998).'` before,
`:312 'imported again.'` after, 15 columns.  Each of those is one width of a sweep at `746718d`
over 583 modules and 7920 in-scope paragraphs at every width from 60 to 140 -- **26 328**
flag-instances, the total the `no window` census below reads at `d3a75ae` over 7918 paragraphs --
in which the printed repair strands a word **88** times, in **13** distinct paragraphs.  Rare, and
not absent; and what it leaves is a flag like any other, to be widened or declined by name.

**And the count is 88 and not 97, because a refill that pushes a bare `-/` onto a line of its own
has stranded the delimiter and not a word.**  Run the sweep on `lines[:start] + filled` as a list,
which is the obvious way to do it and the wrong one, and it reads **97** in **14** paragraphs.  The
nine extra instances are three paragraphs at the top of their bands -- `GeneralDiagonal.lean:74` at
130..132, `GeneralFibreProductBaseChange.lean:1548` at 117..119 and `TateInvOverlapBand.lean:373`
at 127..129 -- and in every one the new short line is `-/` alone.  Write the refill back into the
file and re-segment it, which is what this scan reads, and `STRUCTURAL`'s `^-/` alternative takes
that line out of the paragraph before `widows` is reached: the rule this section states above,
applied to the repair rather than to the original.  A line *ending* ` -/` is filled prose whose
last word is the delimiter -- 28 % of the standing population is that shape -- so `branch. -/`,
`docstring. -/` and `statement. -/` stay, their bands merely shortened, and only
`GeneralDiagonal.lean:74` leaves the thirteen outright.  Measured end to end rather than argued:
applying its window at 130 takes `--tree` from 656 flagged paragraphs to 655 and takes the
paragraph out of the report, while applying `SpfGammaBase.lean:39`'s at 99 leaves 159 and puts that
paragraph back into it.  The 88 are a subset of the 97, with no instance the other way about.

**The `no window` branch is real, and a fixture drives it.**  Nothing makes a covering window
necessary -- a flag needs only *some* suffix to compress, and the lines above the widow may spend
the saving the way an over-width line does -- so `show` says so rather than falling back to a
window that misses.  **In the five-line witness `--selftest` uses**, the line below the widow
opens with a 98-column word, so `cols("no") + 1 + 98 > 99` and the widow cannot join it; that line
is over-width, and what is left of it after the split is itself 98 columns, so the split spends
exactly the line the tail's repair would have saved and every suffix reaching up to the widow
breaks even.  **That is an account of one paragraph, not a test.**  The branch fires exactly when
no suffix containing the stranded line refills shorter, and there is no more local reading of it:
a long first word below the widow is neither sufficient nor necessary.  Shortening only the
**second** word below, in that same witness, leaves that condition holding and produces a covering
window, because what decides the tail is the remainder *after* the split; and a paragraph whose
every line opens with a word of at most 14 columns reaches the branch when the long word sits in
the **middle** of the line below.  Both synthetic searches run for issue 2173 came back empty and
the witness was built by hand.  `--selftest` pins the branch **through the report** (issue 2176)
on the witness, and pins three neighbours beside it: a companion that shortens the first word
below and so gets a window, one that shortens the second word instead and gets one too, and one
whose every line opens with a short word and that reaches the branch anyway.  The two
`repair_window`-level checks stay.

**On this tree the branch never fires.**  At `d3a75ae`, over 583 modules and 7918 in-scope
paragraphs at **every** width from 60 to 140 -- **26 328** flag-instances in all -- the count
with no covering window is **0**; the **0** of the 159 at 99 and **0** of the 226 at 100 are that
sweep read at two widths.  It is a near miss rather than a fantasy: the longest single word in an
in-scope paragraph line here is **98** columns (`TateInvQuotientNodeLocusChart.lean:239`, a
backticked declaration name plus `'s`), which is already long enough to block a one-column widow
at 99.  The arrangement is missing, not the vocabulary, and that is why the branch is a branch
rather than an assertion.

## The stub species, and the diagnosis issue 2236 filed that turned out to be wrong

**A widow is a word or two left at a paragraph's *end*.  A stub is a short line in its *middle*,
left where a re-fill stopped** -- a clause is inserted, a numeral widens, the author repairs the
line they touched and the fill below it is never redone.  Issue 2236 filed that species, and it
filed a diagnosis with it: that `widows` applies `is_short_plain` to *the paragraph's last line*.
**It does not**, and re-reading the loop is how that was settled: it runs over every line of the
paragraph, excludes the first, and excludes a line whose successor is a single unfittable token.  A
mid-paragraph short line has been in scope since that loop was written.

**So the blindness is `is_short_plain`'s *two-word* cutoff and nothing positional**, and #826 is
the witness that settles it.  At `3a724e0` the paragraph at `:404` runs thirty-one lines and holds
three lines a fill would not have left -- `:415` at 95 columns, `:424` at 58 and `:427` at 35.  Its
**first** conjunct passes: the suffix from `:427` refills eleven lines into ten.  Yet `widows`
returns `[]`, because `:424` carries **eleven** words and `:427` carries **eight**, so
`is_short_plain` rejects both, and the exclusions are never consulted.  `--diff e9679d6..3a724e0`
reported **0** stranded lines over a paragraph with two stubs in it, and that is the regression
this species exists for.

**A threshold in columns is the obvious rule and it is the wrong one**, for the reason that row
gives: a short mid-paragraph line is sometimes *forced* and sometimes correct, and a width cannot
tell those from the third case.  The rule here is the counterfactual instead -- *would a greedy
re-fill put a different unit on this line* -- and its three conjuncts are `stubs`'.  Each was
measured over the 8124 in-scope paragraphs at `7781393` rather than argued, and a pull request that
adds a module moves all of these, so re-measure rather than quoting them.

    conjunct, each adding to the one above                                     lines   paragraphs
    -------------------------------------------------------------------------  -----   ----------
    a non-first non-last line some window containing it refills shorter, with
      the next *word* fitting on it -- the counterfactual, at `refill`'s own
      whitespace tokenisation                                                     815          480
    ... with the next **atom** fitting instead: a backticked span and a short
      bolded figure are single units                                              685          426
    ... and the atoms that would move up are **plain**, `is_short_plain`'s own
      word -- backtick-free and at most `--max-token` characters                   345          230
    **... and at least `--min-atoms` of them fit**                              **81**       **72**

**The atom rule is derived from the tree, not invented.**  Over the 35413 in-scope paragraph lines
here, **118** carry an odd number of `` ` `` marks -- 0.33 %, so a backticked span crosses a break,
rarely.  A **short bolded figure** crosses one **0** times out of **329**.  So neither is a law and
the first is not even close to one: `splits_an_atom` exists because the 118 are real, and it
returns a line to the population it belongs in rather than pretending the break is impossible.  The
16-character bound in `FILL_ATOM`, and the digit-and-at-most-three-words test in `atoms`, are what
keep a bolded *sentence* -- 995 lines carry an odd number of `**` -- from being read as an
unbreakable unit; without them #826's own `:427` is invisible, because the bolded sentence
beginning on the line below it becomes a 97-column atom that cannot fit anywhere.

**The plain conjunct is what keeps the tree's commonest deliberate break out**, and it is the
single largest of the four steps: 685 to 345.  The break is *before a long backticked name* --
`RefinedOverlapTransition.lean:193` is 47 columns and the line under it opens with a 47-column
declaration name -- and it is the habit `## The predicate` already records under *authors break
before long backticked names*.  Counting past the name would flag every one of them, so the count
stops at the first atom that is not plain.

**And `--min-atoms` is 2 because the curve says so, not because two is a nice number.**  345 at
one, **81** at two, 59 at three, 43 at four: a factor of **4.3** at the first step and **1.4**,
**1.4** after it.  That is a knee.  The reading behind the shape is that a line short by exactly
one atom differs from the greedy fill by a *single* decision, which is what a break taken for sense
looks like; `RefinedOverlapTransition.lean:415`, 95 columns with one three-letter word fitting
beside it, is that case and is correctly not reported.

**What it costs on `--diff`, which is the mode that earns it.**  Over the last **60** commits on
`master` at `7781393`, the species reports **16** introduced lines in **6** commits, against the
widow species' **4** in the same range -- and the largest single commit is **4**.  The standing
`--tree` population is **81** lines in 72 paragraphs against the widow species' 163 in 159, of
which **16** lines are both.  Nothing in `refill`, `widows`, `is_short_plain` or `STRUCTURAL`
moves: the `--tree` report is **additive**, 158 lines added and 0 removed, and `--selftest` keeps
its exit code and every case it had.

**The one migration this row priced and declined.**  Reading `widows`' own successor exclusion at
atoms rather than at words -- which is arguably what it always meant -- moves that species by **33
lost and 3 gained** out of 163.  That is a change to a documented standing population with its own
fixtures and its own line in `CONTRIBUTING.md`, it is not what issue 2236 asked for, and the two
questions are genuinely different: a widow asks *is a word stranded*, where the rest of the line is
empty and the unit below hardly matters; a stub asks *would a re-fill put something here*, which is
a question about units.  So `refill` is untouched and `atoms` is the stub species' alone.  **The
33/3 is the price of doing it later**, and it is here so that the next row does not have to
re-derive it.

**The judgement issue 2236 asked for out loud: the missing blank line is declined, and here is
where it belongs.**  #826's second defect was a paragraph break that was never written, so `**Four
of the 47 ...**`  renders as a continuation and `file has seen, and it is not close.`  sits
mid-paragraph rather than at a paragraph's end.  **Its consequence is caught here** -- that line is
`:427` and it is a stub by this rule, with no special case for it -- but the *cause* is not this
scan's business.  Inferring an intended paragraph break means deciding that a bolded lead-in opens
a paragraph, and `## Where the population comes from` is the record of what happened the last time
a rule guessed at emphasis: 1104 misclassified lines.  A scan that starts inferring paragraph
breaks can be wrong about prose in a way a fill scan cannot.  It belongs with a Markdown-structure
check over the whole docstring -- the natural home is a mode of `scripts/outward_prose_scan.py`,
which already walks prose rather than fills -- and it is worth a row of its own.  **Declined here,
named there, and the stranded line it causes is reported all the same.**

**What a stub report is not.**  Like a widow it is a question: the window printed against it is the
smallest one that *absorbs* the line, which is not always the one an author would try first -- when
the stub and everything under it refill to the same count, the window starts *above* the stub, and
`--selftest` pins that branch through the report.  And it is not always the repair to make: at
#826's `:404` the printed window removes both stubs and strands nothing, but what it leaves is one
paragraph where the author meant two, and the blank line is the better fix.  Widen it, decline it
by name, or repair the structure instead.
"""

from __future__ import annotations

import argparse
import glob
import io
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

# The stub species' own parameter, on the same footing and for the same reason: a stub count is
# meaningless without it, so both report paths print it beside the width.
ATOMS_LINE = "plain atoms a stub must fit       : %5d"

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

# The spans a fill may not break, for the **stub** species only: a backticked span and a bolded
# figure.  Both are measured over this tree's own in-scope paragraphs rather than asserted -- 118
# lines of 35413 split a `` ` ``-span, **0** of 329 short bolded figures split -- and the bound of
# 16 characters plus the digit-and-at-most-three-words test in `atoms` is what keeps a bolded
# *sentence* from being read as an unbreakable unit.  `refill` is untouched and still splits on
# whitespace, so the widow species' population does not move; see `## The stub species`.
FILL_ATOM = re.compile(r"``[^`]*``|`[^`]*`|\*\*[^*]{1,16}\*\*")

# Plain atoms that must fit before a short mid-paragraph line is a stub.  **Two, and it is
# measured**: at one the tree reads 345 lines and at two it reads 81, a factor of 4.3, while
# every step after that is a factor of 1.4 -- so two is a knee and not a point on a slope.  The
# reading behind the shape is that a line short by exactly one atom differs from the greedy fill
# by a single decision, which is what a break taken for sense looks like.
MIN_ATOMS = 2


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


def repair_window(lines: list[str], width: int,
                  covering: int | None = None) -> tuple[int, list[str]] | None:
    """The **smallest** suffix of `lines` that refills shorter, as `(first index, its refill)`.

    `covering` is the highest index the window must hold, and it is the difference between the two
    questions this function answers.  `None` asks the **first conjunct's** question -- *is any
    suffix compressible at all* -- and `start = 0` is the whole paragraph, which is what that
    conjunct used to require.  An index asks **`show`'s** question -- *what is the smallest window
    that absorbs this line* -- and starts the search at that line, so every window it tries holds
    it.  `None` when no window qualifies.

    **The two are not the same window**, and conflating them was a defect: the smallest suffix
    that *saves a line* need not hold the line that was flagged, and on this tree there are three
    paragraphs where it does not.  The module docstring names them.  *A repair is named by the
    line it has to absorb, not by where the saving happens to be.*
    """
    top = len(lines) - 2 if covering is None else min(covering, len(lines) - 2)
    for start in range(top, -1, -1):
        filled = refill(lines[start:], width)
        if len(lines[start:]) - len(filled) >= 1:
            return start, filled
    return None


def widows(paragraph: list[tuple[int, str]], width: int = WIDTH,
           max_token: int = MAX_TOKEN) -> list[tuple[int, str]]:
    """The stranded lines of `paragraph`, or `[]` if there are none.

    Both conjuncts, then the two exclusions.  See the module docstring for what each rules out and
    what breaks if it is dropped.

    **The first conjunct asks whether some suffix refills shorter, not whether the whole paragraph
    does.**  A paragraph holding a line wider than `width` fails the whole-paragraph test even when
    its tail is compressible, because the greedy fill has to re-break that line and spends the line
    the repair would save.  `start = 0` is the whole-paragraph test, so this is a strict
    generalisation of it: nothing that was reported stops being reported.
    """
    lines = [line for _, line in paragraph]
    if repair_window(lines, width) is None:
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


def atoms(text: str) -> list[str]:
    """`text` split into the units a fill may not break: words, except that a backticked span
    and a short bolded figure are single atoms even when they hold spaces.

    `refill` splits on whitespace, which is right for the *widow* species and wrong for this one:
    the question a stub asks is *would a re-fill put a different unit here*, and answering it with
    a unit this tree's authors never split gives the wrong answer at every break taken to keep a
    name whole.  Both exceptions are measured over the in-scope paragraphs rather than chosen --
    see `## The stub species` in the module docstring -- and neither is a claim that the tree
    *cannot* split them: `` ` ``-spans cross a break on 118 of 35413 lines, and a short bolded
    figure on **0** of 329.
    """
    guards = []
    for span in FILL_ATOM.finditer(text):
        body = span.group(0)
        if " " not in body:
            continue                                  # already one whitespace word
        if body.startswith("*"):
            inner = body[2:-2]
            if not any(c.isdigit() for c in inner) or len(inner.split()) > 3:
                continue                              # a bolded sentence, not a figure
        guards.append((span.start(), span.end()))
    out: list[str] = []
    current = ""
    index = guard = 0
    while index < len(text):
        while guard < len(guards) and guards[guard][0] < index:
            guard += 1
        if guard < len(guards) and index == guards[guard][0]:
            current += text[guards[guard][0]:guards[guard][1]]
            index = guards[guard][1]
            guard += 1
            continue
        if text[index].isspace():
            if current:
                out.append(current)
                current = ""
        else:
            current += text[index]
        index += 1
    if current:
        out.append(current)
    return out


def splits_an_atom(lines: list[str], index: int) -> bool:
    """Whether the break after `lines[index]` falls **inside** an atom.

    Counted rather than reconstructed: joining the two lines merges the two halves into one atom,
    so the join holds fewer atoms than the parts do.  The 118 lines that do this are not stubs by
    any reading -- the author put the break there deliberately or the span is longer than the
    width -- and the count is the cheapest test that says so.
    """
    return (len(atoms(lines[index])) + len(atoms(lines[index + 1]))
            != len(atoms(lines[index] + " " + lines[index + 1])))


def plain_atoms_fitting(lines: list[str], index: int, width: int, max_token: int) -> int:
    """How many **plain** atoms from below would fit on `lines[index]`, stopping at the first
    that is not plain.  `-1` when the break after the line already splits an atom.

    *Plain* is `is_short_plain`'s own vocabulary -- backtick-free and at most `max_token`
    characters -- reused rather than re-invented, because the two species are asking the same
    question about the same text and a second spelling of *plain* would be a second thing to keep
    true.  Stopping at the first non-plain atom is what keeps this off the break a reader can see
    the reason for: an author who starts a line with a 47-column declaration name has explained the
    short line above it, and counting past that name would flag every one of them.
    """
    if splits_an_atom(lines, index):
        return -1
    room = cols(lines[index])
    count = 0
    for atom in atoms(" ".join(lines[index + 1:])):
        room += 1 + cols(atom)
        if room > width:
            break
        if "`" in atom or len(atom) > max_token:
            return count
        count += 1
    return count


def stubs(paragraph: list[tuple[int, str]], width: int = WIDTH, max_token: int = MAX_TOKEN,
          min_atoms: int = MIN_ATOMS) -> list[tuple[int, str]]:
    """The **mid-paragraph stubs** of `paragraph`: lines the fill was abandoned at.

    A widow is a line *at the end* of a paragraph with a word or two left on it.  A stub is the
    other shape, and the commoner one: a short line in the **middle** of a paragraph, left behind
    because an edit re-filled around it and stopped.  Nothing above reads it -- `widows` cannot,
    because a stub carries more than two words as often as not, and `--tree` at any width cannot,
    because the line is short rather than long.

    Three conjuncts, each measured in `## The stub species`:

    * the line is neither the paragraph's **first** nor its **last**.  A short first line has
      nothing above it to be pulled onto; a short last line is a widow and is the other species'
      to report, so the two populations are disjoint by construction except where a line is both;
    * at least `min_atoms` **plain** atoms from below would fit on it.  One is the counterfactual
      -- *a greedy re-fill puts a different unit here* -- and `min_atoms` above one is what keeps
      a deliberate break out, since a break taken one atom early is a single fill decision and is
      what a sense-break looks like;
    * some window **containing** the line refills shorter, so the flag arrives with a repair that
      can absorb it.  This is `repair_window`'s `covering` question, the same one `show` asks.
    """
    lines = [line for _, line in paragraph]
    out = []
    for index in range(1, len(lines) - 1):
        if plain_atoms_fitting(lines, index, width, max_token) < min_atoms:
            continue
        if repair_window(lines, width, index) is None:
            continue
        out.append(paragraph[index])
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


def scan_text_stubs(text: str, width: int, max_token: int, min_atoms: int = MIN_ATOMS):
    found = []
    for paragraph in paragraphs(text):
        stubbed = stubs(paragraph, width, max_token, min_atoms)
        if stubbed:
            found.append((paragraph, stubbed))
    return found


def species_scans(width: int, max_token: int, min_atoms: int):
    """`(label, scan)` for each species, in report order and with their parameters bound.

    One list, used by both report paths, so a species cannot be counted on one end of a `--diff`
    and compared against the other's population at the other end -- which is the shape of mistake
    that makes a flag look pre-existing when it is new.
    """
    return [("stranded lines", lambda t: scan_text(t, width, max_token)),
            ("mid-paragraph stubs", lambda t: scan_text_stubs(t, width, max_token, min_atoms))]


def scan_tree(root: str, species):
    """`species` is `scan_text` or `scan_text_stubs` with its parameters already bound."""
    out = []
    for path in lean_files(root):
        with open(os.path.join(root, path), encoding="utf-8") as handle:
            text = handle.read()
        for paragraph, flagged in species(text):
            out.append((path, paragraph, flagged))
    return out


def show(path: str, paragraph, stranded, width: int) -> None:
    lines = [line for _, line in paragraph]
    flagged = {number for number, _ in stranded}
    first = min(index for index, (number, _) in enumerate(paragraph) if number in flagged)
    window = repair_window(lines, width, first)
    if window is None:
        print("  %s:%d  paragraph of %d lines; no window holding the stranded line refills shorter"
              % (path, paragraph[0][0], len(lines)))
    else:
        start, filled = window
        print("  %s:%d  paragraph of %d lines; %d of them refill to %d"
              % (path, paragraph[0][0], len(lines), len(lines) - start, len(filled)))
    for number, line in stranded:
        print("      :%d  %r" % (number, line.strip()))


def list_hits(hits, width: int) -> None:
    """Every flagged paragraph of one species, under the count line that announced it.

    One listing for both species and both report paths, so a count and the paragraphs under it
    cannot come from different places -- a report that prints `81` over an empty list is the
    failure this shares out rather than repeats.
    """
    for path, paragraph, flagged in hits:
        show(path, paragraph, flagged, width)


def report_tree(root: str, width: int, max_token: int, min_atoms: int = MIN_ATOMS) -> int:
    hits = scan_tree(root, lambda t: scan_text(t, width, max_token))
    stubbed = scan_tree(root, lambda t: scan_text_stubs(t, width, max_token, min_atoms))
    modules = len(lean_files(root))
    stranded = sum(len(s) for _, _, s in hits)
    print("modules under FormalSchemes/      : %5d" % modules)
    print(WIDTH_LINE % (width, max_token))
    print(ATOMS_LINE % min_atoms)
    print("FLAGGED: paragraphs with a stranded line : %5d   (%d lines)" % (len(hits), stranded))
    list_hits(hits, width)
    print("FLAGGED: paragraphs with a mid-paragraph stub : %5d   (%d lines)"
          % (len(stubbed), sum(len(s) for _, _, s in stubbed)))
    list_hits(stubbed, width)
    print()
    print("A flag is a question, not a finding: re-fill the paragraph by the smallest window that")
    print("absorbs the line, or decline it by name with a reason.  This scan has no verdict or")
    print("exit code of its own -- the standing population is a wart with precedent (issue 2159),")
    print("and `--diff` is the mode that keeps it from growing.")
    print("A *stranded line* is a widow -- a word or two left at a paragraph's end.  A *stub* is")
    print("the other shape: a short line in the middle of a paragraph, left where a re-fill")
    print("stopped.  The two are separate populations and the second one is read here first.")
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


def report_diff(diff_range: str, root: str, width: int, max_token: int,
                min_atoms: int = MIN_ATOMS) -> int:
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
    print(ATOMS_LINE % min_atoms)
    species = species_scans(width, max_token, min_atoms)
    introduced = {label: [] for label, _ in species}
    for old_path, new_path in pairs:
        if new_path is None:
            continue
        after = subprocess.run(["git", "-C", root, "show", "%s:%s" % (head, new_path)],
                               capture_output=True, text=True)
        if after.returncode:
            continue
        before = None
        if old_path is not None:
            got = subprocess.run(["git", "-C", root, "show", "%s:%s" % (base, old_path)],
                                 capture_output=True, text=True)
            before = got.stdout if got.returncode == 0 else None
        for label, scan in species:
            was = set()
            if before is not None:
                for _, flagged in scan(before):
                    was |= {line.strip() for _, line in flagged}
            for paragraph, flagged in scan(after.stdout):
                fresh = [(n, l) for n, l in flagged if l.strip() not in was]
                if fresh:
                    introduced[label].append((new_path, paragraph, fresh))
    for label, _ in species:
        print("FLAGGED: %s this range introduces : %5d"
              % (label, sum(len(s) for _, _, s in introduced[label])))
        list_hits(introduced[label], width)
    print()
    print("A flag is a question, not a finding: re-fill the paragraph by the smallest window that")
    print("absorbs the line, or decline it by name.  Comparison is by the stranded line's *text*,")
    print("not its number, so a paragraph that merely moved down the file is not reported, and a")
    print("renamed one is compared against its own old path.")
    print("A *stranded line* is a widow at a paragraph's end; a *stub* is a short line in its")
    print("middle.  Each species is compared against its own population at the base.")
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

    def summary(text, path):
        """`show`'s own first line for `text`, so a fixture can pin the **report** and not only
        the function behind it.  Captures rather than refactors `show`, because what is being
        pinned is the line a reader sees."""
        held, sys.stdout = sys.stdout, io.StringIO()
        try:
            for paragraph, stranded in scan_text(text, WIDTH, MAX_TOKEN):
                show(path, paragraph, stranded, WIDTH)
            return sys.stdout.getvalue().splitlines()[0]
        finally:
            sys.stdout = held

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

    # The 38-of-65 shape: prose that is a byte-exact greedy fill at 99, which the old default
    # flagged and this one does not.  Sighted from both sides -- `[]` alone would also be what a
    # broken predicate returns.
    filled_at_99 = doc("x" * 97, "ab")
    check("a paragraph correctly filled at 99 is NOT reported at the default",
          numbers(filled_at_99), [])
    check("... and it is sighted: the old default did report it", [n for p, s in
          scan_text(filled_at_99, 100, MAX_TOKEN) for n, _ in s], [3])
    check("... and the repair it asked for is a line of exactly 100 columns",
          cols("x" * 97 + " ab"), 100)

    # --- the first conjunct is a window, not the whole paragraph -------------------------------
    # A paragraph holding a line WIDER than the fill width: a greedy refill of the whole must
    # re-break that line, spending the line the repair would save, so the whole-paragraph test
    # cannot see the widow even though a window repair at 99 exists.  This fixture shipped
    # *inverted*, pinning the miss; `AwayBaseChangeChartTransition.lean`'s `would carry:` is the
    # one instance on this tree and it is this shape.
    over_width = doc("a" * 50 + " " + "b" * 49, "c" * 90, "no")
    check("a widow under a line wider than the fill width IS reported, by the window",
          numbers(over_width), [4])
    check("... and the WHOLE paragraph saves nothing, so only the window finds it",
          len(paragraphs(over_width)[0])
          - len(refill([l for _, l in paragraphs(over_width)[0]], WIDTH)), 0)
    check("... and the smallest window is the last two lines",
          repair_window([l for _, l in paragraphs(over_width)[0]], WIDTH)[0], 1)
    check("... and `repair_window` is `None` exactly when the first conjunct fails",
          repair_window([l for _, l in paragraphs(sense_break)[0]], WIDTH), None)
    check("... and the window that repairs it stays inside 99",
          [cols(l) for l in refill(["c" * 90, "no"], WIDTH)], [93])
    check("... and `--width 100` reported it before the window did, which is how the class"
          " was found", [n for p, s in scan_text(over_width, 100, MAX_TOKEN) for n, _ in s], [4])

    # The window does not flag a paragraph merely for holding an over-width line.  Same first
    # line, same short plain last line, but nothing below the over-width line compresses -- so no
    # window saves a line and the first conjunct still returns.  Without this, "over-width" and
    # "flagged" would be indistinguishable in the fixtures.
    over_width_tight = doc("a" * 50 + " " + "b" * 49, "c" * 97, "no")
    check("an over-width paragraph in which NO window saves a line is NOT reported",
          numbers(over_width_tight), [])
    check("... and it is sighted: it really does hold a line wider than the fill width",
          max(cols(l) for _, l in paragraphs(over_width_tight)[0]) > WIDTH, True)
    check("... and it really does hold a short plain line, so only the first conjunct keeps"
          " it out", [l for _, l in paragraphs(over_width_tight)[0] if is_short_plain(l)], ["no"])

    # `start = 0` is the whole-paragraph test, so the change is a strict generalisation: the
    # `and`'s shape above still has no window at all, at either width.
    sense_lines = [l for _, l in paragraphs(sense_break)[0]]
    check("the `and`'s shape has no window that saves a line, at 99 or at 100",
          [any(len(sense_lines[k:]) - len(refill(sense_lines[k:], w)) >= 1
               for k in range(len(sense_lines) - 1)) for w in (99, 100)], [False, False])

    # `show` prints the window, not the whole-paragraph refill, because the whole-paragraph refill
    # is the repair the footer of both report paths tells the reader NOT to make.
    check("the reported repair is the smallest window and not the whole paragraph",
          repair_window([l for _, l in paragraphs(
              doc("x" * 97, "no", "stated figure anywhere on the tree, and more besides."))[0]],
              WIDTH)[0], 1)

    # ... but the smallest window that SAVES a line need not be one that HOLDS the flagged line,
    # and the report has to name the second.  Here the last two lines refill into one on their
    # own, so the conjunct's answer is `start = 2` -- which is below the widow at index 1 and
    # cannot remove it.  This is `LocallyRingedSpaceRange.lean:43`'s shape, where the conjunct's
    # window was thirteen lines under the line it was printed against.
    window_below = doc("x" * 97, "no", "c" * 60, "more words here")
    below_lines = [l for _, l in paragraphs(window_below)[0]]
    check("a widow whose paragraph's smallest saving suffix is BELOW it is still reported",
          numbers(window_below), [3])
    check("... and that saving suffix really does miss the widow, so the fixture is sighted",
          repair_window(below_lines, WIDTH)[0], 2)
    check("... while the window the report prints starts at the widow and absorbs it",
          repair_window(below_lines, WIDTH, 1)[0], 1)
    check("... and it is still a proper suffix, not a retreat to the whole paragraph",
          (len(below_lines), len(repair_window(below_lines, WIDTH, 1)[1])), (4, 1))

    # `covering` can rule out every window while the conjunct's question still has an answer --
    # which is the `no window` branch of `show`.  `over_width` above is the cheapest witness: no
    # window holding its FIRST line saves anything, because that line is the over-width one.
    over_lines = [l for _, l in paragraphs(over_width)[0]]
    check("`repair_window` is `None` when no window holding the given line refills shorter",
          repair_window(over_lines, WIDTH, 0), None)
    check("... while the unconstrained question on the same paragraph still answers",
          repair_window(over_lines, WIDTH)[0], 1)

    # ... and the branch is reached by a real flag, so the report line itself is pinned and not
    # just the condition behind it (issue 2176).  The widow here is `no` at index 1; the line
    # below it opens with a 98-column word, so `cols("no") + 1 + 98 > 99` and the widow cannot
    # join it.  That line is over-width, so it splits -- and what the split leaves is another 98
    # columns, which cannot take `c * 60` either, so the split spends exactly the line the tail's
    # repair would have saved: every suffix from index 0, 1 or 2 breaks even, and the only saving
    # suffix (index 3) is below the widow.  **That is a reading of this paragraph and not a rule**;
    # the two checks after the companion are the ones that say why it is not one.
    no_window = doc("x" * 99, "no", "y" * 98 + " " + "z" * 98, "c" * 60, "dd ee")
    check("the report says so when no window holding the stranded line refills shorter",
          summary(no_window, "FormalSchemes/NoWindow.lean"),
          "  FormalSchemes/NoWindow.lean:2  paragraph of 5 lines;"
          " no window holding the stranded line refills shorter")
    check("... and it is a real flag: the paragraph is reported, so `show` is reached",
          numbers(no_window), [3, 6])

    # Its sightedness companion.  Shorten **only** the first word below the widow -- the line
    # stays over-width -- and a covering window appears, so the fixture above cannot be passing
    # because of the over-width line or because the paragraph is unflagged.
    covered = doc("x" * 99, "no", "y" * 40 + " " + "z" * 98, "c" * 60, "dd ee")
    check("... and shortening only the first word below the widow gives it a window",
          summary(covered, "FormalSchemes/Covered.lean"),
          "  FormalSchemes/Covered.lean:2  paragraph of 5 lines; 4 of them refill to 3")
    check("... on the same flags, and with the line below the widow still over-width",
          (numbers(covered), max(cols(l) for _, l in paragraphs(covered)[0]) > WIDTH),
          ([3, 6], True))

    # A long first word below the widow is **not sufficient** for the branch, and this is the
    # check that says so: shorten only the SECOND word below.  `cols("no") + 1 + 98` still
    # exceeds the width and the line below is still over-width, and a covering window appears all
    # the same -- because what refuses the tail is the remainder *after* the split, `z * 98` in
    # the witness and `z * 10` here.  This is the neighbour that would have caught a docstring
    # claiming the first word decides it (issue 2176's first review).
    second_word = doc("x" * 99, "no", "y" * 98 + " " + "z" * 10, "c" * 60, "dd ee")
    check("... and shortening only the SECOND word below the widow gives it a window too",
          summary(second_word, "FormalSchemes/SecondWord.lean"),
          "  FormalSchemes/SecondWord.lean:2  paragraph of 5 lines; 4 of them refill to 3")
    check("... with the first word below unchanged, so the condition that is not sufficient holds",
          (cols("no") + 1 + cols("y" * 98) > WIDTH, numbers(second_word)), (True, [3, 6]))

    # ... and it is **not necessary** either.  Every line here opens with a word of at most
    # `MAX_TOKEN` columns, so the widow joins the line below freely -- which is what a covering
    # window is supposed to need -- and the branch is reached anyway, because a 90-column word in
    # the MIDDLE of the line below forces a break inside it wherever a window starts.
    middle_word = doc("mmm aa " + "k" * 75, "oo", "p" * 14 + " " + "t" * 90 + " " + "o" * 12,
                      "aaaaa jjj", "b " + "u" * 75)
    check("... while a paragraph whose every line opens with a short word reaches it regardless",
          summary(middle_word, "FormalSchemes/MiddleWord.lean"),
          "  FormalSchemes/MiddleWord.lean:2  paragraph of 5 lines;"
          " no window holding the stranded line refills shorter")
    check("... and it is sighted: no line of it opens with a word wider than `MAX_TOKEN`",
          (max(cols(l.split()[0]) for _, l in paragraphs(middle_word)[0]) <= MAX_TOKEN,
           numbers(middle_word)), (True, [3, 5]))

    # --- the printed window is not a fixed point (issue 2185) ----------------------------------
    # The window `show` prints absorbs the line it is printed against, and a greedy refill of it
    # can strand a *different* word: 88 of the 26 328 flag-instances over widths 60..140 do, and
    # `SpfGammaBase.lean:39` at 99 and `GeneralFibreProductBaseChange.lean:297` at 100 are the two
    # at this tree's own widths.  These fixtures drive the **report** and then re-scan what
    # following its advice produces, rather than comparing `repair_window` return values.
    def repaired(text, width=WIDTH):
        """`text` with `show`'s printed window applied to its one flagged paragraph.

        Written back into the file and re-segmented, because that is what the scan reads next --
        not kept as `lines[:start] + filled`, which is a list the segmentation never sees.  The
        difference between the two is exactly the bare `-/` cases below, and it is why the
        docstring's figure is 88 and not 97.
        """
        lines = text.split("\n")
        (paragraph, stranded), = scan_text(text, width, MAX_TOKEN)
        body = [line for _, line in paragraph]
        flagged = {number for number, _ in stranded}
        first = min(i for i, (number, _) in enumerate(paragraph) if number in flagged)
        start, filled = repair_window(body, width, first)
        base = paragraph[0][0]
        return "\n".join(lines[:base - 1] + body[:start] + filled + lines[base - 1 + len(body):])

    h50, g40, a90 = "h" * 50, "g" * 40, "a" * 90
    strands = doc(h50, g40, "no", a90, "aa bb cc dd")
    check("the window the report prints can strand a word the paragraph did not have",
          (summary(strands, "FormalSchemes/Strands.lean"), numbers(strands)),
          ("  FormalSchemes/Strands.lean:2  paragraph of 5 lines; 3 of them refill to 2", [4]))
    check("... and following it flags the paragraph again, at the line the refill left",
          (numbers(repaired(strands)), summary(repaired(strands), "FormalSchemes/Strands.lean")),
          ([5], "  FormalSchemes/Strands.lean:2  paragraph of 4 lines; 4 of them refill to 3"))

    # Its sightedness companion: one word longer in the tail, so the refill's last line carries
    # three words rather than two and is not short plain.  **Its report line is byte-identical to
    # the one above** -- same path, same figures -- which is the whole point: what a window does
    # once it is applied is not visible in what the report prints about it.
    settles = doc(h50, g40, "no", a90, "aa bb cc dd ee")
    check("... while a paragraph whose report line is identical can strand nothing",
          (summary(settles, "FormalSchemes/Strands.lean"), numbers(settles),
           numbers(repaired(settles))),
          ("  FormalSchemes/Strands.lean:2  paragraph of 5 lines; 3 of them refill to 2", [4], []))

    # The ruling the docstring makes: a refill that pushes a bare `-/` onto a line of its own has
    # stranded the delimiter and not a word, and the scan does not see it, because `STRUCTURAL`
    # takes a line *beginning* `-/` out of every paragraph.  `GeneralDiagonal.lean:74` at 130..132
    # is this tree's instance and this is its shape; a line *ending* ` -/` is prose and stays.
    terminator = "/-!\n" + "\n".join([h50, g40, "no", a90, "bb cc -/"]) + "\n"
    check("a printed window that pushes a bare `-/` onto its own line strands nothing",
          (summary(terminator, "FormalSchemes/Terminator.lean"), numbers(terminator),
           numbers(repaired(terminator))),
          ("  FormalSchemes/Terminator.lean:2  paragraph of 5 lines; 3 of them refill to 2",
           [4], []))
    check("... and the difference is the segmentation and not the arithmetic: as a bare list"
          " that same refill does hold a stranded `-/`",
          ([line for _, line in
            widows(list(enumerate([h50, g40, "no " + a90 + " bb cc", "-/"], 2)), WIDTH)],
           bool(STRUCTURAL.match("-/"))),
          (["-/"], True))

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

    # --- the stub species ----------------------------------------------------------------------
    # A widow is a word or two left at a paragraph's END; a stub is a short line in its MIDDLE,
    # left where a re-fill stopped.  `widows` sees a stub only when it happens to be short *plain*
    # -- at most two words -- and the commoner shape carries more, which is why `--diff` on
    # `e9679d6..3a724e0` reported 0 stranded lines over a paragraph holding two stubs.  Every
    # fixture below states which conjunct it is pinning **and** checks that the other two do not
    # reach, because `[]` is also what a broken predicate returns.
    def stub_numbers(text, min_atoms=MIN_ATOMS):
        return [n for p, s in scan_text_stubs(text, WIDTH, MAX_TOKEN, min_atoms) for n, _ in s]

    def stub_summary(text, path):
        """`show`'s own first line over the stub species, so the fixtures drive the report."""
        held, sys.stdout = sys.stdout, io.StringIO()
        try:
            for paragraph, stubbed in scan_text_stubs(text, WIDTH, MAX_TOKEN):
                show(path, paragraph, stubbed, WIDTH)
            return sys.stdout.getvalue().splitlines()[0]
        finally:
            sys.stdout = held

    def stub_repaired(text):
        """`text` with the window the stub report prints applied, written back and re-segmented."""
        lines = text.split("\n")
        (paragraph, stubbed), = scan_text_stubs(text, WIDTH, MAX_TOKEN)
        body = [line for _, line in paragraph]
        flagged = {number for number, _ in stubbed}
        first = min(i for i, (number, _) in enumerate(paragraph) if number in flagged)
        start, filled = repair_window(body, WIDTH, first)
        base = paragraph[0][0]
        return "\n".join(lines[:base - 1] + body[:start] + filled + lines[base - 1 + len(body):])

    tail = "and a tail that shortens the refill."

    # The species itself: a short line in the middle that a re-fill absorbs.  `widows` is silent
    # on it -- three words, so not short plain -- which is the whole finding of issue 2236.
    stub = doc("x" * 97, "a short stub", tail)
    check("a short mid-paragraph line a re-fill absorbs IS reported as a stub",
          stub_numbers(stub), [3])
    check("... and the widow species is silent on it, which is why the row exists",
          (numbers(stub), is_short_plain("a short stub")), ([], False))

    # Over-refusal control 1, and the one the row names first: the line below opens with a token
    # too long to join, so no re-fill would put it here and the line is forced.  Sighted on both
    # of the other conjuncts -- a covering window exists, so only the atom count keeps it out.
    forced = doc("x" * 97, "a short stub", "z" * 95, "aa bb", "cc dd ee ff gg")
    forced_lines = [l for _, l in paragraphs(forced)[0]]
    check("a short mid-paragraph line whose successor cannot join it is NOT a stub",
          3 in stub_numbers(forced), False)
    check("... and it is sighted: no plain atom fits, while a covering window does exist",
          (plain_atoms_fitting(forced_lines, 1, WIDTH, MAX_TOKEN),
           repair_window(forced_lines, WIDTH, 1) is not None), (0, True))

    # Over-refusal control 2: forced by a protected span.  The next line opens a backticked span
    # holding spaces; its first whitespace *word* fits and the span does not, so this fixture is
    # exactly the difference `atoms` makes.  `` ` ``-spans cross a break on 118 of 35413 in-scope
    # lines here, so the rule is the tree's practice and not a law -- hence `splits_an_atom`.
    span = "`Spf (A " + "q" * 80 + " B)`"
    protected = doc("x" * 97, "a short stub", span, "aa bb", "cc dd ee ff gg")
    protected_lines = [l for _, l in paragraphs(protected)[0]]
    check("a short mid-paragraph line held short by a backticked span is NOT a stub",
          3 in stub_numbers(protected), False)
    check("... and it is sighted: the span's first *word* would have fitted, and the span does not",
          (cols("a short stub") + 1 + cols(span.split()[0]) <= WIDTH,
           cols("a short stub") + 1 + cols(span) > WIDTH), (True, True))
    check("a backticked span holding spaces is one atom, and a bolded figure is one too",
          (atoms("`Spf (A, I)` and **0 against 47**, done"),
           atoms("**a bolded sentence with 47 in it** and more")),
          (["`Spf (A, I)`", "and", "**0 against 47**,", "done"],
           ["**a", "bolded", "sentence", "with", "47", "in", "it**", "and", "more"]))
    check("a bolded span is an atom only if it holds a digit, and only up to three words",
          (atoms("**a bold aside** and more"), atoms("**1 a b c d** and more"),
           atoms("**2 of 3** and more")),
          (["**a", "bold", "aside**", "and", "more"],
           ["**1", "a", "b", "c", "d**", "and", "more"],
           ["**2 of 3**", "and", "more"]))
    check("a break inside a span is seen, so those 118 lines are not read as stubs",
          (splits_an_atom(["and the map `Spf (A,", "I)` is the chart", "tail"], 0),
           splits_an_atom(["and the map", "`Spf (A, I)` is the chart", "tail"], 0)),
          (True, False))
    # ... and the guard has to be reached from `stubs`, not only asserted about: a line whose
    # break falls inside a span is not a stub even when everything else about it says it is.
    inside = doc("x" * 97, "a short stub and the map `Spf (A,",
                 "I)` is the chart aa bb", "cc dd ee ff gg", "hh ii jj kk ll")
    inside_lines = [l for _, l in paragraphs(inside)[0]]
    check("a short mid-paragraph line whose break falls inside a span is NOT a stub",
          3 in stub_numbers(inside), False)
    check("... and it is sighted: `plain_atoms_fitting` returns -1 there, and a window exists",
          (plain_atoms_fitting(inside_lines, 1, WIDTH, MAX_TOKEN),
           repair_window(inside_lines, WIDTH, 1) is not None), (-1, True))

    # The bound on `FILL_ATOM`, driven through `stubs` rather than through `atoms`: #826's `:427`
    # sits above a bolded *sentence*, and read as one atom that sentence fits nowhere, so the stub
    # the row was filed for would go invisible.
    long_bold = "**a 47 " + "c" * 80 + "**"
    bold_below = doc("x" * 97, "a short stub", long_bold + " aa bb", "cc dd ee ff gg",
                     "hh ii jj kk ll mm nn")
    check("a bolded SENTENCE below a stub does not hide it -- the 16-character bound",
          3 in stub_numbers(bold_below), True)
    check("... and it is sighted: read as one atom that span is too wide to fit anywhere",
          (len(atoms(long_bold)), cols("a short stub") + 1 + cols(long_bold) > WIDTH), (3, True))

    # `plain` stops the count; it does not merely skip.  Each half of it gets a fixture, because
    # dropping either one alone leaves the other looking like the whole rule.  In both, the atom
    # below FITS -- so the width is not what is refusing it -- and plain atoms follow it, so
    # counting past it instead of stopping would reach `min_atoms`.
    long_word_below = doc("x" * 97, "a short stub", "indistinguishable aa bb cc",
                          "dd ee ff gg hh ii")
    backtick_below = doc("x" * 97, "a short stub", "`abc` aa bb cc", "dd ee ff gg hh ii")
    check("a fitting atom that is long stops the count, so the line is not a stub",
          3 in stub_numbers(long_word_below), False)
    check("... and a fitting atom that is backticked stops it too, however short",
          3 in stub_numbers(backtick_below), False)
    check("... and both are sighted: each atom fits, and two plain atoms follow it",
          (cols("a short stub") + 1 + cols("indistinguishable") <= WIDTH,
           len("indistinguishable") > MAX_TOKEN,
           cols("a short stub") + 1 + cols("`abc`") <= WIDTH, len("`abc`") <= MAX_TOKEN),
          (True, True, True, True))

    # The joining space and the width comparison, at the boundary where each one decides.  The
    # second atom lands on exactly the fill width, which is the column `room > width` admits and
    # `room >= width` does not; drop the space and a third would land there instead.
    boundary = doc("x" * 97, "s" * 91, "aa bbbb cc dd ee ff", "gg hh ii jj", "kk ll mm nn")
    boundary_lines = [l for _, l in paragraphs(boundary)[0]]
    check("a line whose second atom lands on exactly the fill width IS a stub",
          3 in stub_numbers(boundary), True)
    check("... and it is sighted: that atom ends at column 99, so `>` and `>=` disagree here",
          (cols("s" * 91) + 1 + cols("aa") + 1 + cols("bbbb"), WIDTH), (99, 99))
    check("... and the count there is exactly two, so a third atom does not rescue it",
          plain_atoms_fitting(boundary_lines, 1, WIDTH, MAX_TOKEN), 2)

    # The `min_atoms` conjunct, which is what separates a stub from a break taken for sense: a
    # line short by exactly ONE plain atom differs from the greedy fill by a single decision.
    # Sighted from both sides -- at `--min-atoms 1` the same line is reported.
    one_atom = doc("x" * 97, "s" * 95, "aa bbbb cccc dddd", "aa bb", "cc dd ee ff gg")
    one_lines = [l for _, l in paragraphs(one_atom)[0]]
    check("a mid-paragraph line short by exactly one plain atom is NOT a stub",
          3 in stub_numbers(one_atom), False)
    check("... and it is sighted: exactly one atom fits, and at `--min-atoms 1` it is reported",
          (plain_atoms_fitting(one_lines, 1, WIDTH, MAX_TOKEN), 3 in stub_numbers(one_atom, 1)),
          (1, True))
    check("the default is two plain atoms, and it is measured (345 lines against 81)",
          MIN_ATOMS, 2)

    # The covering-window conjunct: a line every window containing it breaks even on.  The
    # paragraph is still reported, at another line, so the fixture is not passing by being empty.
    no_window = doc("x" * 99, "oo bb cc",
                    "p" * 14 + " " + "q" * 10 + " " + "t" * 92 + " " + "r" * 90, "c" * 60, "dd ee")
    no_window_lines = [l for _, l in paragraphs(no_window)[0]]
    check("a short mid-paragraph line no window containing it can absorb is NOT a stub",
          stub_numbers(no_window), [5])
    check("... and it is sighted: two plain atoms fit, and only the window conjunct refuses it",
          (plain_atoms_fitting(no_window_lines, 1, WIDTH, MAX_TOKEN),
           repair_window(no_window_lines, WIDTH, 1)), (2, None))
    # ... so `show`'s `no window` branch is unreachable for this species, by construction.
    check("every stub has a covering window, so the stub report never says it has none",
          all(repair_window([l for _, l in p], WIDTH,
                            min(i for i, (n, _) in enumerate(p) if n == s[0][0])) is not None
              for text in (stub, no_window)
              for p, s in scan_text_stubs(text, WIDTH, MAX_TOKEN)), True)

    # The two positional exclusions, and they are what keeps the two populations apart.
    leading = doc("a short stub", "and a tail here", "aa bb", "cc dd ee ff gg")
    check("a paragraph's FIRST line is never a stub, however short -- and the fixture is"
          " sighted, since the lines under it are reported",
          (2 in stub_numbers(leading), stub_numbers(leading)), (False, [3, 4]))
    trailing = doc("x" * 97, "and a middle line short enough to be a stub in its own right",
                   "four imports")
    check("... and a paragraph's LAST line is never a stub either -- that is the widow species",
          (stub_numbers(doc("y" * 80, "four imports")),
           numbers(doc("y" * 80, "four imports"))), ([], [3]))
    check("... and in a paragraph whose middle IS a stub, the last line is still only a widow",
          (stub_numbers(trailing), numbers(trailing)), ([3], [4]))

    # The two report paths take their species from one list, so a count cannot be taken from one
    # of them and compared against the other's population at the base.
    labels_and_scans = species_scans(WIDTH, MAX_TOKEN, MIN_ATOMS)
    check("both report paths read the same two species, in this order",
          ([label for label, _ in labels_and_scans],
           [[n for p, s in scan(stub) for n, _ in s] for _, scan in labels_and_scans]),
          (["stranded lines", "mid-paragraph stubs"], [[], [3]]))
    check("the atom count is on the summary line, at the value actually used",
          ATOMS_LINE % MIN_ATOMS, "plain atoms a stub must fit       :     2")

    # The report body itself: one listing for both species and both paths, so the count line and
    # the paragraphs under it cannot come from different places.  Driven rather than asserted.
    def listing(hits):
        held, sys.stdout = sys.stdout, io.StringIO()
        try:
            list_hits(hits, WIDTH)
            return sys.stdout.getvalue().splitlines()
        finally:
            sys.stdout = held

    check("the listing prints every flagged paragraph it is handed, and nothing when handed none",
          (listing([("FormalSchemes/S.lean", p, s)
                    for p, s in scan_text_stubs(stub, WIDTH, MAX_TOKEN)]), listing([])),
          (["  FormalSchemes/S.lean:2  paragraph of 3 lines; 2 of them refill to 1",
            "      :3  'a short stub'"], []))

    # Over-match control: prose that is a byte-exact greedy fill is flagged by neither species.
    exact = doc(*refill(["word"] * 80, WIDTH))
    check("a paragraph that is an exact greedy fill is flagged by neither species",
          (stub_numbers(exact), numbers(exact)), ([], []))
    check("... and it is sighted: it really is the fill, four lines of exactly 99 columns",
          [cols(l) for l in refill(["word"] * 80, WIDTH)], [99, 99, 99, 99])

    # The remedy, followed rather than described (issue 2236 §5).  First the ordinary case.
    check("the stub report prints the window that absorbs the line, and following it works",
          (stub_summary(stub, "FormalSchemes/Stub.lean"), stub_numbers(stub_repaired(stub))),
          ("  FormalSchemes/Stub.lean:2  paragraph of 3 lines; 2 of them refill to 1", []))

    # ... and then the branch an author would get wrong: the smallest window that absorbs the
    # stub starts ABOVE it, because the stub and everything under it refill to the same count.
    # The window an author would try first -- from the stub down -- saves nothing.
    above = doc("aa bb cc dd ee ff gg hh", "jj kk ll mm nn oo pp qq rr ss tt uu vv ww",
                " ".join(["zz"] * 21))
    above_lines = [l for _, l in paragraphs(above)[0]]
    check("a stub whose absorbing window starts above it is reported with THAT window",
          (stub_numbers(above), repair_window(above_lines, WIDTH, 1)[0],
           stub_summary(above, "FormalSchemes/Above.lean")),
          ([3], 0, "  FormalSchemes/Above.lean:2  paragraph of 3 lines; 3 of them refill to 2"))
    check("... and the window from the stub down -- the one to try first -- saves nothing",
          len(above_lines[1:]) - len(refill(above_lines[1:], WIDTH)), 0)
    check("... and following the printed window does remove it",
          (stub_numbers(stub_repaired(above)), numbers(stub_repaired(above))), ([], []))

    # --- dogfooding: this script's own docstring ------------------------------------------------
    own_paragraphs = _paragraphs_of(__doc__.split("\n"), lambda _n: True)
    own = [n for p, s in [(p, widows(p)) for p in own_paragraphs] for n, _ in s]
    check("this script's own module docstring strands nothing", own, [])
    own_stubs = [n for p, s in [(p, stubs(p)) for p in own_paragraphs] for n, _ in s]
    check("... and holds no stub either, under the rule it ships", own_stubs, [])

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
    parser.add_argument("--min-atoms", type=int, default=MIN_ATOMS,
                        help="plain atoms that must fit before a mid-paragraph line is a stub")
    parser.add_argument("--selftest", action="store_true", help="needs no build and no tree")
    args = parser.parse_args()

    if args.selftest:
        return selftest()
    if args.diff:
        return report_diff(args.diff, args.root, args.width, args.max_token, args.min_atoms)
    if args.tree:
        return report_tree(args.root, args.width, args.max_token, args.min_atoms)
    parser.error("one of --tree, --diff or --selftest is required")


if __name__ == "__main__":
    sys.exit(main())
