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
    python3 scripts/closure_audit.py --stub FormalSchemes.New:FormalSchemes.A,FormalSchemes.B

There is deliberately **no `--diff` mode**.  A closure figure is falsified by an edit somewhere
else in the tree, so the population that matters is every claim in every file, not the claims in
the hunks; a diff-restricted run would be blind to the only way these figures ever go wrong.  That
is the same argument `citation_audit.py`'s `markdown_line_pointers` makes for reading whole
documents.

`--selftest` prints **one line per case and nothing else**, and since row 2225 that is checked
rather than merely true: `main` captures the run, reports the count it printed, and exits **1** if
any other line is in there.  So the mode has two ways to fail -- a case, or the shape -- and
`grep -c ok` over its output is a reading of the case count.  What is *not* checked is that count
against a literal; the comment beside the gate in `main` says why, and it is a decision rather than
an omission.

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
out: they measure Mathlib's import graph, which this script does not walk.  One marker is read per
**figure** rather than per sentence -- an unpinned project total, which a closure claim in the same
sentence used to hide; *Project totals* below is why.  **The marker has to be
in a comment**, which the checked spelling does not have to be: `closure` case-insensitively is
`AlgebraicClosure` too, so without that gate a proof body joins a reading list of sentences and a
lemma about algebraic closures moves a coverage figure.

Most of what `--sweep` reports is legitimately out of reach -- deltas whose second figure is
counterfactual, intersections of several closures, peak-RSS numbers, issue numbers.  It is a
reading list, not a failure list.  **A figure in it that is a plain measurement of the tree should
be rewritten in the checked spelling rather than left for the next sweep**, and one endpoint of
every delta is such a measurement: *"importing it would take this file's closure from 48 to 93"*
says the closure is 48 **now**.

## Project totals, the one figure here with no subject

*"**140** of the **586** modules under `FormalSchemes/` carry a redundant import"* measures the
**tree**, not a module, so there is nothing to attribute and no way for the species to be declined:
it is checked or it is not seen.  That made it the one species where the grammar carries the whole
risk, and until row 2209 the grammar lost: the total was read only as a **companion**, in the tail
of a closure claim's own sentence, and this tree writes it in sentences with no closure phrase in
them and in front of the claim's own figure.  Both positions are out of a companion's reach, both
companion spellings had 0 occurrences anywhere under `FormalSchemes/`, and neither tolerated the
`**` every figure here is bolded with.  `FormalSchemes/RefinedOverlapTransition.lean` then carried
three numerals that went stale the moment a module was added -- at #811's head, with `--tree`
reporting MISMATCH 0 and `--sweep` reporting nothing new.

So `TOTAL` is its own scan over whole files, and it keeps **two** rules.  **The count has to be
pinned to the tree** -- by a possessive (`this tree's`, `the project's`, `the library's`) or by the
path after `under` -- and **nothing may post-modify the noun phrase it sits in**, because
post-modification is the only thing that turns a count of the tree into a count of a subset.
Everything else is the reading list's: *"**2** of the **5** modules that import it"* is a subset in
the same words, and reading its 5 as the total would be a confident MISMATCH against correct prose,
which this file argues throughout is worse than a gap.  That decision costs one of the three
numerals above -- the paragraph states the same total a second time as a bare *"**538** of the 586
modules"* -- and `--sweep` now reports that sentence, which is the disposition `CONTRIBUTING.md`
prescribes for a measurement the checker cannot read.  It is also the one place where `--sweep`'s
*"the sentence is already seen by `claims`"* exclusion is decided per **figure** and not per
sentence: the closure claim beside an unpinned total is exactly what hid it, and since row 2213 the
checked-total exclusion beside it is read per figure for the same reason.

**This species has no decline path and does not need one, and that is a decision rather than an
omission** (row 2213). Every other decline in this file is the *script* refusing to attribute an
ambiguous subject, and the repair is always to reword the prose -- there is no author-written
opt-out marker anywhere here, and adding the first one would be adding the first place a stale
figure can hide, in the species that exists because three of them hid. What replaces a decline is
that a sentence read wrongly is **already** dispositionable, in one clause and without touching the
numeral, because the two rules above are rules about the *shape* of the phrase and the author
controls the shape:

* a subset count that the guard already refuses needs **no** edit -- it is not read as a total, and
  `TOTAL_UNCHECKED` puts it on `--sweep`, so it is still read by a human;
* for the two shapes no regex separates from a finite verb -- an **adjective phrase** (*"the **2**
  modules under `FormalSchemes/` reachable from it"*) and a **zero relative** (*"…`FormalSchemes/`
  `FormalSchemes.Base` reaches"*) -- inserting `that` or `that are` turns each into a relative
  clause the guard does refuse, and both land on the reading list.  `--selftest` carries the pair
  before and after, and `--tree` prints the recipe under any total MISMATCH it reports.

So the only way to reach a red `--tree` on a correct sentence is to write one of those two shapes
and not read the three lines the MISMATCH prints.  The population of both at `d699026` is **0**.

## A tree census, and the bucket values row 2214 left alone

A **census** is the third shape this tree writes about its own module set: a partition of the
modules by how much of a named set each of them reaches.  Its *total* -- *"the only one of the
**T** modules under `FormalSchemes/`"* -- has been a checked figure since row 2214 and is a
`TOTAL`-shaped question.  Its **buckets** -- *"**A** reach none, **B** reach exactly one and **C**
reach two"* -- were not, and the reason row 2214 gave was that checking them needs the instrument to
know *which* modules the sentence is a census of.  The shape is written in letters here for the
reason the comment beside `CENSUS_UNCHECKED` gives: `scripts/` is outside every instrument's walk,
so a numeral copied into this file rots the next time somebody adds a module and nothing notices.

It can know, and what makes it possible is not a cleverer resolver: it is that a census **spells the
cardinality of its own subject set in words**.  *"reaches all six of the above"* resolves to six
module tokens or the reading is refused.  Nothing else in this file has that -- every anaphor
`attribute()` resolves is taken on faith, because a sentence saying *that file* does not also say
how many files it meant -- and it is why the buckets can be a **checking** species rather than a
guess.  Four gates run before any figure is compared, and every one of them declines rather than
picking:

* the sentence spells a cardinality, and the set resolves to exactly that many modules **of this
  tree** -- from the sentence itself, or one hop back from the `## Placement` opener and only from
  before its colon, because an opener names its own module again after the colon;
* the universe is named, as *the other **N*** (every module but the one whose docstring this is) or
  as *the only one of the **N*** (all of them), and never both;
* every bucket predicate is a number word in a closed vocabulary and is an index into a set of that
  size;
* the self-counting convention holds -- a declaration placed in a file has that file's own contents
  -- unless the sentence declares the other one, in which case the reading is refused.  Accepting
  both silently would give a stale figure two ways to look right.

What is then checked is the universe's own numeral, each bucket against the walk, the **remainder**,
and -- where the sentence says *this* module is the only one to reach the whole set -- that member
by name.  The remainder is the one worth spelling out, because it is what row 2220 measured the
arithmetic to be blind to: the buckets a census states in words without a numeral are not inferred
from the shortfall, they are read off the walk, and the sentence has to have **named** them.  So a
module landing in a bucket above every index the sentence mentions is red here, and a sum rule
cannot see it.

This is the species where a MISMATCH means **change the numeral**, which is the opposite of what a
total's or a census total's remedy says.  A figure that has passed four gates is one whose reading
is pinned, so the sentence is stale rather than misread; refusing the reading is still available and
is done by breaking a gate.  The two gates cost different things and it is worth saying which is
which: **eliding the spelled cardinality** leaves the sentence a census this walk cannot pin, so it
is printed in `--tree`'s `census-declined` block with the reason, while **dropping the `N reach`
spelling** stops it being a census here at all and puts it back on `--sweep`.  Either way `--tree`
goes green on it; only the second returns it to the list row 2214 kept it on.

The one claim in the species that is **not** a numeral is the identity -- *"this module is the only
one of the **N**"* -- and it is reported as two figures rather than one, because the sentence
asserts two things: that this file is in the top bucket, and that nothing else is.  Both are
reported against a count the reader can act on, and the second names the modules the walk found,
because *states 1, walk gives 1* is what a single membership figure degenerates to when the count
is right and the member is wrong.  Its remedy is its own for the same reason: there is no numeral
to re-run for.

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

If `B` already *reaches* `A` the edge would close a cycle and Lean would refuse the tree, so the
report says so on a `NOTE` line and prices it anyway.  It is a **label and not a refusal**: the
figures are a well-defined walk of that digraph, an author weighing *"should `A` import `B`, or
`B` import `A`?"* is asking how far apart the two ends are, and on this tree every one of the
existing import edges is such a pair when flipped -- so refusing would decline the commonest
second half of the question the mode exists to answer.

**This mode does not read the counterfactual sentence and must not pretend to.**  It prints what
the tree would say; comparing that against what a paragraph does say is the author's job, exactly
as with `--sweep`.  Every run that produces a report exits **0** -- there is no tree here for a
gate to be about; an invocation this mode cannot make sense of, a name that is not a module of
this tree or a module asked to import itself, still fails as any other bad argument does.

## `--stub`, which prices a module that does not exist

`CONTRIBUTING.md`'s *What adding a module costs* prescribes an experiment -- write a stub module,
run `--tree`, count the MISMATCH population, delete the stub -- and a `## Placement` paragraph then
quotes the result in prose.  That sentence is a measurement of a tree that does not exist, and until
this mode it was the one figure species here with **no instrument at all**: `--tree` cannot check it
because the subject is off the tree, `--edge` prices an import rather than a module, and `--sweep`
could only list the sentence when something *else* in it happened to carry a marker.  The cost of
that was not hypothetical.  One such figure was published wrong at six consecutive heads of one
branch, by a different amount at each, because the count moves as the authoring pull request's own
docstring grows -- so a figure measured mid-development is stale before the pull request opens, and
nothing here could notice (issue 2221).

`--stub NAME:A,B,C` runs the experiment instead of describing it: the tree is copied to a temporary
directory, the stub is written into the copy as its import lines and nothing else, and both trees
are audited.  The price is the copy's MISMATCH population minus the tree's own, so the report is
about the stub even on a red tree -- `_fingerprint`'s argument, shared with `--edge`.

**The imports are the experiment, so they are named and echoed and never inferred.**  *A module over
this one* and *a module repeating this one's imports* are different questions with different
answers, over file lists that can be identical, and a mode that let the second be spelled as the
first would answer the wrong one silently.

**Two species and no third**, which is `CONTRIBUTING.md`'s own table: a **project total or tree
census**, which a new module falsifies wherever on the tree it is written, and a **reverse closure**
of a module the stub reaches.  A stub is a leaf -- nothing imports it -- so no forward closure can
move, and it adds a file rather than growing one, so no size figure can move either.  Anything
landing outside those two is `unclassified`, which is never a level: it is a claim shape nobody has
thought about, or a bug here.  The reverse-closure bucket carries a *leaf-sentence* sub-count beside
it, because a paragraph that calls its own file a leaf is **rewritten** rather than renumbered when
it gains a consumer, and that repair is not a `+1`.

**The rebuild is the figure three sessions have disagreed about, so both conventions are printed and
the self-inclusion rule is in the output text rather than in a comment.**  One sentence of this
tree's prose has been published with three different union figures by three different sessions, and
nobody miswalked anything: the differences are *counting a repaired file as re-elaborating itself*
against *counting only the modules that import one*, and *with the stub on the tree* against
*without it*.  A prose clause has never managed to carry that, and an instrument has to pick.  The
union is taken on the tree the repairs are made in -- the one **with** the stub, since the new
module has to be elaborated too -- and the same union without it is printed on the line below.  The
largest single contributor is named with the union that drops it, which is the arithmetic
`CONTRIBUTING.md` already does by hand for `FormalSchemes/StructureSheaf.lean`.

**A copy of the tree, not a synthesised module map, and the reason is not caution.**  `--edge` needs
no copy because it changes the *graph* and never the module *set*: `closures(mods, deps)` opens no
file when `deps` is given.  A stub changes the set, and every other reader here -- `claims`,
`total_claims`, `size_claims`, `invisible`, `file_size` -- resolves a module through `open(path)`,
while `closures` keys the reverse closures on `mods`, so the stub has to be **in** `mods` and
anything in `mods` is opened.  Copying is a tenth of a second against two audits of several seconds
each, it makes this mode *literally* the manual experiment `CONTRIBUTING.md` prescribes, and it
leaves every one of those readers untouched.  **Nothing is written under the repository**: the copy
is a `tempfile.TemporaryDirectory`, removed on every exit path including an exception, and
`--selftest` asserts the tree is byte-identical after a run that raised.

Like `--edge`, this prices and does not check.  It reads no counterfactual sentence and it cannot go
red against one -- the sentence names a stub that is not in the report's input, so there is nothing
to attribute the figure to -- and every run that produces a report exits **0**.  **Reproducibility
is the deliverable here and enforcement is not available**, which is worth saying out loud so that
no reader waits for a MISMATCH that cannot come.

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
# the claim's own subject count, except for `self`, which is the *file's* closure rather than the
# subject's.  A project total was a third kind here until row 2209 and is a claim species of its own
# now: it has no subject, so nothing about it is read under a host claim's convention, and the
# position a companion is looked for in is not where this tree writes it.  See `TOTAL`.
COMPANIONS = [
    (re.compile(r"\((\d+)(?: modules)?(?: counted)? with itself\)"), "subject", 1),
    (re.compile(r"\((\d+)(?: modules)?(?: counted)? besides itself\)"), "subject", 0),
    (re.compile(r"(\d+) with itself\b"), "subject", 1),
    (re.compile(r"(\d+) before this (?:leaf|file|module)"), "subject", -1),
    (re.compile(r"against this (?:leaf|file|module)'s \*{0,2}(\d+)"), "self", 0),
]

# **A pin in front of the noun phrase is undone by a modifier behind it**, and post-modification is
# the *only* thing that turns a count of the whole tree into a count of a subset.  So the pinned
# spellings are read only when nothing post-modifies them, and this is the list of what counts.
# English post-modifiers of a count noun are four: a relative clause, a participial phrase, a
# prepositional phrase, and an adjective phrase.  The first three are mechanically separable from
# the finite verb that follows a total (*"…under `FormalSchemes/` **carry** an import"*); the fourth
# is not, and it is named at the end of this comment rather than pretended away.
#
# The guard errs towards **refusing**, deliberately and in one direction only: a refused total is
# still read by a human, because `TOTAL_UNCHECKED` puts it on `--sweep`'s reading list, while a
# false MISMATCH is a red `--tree` on somebody's correct sentence and `--tree` MISMATCH 0 is an
# acceptance criterion on every row of this board.  `\w+ed` is the clearest case of that trade: it
# refuses the past-participial *"the **17** modules under `FormalSchemes/` **repaired** by #807"*,
# and with it a preterite main verb (*"…**paid** for the edit"*), which is a total merely swept.
#
# The prepositions are the **restrictive** half of the closed class and not the whole of it.  `at`,
# `of`, `by`, `for`, `to`, `on`, `as`, `from` and `in` are deliberately **absent**: after a complete
# noun phrase each of those overwhelmingly opens an anchor, an argument of the verb still to come or
# a scope phrase that leaves the total a total -- *"…under `FormalSchemes/` **at** `267efe3`"*,
# *"…**of** which **140** carry an import"*, *"…**in** total"* -- and refusing them would cost the
# commit-anchored spelling `CONTRIBUTING.md` asks authors for.
#
# What no regex settles, said rather than hidden, with the population of each at `d699026`:
# an **adjective-phrase** modifier (*"the **5** modules under `FormalSchemes/` reachable from
# `Foo`"*) and a **zero relative** (*"the **2** modules under `FormalSchemes/` `Foo` imports"*).
# Both are **0**.  Neither is a reason to grow an author-written opt-out; see the module docstring's
# *Project totals* section for why this species has no decline path and what replaces one.
RESTRICTION = (r"(?!\s+(?:that|which|who|whose)\b)"
               r"(?!\s+\w+(?:ing|ed)\b)"
               r"(?!\s+(?:with|without|inside|outside|within|above|below|beyond|beneath|"
               r"underneath|between|among|amongst|beside|besides|behind|except|excepting|"
               r"regarding|concerning)\b)")

# A **project total** -- the number of modules under `FormalSchemes/` -- is the one figure this tree
# quotes that has **no subject**: it is a property of the tree and not of any module, so there is
# nothing for `attribute` to pin down and the sentence carrying it need not carry a closure claim at
# all.  It was a `COMPANIONS` entry until row 2209, read only in the tail of a closure claim's own
# sentence, and that position is not where this tree writes it: at `267efe3` both companion
# spellings had **0** occurrences anywhere under `FormalSchemes/`, while the spelling the tree does
# use -- ``of the **586** modules under `FormalSchemes/` `` -- sat once in a sentence with no
# closure phrase in it (`RefinedOverlapTransition.lean:107`) and once *before* the figure of the
# claim in its own sentence (`:118`), which is out of a companion's reach by construction.  So the
# species was unreachable in both directions at once, and three numerals rotted behind it on #811
# with `--tree` reporting MISMATCH 0.  It is its own scan now, over whole files, attributed to
# nothing.
#
# The grammar keeps the two properties that make reading a total safe: **the noun phrase has to be
# pinned to the whole tree**, by a possessive (`this tree's`, `the project's`, `the library's` --
# the same three `SWEEPABLE` has always listed) or by the path after `under`; and **nothing may
# post-modify it**, which is `RESTRICTION` above.  A bare *"N of the M modules"* is deliberately
# **not** checked -- *"**2** of the **5** modules that import it"* is the same words about a subset,
# and reading its `5` as the project total would be a confident MISMATCH against correct prose,
# which is the outcome this script's own comments call worse than the decline it replaces.  That
# shape goes to the reading list instead (`TOTAL_UNCHECKED`).
#
# The possessive set is **one** spelling, not three plus a special case.  `the project's` was the
# incumbent and the other two were swept and not checked until row 2213; two possessives pinning the
# same noun to the same tree with opposite dispositions is an arbitrary line, and drawing it cost
# the coverage rather than buying anything.  Population of the two newly checked spellings at
# `d699026`: **0**, so this widens what is readable without moving a figure.
#
# Two details are read off the tree rather than assumed, and one of them **narrows** the incumbent
# grammar rather than widening it.
#
# The numeral is **bolded** in every closure figure here, and neither incumbent regex tolerated
# `**`, so neither could have read this tree's spelling even in the companion position.
#
# And `under` on its own does **not** pin the phrase to the tree, which is the one decision row 2209
# left open.  The incumbent `over the (\d+) modules under` did not require the path, and with a
# numeral in the phrase that is the over-wide reading: *"the **3** modules under it"*, *"the **17**
# modules under the Tate prefix"* and *"the **12** modules under `FormalSchemes/Tate`"* are all
# subset or subtree counts in the same words, and reading one of those as the project total is the
# confident MISMATCH against correct prose that this script's comments call worse than a gap.  The
# path is therefore required, in either the backticked or the bare spelling; the population the
# narrowing gives up is **0 sentences at `267efe3`** -- both incumbent spellings matched nothing
# anywhere under `FormalSchemes/` -- and what it gives up in the future lands on the reading list
# instead, which is what `TOTAL_UNCHECKED` is for.
#
# **The same shape sits on the other side of the pin and is refused there too**, and that is
# `RESTRICTION`'s whole job: *"the **2** modules under `FormalSchemes/` that import `Foo`"* is a
# subset in the same words as the total, and a sentence saying it is usually **correct** -- the
# numeral is the size of somebody's reverse closure.  Row 2209 shipped the pronoun and participle
# halves of that guard; row 2213 widened it to the prepositional one and applied the whole of it to
# **both** patterns, because a pin in front of the noun phrase does not survive a modifier behind
# it whichever pin it was.
#
# **Read `RESTRICTION` together with the path alternation, which is why the alternation is spelled
# out rather than written `` `?FormalSchemes/`? ``.**  With an optional closing backtick the engine
# can leave that backtick unconsumed, and then *every* lookahead appended after it is inspecting a
# backtick rather than the next word -- so the guards silently do nothing in the backticked
# spelling, which is the one this tree writes.  The incumbent `(?![A-Za-z])` survived only because a
# deeper path fails for a second reason (the *opening* `` `? `` cannot then match the literal).
# Measured: with `` `? `` the `that` clause above is read as a total.
TOTAL = [
    re.compile(r"of (?:this|the) (?:tree|project|library)'s \*{0,2}(\d+)\*{0,2} modules"
               + RESTRICTION, re.I),
    re.compile(r"the \*{0,2}(\d+)\*{0,2} modules under "
               r"(?:`FormalSchemes/`|FormalSchemes/(?![A-Za-z]))" + RESTRICTION, re.I),
]

# The total spellings `TOTAL` declines to check, which are therefore the ones `--sweep` has to
# carry: the module-count noun phrase with nothing pinning it to the whole tree, and the pinned one
# with something post-modifying it.  At `d699026` the live instances are the two sentences of
# `FormalSchemes/RefinedOverlapTransition.lean`'s `## Placement` that restate the tree's total as a
# bare *"N of the 586 modules"* -- and each sits in a sentence that **also** carries a closure
# claim, so the per-sentence `CLOSURE` exclusion in `invisible` hid them as well, which is why that
# exclusion and the checked-total one beside it are both read per **figure** for this species.
# There are two triggers: the preposition, `of` or `over`, matching the two the tree writes; and the
# *"N modules under"* noun phrase itself, which carries the shapes `TOTAL` refuses after the path --
# without that second alternation a restricted total is invisible to both instruments, which is the
# state row 2209 exists to end.  The possessive spellings `TOTAL` refuses for the same reason reach
# the reading list through `SWEEPABLE`'s own possessive alternation rather than through this one.
TOTAL_UNCHECKED = re.compile(r"\b(?:of|over) the \*{0,2}\d+\*{0,2} modules?\b"
                             r"|\bthe \*{0,2}\d+\*{0,2} modules under\b", re.I)

# `forward closure 36 with itself` -- the other convention, inline.
WITH_ITSELF = re.compile(r"^\s*(?:project |modules? )*(?:counted )?(?:with itself|including it)")

# A sentence naming Mathlib is measuring Mathlib's import graph, not this tree's, and no walk here
# can check it.  It is left out of `--sweep` rather than reported and dismissed every run.
MATHLIB = re.compile(r"Mathlib", re.I)

# A **tree census** is the third shape this tree writes about its own module set, after a closure
# figure and a project total: a partition of the modules into buckets, stated with no closure phrase
# in it and with the noun of the count phrase *elided*.  Both live examples are in
# `FormalSchemes/RefinedOverlapTransition.lean`'s `## Placement`; the shape is written here in
# letters rather than quoted, because this file is outside every instrument's walk and a numeral
# copied into it rots the next time somebody adds a module, which is the defect row 2214 is about.
# `T` is the tree's module count and `A`, `B`, `C`, `D` are the buckets, the primes marking the
# second census's:
#
#     the best any of the other T-1 does is **three**, and only D of them manage that:
#     **A** reach none, **B** reach exactly one and **C** reach two.
#     this module is the only one of the T that reaches all three -- A' reach none of
#     them, B' reach exactly one, C' reach two and this file is the one that reaches three.
#
# **Row 2214's decision, and it is a decision rather than the obvious reading of its own §3.**  That
# row proposes checking *"the other **N**"* as `len(mods) - 1` and *"the only one of the **N**"* as
# `len(mods)`, on the ground that neither needs a subject.  The arithmetic is right and the grammar
# is not, and both halves were measured before this was written:
#
# * *"the other **N**"* is **not** checked here, in any spelling.  `the other` needs an antecedent
#   for what is *excluded*, and the regex cannot see it: on this tree the exclusion is the module
#   the docstring is in, so the figure is `len(mods) - 1`, but *"the other **T-6** modules under
#   `FormalSchemes/`"* excluding a named six is the same words and the same shape.  Reading one as
#   the other is a confident MISMATCH against correct prose in the one species with **no decline
#   path**, which is the trade this file refuses everywhere.  It goes to the reading list.
# * *"the only one of the **N**"* **is** checked, and only when the noun phrase is pinned to the
#   tree by the path -- because `the only one of the N modules under `FormalSchemes/`` asks no
#   *other than what* question: the `N` is the size of the set the one is drawn from, and the phrase
#   says which set that is.  The bare spelling, with the noun elided, is not checked, because *"the
#   only one of the **6** imports"* is the same words about something that is not the module set.
# * the **bucket** figures (*"**A** reach none"*) are not checked by anything and are not meant to
#   be: they need the instrument to know which nine modules the sentence is a census *of*, which is
#   a richer reading than any species here does.  Reading list.
#
# **The population of the checked spelling on this tree is 0, and that is the point rather than a
# disappointment.**  Both live census totals have the noun elided, so the row's own proposal would
# not have checked either of them either; what the two options differ in is which spelling an author
# can *opt into*, and what closes row 2214's actual cost -- seven numerals falsified silently by a
# module addition while `--tree` reported MISMATCH 0 -- is `CENSUS_UNCHECKED` below, which puts both
# sentences on `--sweep` where a human reads them every run.
#
# **No trailing guard, deliberately, and this is the one place `RESTRICTION`-shaped reasoning does
# not transfer.**  In *"the only one of the **N** modules under `FormalSchemes/` that reaches all
# three"* the relative clause restricts *the only one*, not *the N modules*, so the figure is a true
# total and refusing it would be wrong.  That is also why this cannot be a `TOTAL` alternation: at
# `05a5fe2` `TOTAL[1]`'s own `(?!\s+(?:that|which|who|whose)\b)` refuses exactly that sentence, so
# the pinned census total is invisible to it.  Having no trailing guard also means there is no
# lookahead here for `**` to defeat -- which matters, because the tree bolds emphasised words and a
# bolded post-modifier walks straight past a guard that begins `\s+`.  The **path** still has to be
# unbolded, exactly as in `TOTAL`: ``under **`FormalSchemes/`**`` is read by neither species, and
# the population of that spelling under `FormalSchemes/` at `05a5fe2` is **0**.
CENSUS = [
    re.compile(r"the only one of the \*{0,2}(\d+)\*{0,2} modules under "
               r"(?:`FormalSchemes/`|FormalSchemes/(?![A-Za-z]))", re.I),
]

# The line a `--tree` MISMATCH prints beside a total-shaped figure, and it is a property of the
# **species** rather than of `kind`.  `TOTAL` and `CENSUS` share `kind="total"` on purpose --
# `--edge` partitions both on `subject=None`, and nothing downstream wants them apart -- but the
# remedy is the one thing about them that is opposite.  Post-modifying the noun phrase is what makes
# a `TOTAL` refuse; it is a **no-op** for `CENSUS`, which carries no trailing guard by design.  So
# printing the total's line under a census MISMATCH would name three edits -- `that`, a participle,
# `with` -- that all leave the tree red, in the one species with no decline path, and an author who
# followed it would have no way out at all.  Measured before this was written: all three do (row
# 2214).  The lines are stored wrapped with their parentheses, so `main()` prints and decides
# nothing, and a fixture can assert *which* remedy a mismatch carries without reading stdout.
TOTAL_DISPOSITION = (
    "(if that numeral is not the tree's module count, the sentence is right and the reading is",
    " wrong: post-modify the noun phrase -- `that`, `which`, a participle or `with` -- and it",
    " goes to --sweep instead.  Do not change the numeral.)",
)

# The census's own remedy, which is the opposite one: `CENSUS[0]` reads the count only when the noun
# phrase names the path, so **eliding the noun** is what sends the sentence to `--sweep` -- *"the
# only one of the **2** that import `Foo`"*.  Naming the subset instead (*"of the **2** modules that
# import `Foo`"*) is the other way out, and is `TOTAL_UNCHECKED`'s shape.
CENSUS_DISPOSITION = (
    "(if that numeral is not the tree's module count, the sentence is right and the reading is",
    " wrong: post-modifying it does not help here -- elide the noun (`the only one of the N`)",
    " or name the subset, and it goes to --sweep instead.  Do not change the numeral.)",
)

# The census spellings nothing checks, which are therefore the ones `--sweep` has to carry: the two
# elided count phrases and the bucket predicate.  The bucket marker is deliberately the loose
# `N reach` / `N reaches` rather than an alternation of *none* / *exactly one* / *two* -- it reaches
# every bucket predicate the tree writes and, measured at `05a5fe2`, both spellings put the same
# **2** sentences on the list, so the narrower one buys nothing and would go stale against the next
# way somebody words a bucket.  `the only one of the N` is matched here as well as in `CENSUS`,
# being a prefix of it; `invisible` tries `CENSUS` first for that reason, exactly as it does for
# `TOTAL`.
CENSUS_UNCHECKED = re.compile(r"\bthe other \*{0,2}\d+"
                              r"|\bthe only one of the \*{0,2}\d+"
                              r"|\b\*{0,2}\d+\*{0,2} reach(?:es)?\b", re.I)

# A counterfactual **price**: *"**15** figure repairs in **9** files"*, the shape `--edge` and
# `--stub` publish and the shape a `## Placement` paragraph quotes back at them.  It is a marker for
# `--sweep` and never a species, and the reason is the one `--stub`'s section of the module
# docstring gives: the subject is a tree that does not exist, so there is nothing for `--tree` to
# attribute the figure to -- which is exactly why the sentence wants a human reading it every run
# rather than nothing reading it ever.  Measured at `2857956`: five sentences in three files carry
# this shape,
# four of which were already on the reading list for a neighbouring closure word or project total,
# and the fifth was hidden by the per-sentence `CLOSURE` exclusion in `invisible` -- the row 2209
# mechanism again, a figure invisible because of the claim beside it.  Keyed on the **numeral**, so
# *"no figure repaired anywhere"*, which states a price of none in words, is not a hit: there is no
# measurement in it to re-run.
PRICE = re.compile(r"\*{0,2}\d+\*{0,2} figure repairs?\b", re.I)

# A module name `--stub` will accept: at least one component under `FormalSchemes`, each of them a
# word of the character class `IMPORT` reads.  It is deliberately not a check that the name is a
# legal Lean identifier -- nothing here runs Lean -- only that the file it names is one the walk
# finds.  A `startswith` test is not enough, and the two shapes it lets through are the reason this
# is a `fullmatch`: `FormalSchemes.` builds the path `FormalSchemes/.lean`, which `glob` does not
# match because of the leading dot, and a name carrying a path separator writes outside the
# directory the walk reads.  Neither can reach
# the repository -- the stub is written into a copy -- but both make the stub **absent** from the
# tree that is then priced, and the failure is a `KeyError` two functions later rather than a bad
# argument at the door.
STUB_NAME = re.compile(r"FormalSchemes(?:\.[A-Za-z0-9_]+)+")
# ---------------------------------------------------------------------------------------------
# A census's **bucket values**, which row 2214 declined and this walk checks.
#
# `CENSUS_UNCHECKED` above puts a census sentence on `--sweep` and says why the buckets are not
# checked: *"they need the instrument to know which nine modules the sentence is a census of, which
# is a richer reading than any species here does."*  The instrument can know, and the reason is that
# **each census names its own subject set and spells that set's cardinality in words**, so the
# resolution is checkable before it is used.  Nothing else here has that: every anaphor
# `attribute()` resolves is taken on faith, because a sentence saying *that file* does not also say
# how many files it meant.  Here *"reaches all six of the above"* resolves to six module tokens or
# the reading is refused -- the text states the answer to the question the resolver is asking, and
# that checksum is what makes a **checking** species out of what would otherwise be a guess.
#
# Measured at `2857956`, the population of census sentences under `FormalSchemes/` is **2**, both in
# `FormalSchemes/RefinedOverlapTransition.lean`'s `## Placement`, and between them they carry the
# thirteen numerals row 2224 §1 tabulates.  They resolve their subject set two different ways, and
# both mechanisms are needed.  **Both are quoted verbatim at `2857956` and every numeral in them is
# the tree's own, so read them as a dated transcript and not as a figure of this file:** `scripts/`
# is outside every instrument's walk, and this is the one place below where a live numeral is copied
# rather than lettered, because the shape of the *sentence* is what the grammar has to be read
# against.
#
#     No module of this tree reaches all six of the above -- the best any of the other 586 does
#     is **three**, and only 4 of them manage that: **416** reach none, **146** reach exactly
#     one and **20** reach two.
#
#     ... and **this module is the only one of the 587 that reaches all three** -- 546 reach
#     none of them, 35 reach exactly one, 5 reach two and this file is the one that reaches three.
#
# The first names **0** modules in its own sentence and six in the `## Placement` opener one
# sentence back, before that opener's colon; the second names its three in its own sentence and
# **0** in the sentence before it.  So the resolver tries the sentence itself and then one hop back,
# and the cardinality checksum is what decides between them rather than a preference.
#
# **The colon is load-bearing on the hop.**  The opener is *"A leaf over `A`, ..., `F`: the forward
# closure of `Self` is **71** ... and the reverse closure of `Self` is **0**."* -- 8 module tokens,
# 7 distinct, because it names the subject module twice after the colon.  Only the **6** before the
# colon are the subject set.  One hop is `_inherited()`'s existing proximity rule and the opener is
# a tree-wide idiom rather than one sentence: at `2857956`, `leaf over` appears in **11** files and
# line-initial `A leaf over` / `The leaf over` in **6**.
#
# **What this species does *not* read, each with its population at `2857956`.**
#
# * the alternative-convention quadruple, *"the closure convention of this section, which does not,
#   gives 420 / 144 / 18 / 4"*.  It is a separate sentence (`BREAK` is `[.;]\s` and a semicolon
#   splits the parenthetical), it carries no bucket predicate, and reading it would mean binding
#   four bare numerals to four buckets **by position** -- and the numerals being descending here is
#   a property of this tree, not of the shape.  Population **1**, and it keeps its `--sweep` entry,
#   which is the right place for a figure whose grammar is one sentence wide.
# * a census whose sentence declares the strict convention for its own buckets.  Population **0**:
#   both live censuses use the self-counting reading, and the tree spells the other one out when it
#   means it.  `CENSUS_STRICT` below declines rather than guesses.
BUCKET_WORD = {"none": 0, "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
               "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12}

# One bucket: a numeral, `reach` or `reaches`, and the bucket's **index as a word**.  Reading the
# predicate is the decision row 2224 §3.4 asks for, and the alternative -- checking the multiset of
# numerals against the multiset of non-empty bucket sizes -- is measurably weaker on this tree: at
# `2857956` two of `:305`'s three numerals could be swapped with each other and the multiset would
# not notice, while the predicate does.  The vocabulary is closed and tiny (`none`, `exactly one`,
# `two` here) and anything outside `BUCKET_WORD` **declines**, so the strong reading costs nothing
# in the direction that matters.  `exactly` is optional and consumed because the tree writes both.
BUCKET = re.compile(r"\*{0,2}(\d+)\*{0,2}\s+reach(?:es)?\s+(?:exactly\s+)?([a-z]+)\b", re.I)

# The subject set's cardinality, spelled.  This is the gate: no spelled cardinality, no census.
CENSUS_SUBJECT = re.compile(r"\breach(?:es)?\s+all\s+([a-z]+)\b", re.I)

# The two universe phrases, and they are the two `CENSUS_UNCHECKED` already lists.  `the other N`
# excludes the module the docstring is in; `the only one of the N` includes it, which is what *the
# only one* means -- the subject is a member of the set it is the only one of.  Exactly one must be
# present, because they name different universes and a sentence stating both states nothing.
#
# **Row 2214 declined *"the other N"* as a total and this does not overturn that.**  That decline is
# about a numeral with no antecedent for what is *excluded*: *"the other **T-6** modules under
# `FormalSchemes/`"* excluding a named six is the same words.  Here the numeral is read only after
# the subject set `S` has resolved, which makes the two readings **distinguishable** -- `len(mods)
# - 1` against `len(mods) - len(S)` -- and the second gets a decline of its own below rather than a
# MISMATCH.  A numeral matching neither is a stale figure and is reported, which is the whole point:
# adding a module to the tree falsifies *"the other 586"* and nothing before this noticed.
CENSUS_OTHER = re.compile(r"\bthe other \*{0,2}(\d+)\*{0,2}\b", re.I)
CENSUS_ALL = re.compile(r"\bthe only one of the \*{0,2}(\d+)\*{0,2}\b", re.I)

# A sentence declaring, for its own buckets, the convention that does **not** count a module as
# reaching itself.  The default is the self-counting one, because it is what both live censuses use
# and what a placement argument means -- a declaration put in a file has that file's own contents.
# Accepting both silently is what row 2224 §3.2 forbids: at `2857956` it would accept 546 / 35 / 5
# **and** 549 / 32 / 5 for one sentence, so a stale figure would have two ways to look right.
CENSUS_STRICT = re.compile(r"\bdoes not count\b|\bnot counting\b|\bexcluding itself\b"
                           r"|\bbesides itself\b", re.I)

# Any number word, anywhere in the census sentence.  This is how the buckets the sentence names
# **without** a numeral are accounted for -- `:393`'s *"this file is the one that reaches three"*
# and `:305`'s *"the best ... is three, and only 4 of them manage that"*.  Row 2224 §3.3 asks for
# the remainder to equal what the walk leaves over rather than being inferred from the shortfall,
# and the walk knows both halves: the remainder the sentence implies is `len(universe)` minus the
# numerals it binds, and what the walk leaves over is the sum over the buckets it names in words
# and does not bind.  Requiring those equal is strictly stronger than *the numerals sum to the
# total*, because a bucket the sentence names **nowhere** cannot appear on the walk's side -- so a
# module landing in a bucket above every index the sentence mentions is a MISMATCH here and is
# invisible to the arithmetic, which is row 2220's measured finding.
#
# The scan is deliberately loose in the safe direction: a number word used for something else (the
# `six` of *"reaches all six"*, the `one` inside *"the only one of the 587"*) adds a bucket index to
# the accounted-for set and can only make the check **weaker**, never red against correct prose.
BUCKET_ANY_WORD = re.compile(r"\b([a-z]+)\b", re.I)

# The bucket species' remedy, and it is the opposite of both incumbents'.  `TOTAL_DISPOSITION` and
# `CENSUS_DISPOSITION` both end *"Do not change the numeral"*, because there the risk carried by
# the grammar is that a numeral which is not a module count is being read as one -- the reading is
# what goes wrong, so the way out is to reword.  A bucket figure has already passed four gates
# before it is compared: the sentence spells its subject set's cardinality, the set resolves to
# exactly that many modules of this tree, the universe phrase picks one of two named sets and its
# own numeral agrees with it, and every bucket predicate is in a closed vocabulary.  A figure that
# survives all four and still disagrees with the walk is **stale**, so here the numeral is the thing
# to change.  The reading is still refusable, and the way out is to break a gate rather than to
# post-modify anything: elide the spelled cardinality, or state the bucket without the `N reach`
# spelling, and the sentence goes to `--sweep`.
BUCKET_DISPOSITION = (
    "(this figure passed the subject-set, universe and predicate gates, so the reading is",
    " pinned and the numeral is what is stale: re-run the walk.  To refuse the reading",
    " instead, elide the spelled cardinality or drop the `N reach ...` spelling.)",
)

# And the identity's, which is **not** `BUCKET_DISPOSITION`.  Every other figure this species
# reports is a count, so *re-run the walk* names the repair; the identity is a claim about **which
# module** the top bucket holds, and re-running the walk on a sentence that names the wrong module
# returns the same number it returned before.  Printing the bucket remedy under it would be advice
# that does nothing, which is the defect row 2214 rejected #814 for -- there a census mismatch
# carried the *total's* three suggestions and all three were no-ops.  The refusal route is shared,
# because breaking either gate takes the whole sentence out of this species and the identity with
# it.
IDENTITY_DISPOSITION = (
    "(this one is not a numeral.  The sentence names which module is the top bucket's sole",
    " member and the walk names a different set, so the repair is the **name** -- say it of",
    " the module the walk gives, or drop the claim.  To refuse the reading instead, elide the",
    " spelled cardinality or drop the `N reach ...` spelling.)",
)


def _module_list(mods: list[str], cap: int = 3) -> str:
    """A bounded, backticked rendering of a module list for a report line.

    Capped because a report line is read in a terminal and the population it names is unbounded in
    principle, and **the cap is spoken** -- a truncated list that does not say it was truncated is
    the silent-cap failure `stub_cost`'s comment is about, one line long instead of one mode long.
    """
    if not mods:
        return "nothing"
    shown = ", ".join("`%s`" % m for m in mods[:cap])
    return shown if len(mods) <= cap else "%s and %d more" % (shown, len(mods) - cap)

# What makes a sentence a candidate for `--sweep`.  The word `closure` is the obvious trigger, but
# it is not sufficient: *"`FormalSchemes.Gluing` being upstream of 272 of this tree's 496 modules"*
# is a **reverse**-closure measurement carrying two figures and does not contain the word at all.
# Four further markers are added for that shape and for the counterfactual one -- a project-module
# total, a tree census, `upstream of N` and `PRICE` -- and all of them are assertions about an
# import graph however worded, the last about a graph this tree does not have.
SWEEPABLE = re.compile(r"closure"
                       r"|of (?:this|the) (?:tree|project|library)'s \*{0,2}\d+\*{0,2} modules?"
                       r"|" + TOTAL_UNCHECKED.pattern +
                       r"|" + CENSUS_UNCHECKED.pattern +
                       r"|\bupstream of \*{0,2}\d"
                       r"|" + PRICE.pattern, re.I)

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
    closure* / *reverse closure* occurs in 62 of this tree's files and 228 times in all -- the
    `204` attributed and `24` declined of `--tree`'s header -- and every one of those is in a
    comment, since it is not Lean syntax.  A hit inside code would be reported as a declined claim,
    not silently mis-measured.  Newlines are replaced by spaces rather than removed, so every
    position still maps to a line of the file.

    **This reasoning is `CLOSURE`'s and does not carry to `SWEEPABLE`**, whose trigger is a bare
    `closure` that Lean code really does contain -- see `invisible`, which gates on the comment
    spans this one does not need to.
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


def total_claims(mods: dict[str, str]):
    """Yield every project-module total quoted in the tree, as a dict.

    No attribution runs: the figure's subject is the tree, so there is no module to resolve and no
    way for this species to be *declined* -- it is checked or it is not seen.  That is why the
    grammar rather than the resolver carries the whole risk here, and why `TOTAL` is narrow.

    The scan is over whole files for the reason `claims` gives: *modules under* and *the project's
    modules* are prose, not Lean syntax, so a hit is a sentence wherever it lands.

    **Two patterns can now read one numeral, and the span set is what stops it being counted
    twice.**  Until row 2214 they could not, and this docstring said so: `TOTAL`'s second pattern
    needs the numeral immediately after *the*, and in the first `project's` stands in that slot, so
    ``of the project's **3** modules under `FormalSchemes/` `` was one claim read by the first
    pattern only.  `CENSUS` is the third pattern that docstring said *"would need this sentence
    re-read rather than trusted"*, and re-reading it is what this is: *"the only one of the **3**
    modules under `FormalSchemes/` reaches it"* is read by `CENSUS[0]` **and**, because nothing
    restricts the phrase, by `TOTAL[1]` at the numeral inside it.  Both want `len(mods)`, so the
    verdict is the same either way and only the *count* was ever at risk -- but a figure reported
    twice is a figure whose population moves when somebody rewords a sentence, so the first
    pattern to reach a numeral keeps it.  `TOTAL` is scanned first, which makes the incumbent
    species the one that keeps its own spelling.  The `--selftest` cases *two spellings in one
    sentence* and *a census total in the unrestricted spelling is one claim, not two* are the two
    sides of this.
    """
    for module, path in sorted(mods.items()):
        raw = open(path, encoding="utf-8").read()
        flat = raw.replace("\n", " ")
        taken: list[tuple[int, int]] = []
        for pat, what, how in (
                [(p, "the number of modules under `FormalSchemes/`", TOTAL_DISPOSITION)
                 for p in TOTAL]
                + [(p, "the number of modules under `FormalSchemes/`, as the size of the"
                       " set this sentence is a census of", CENSUS_DISPOSITION)
                   for p in CENSUS]):
            for m in pat.finditer(flat):
                # The numeral's own span, not the phrase's: two spellings of one census overlap in
                # their wording far more often than they overlap on a figure, and it is the figure
                # that must not be counted twice.  No sentence this tree could write separates the
                # two keys -- `CENSUS[0]`'s match always contains `TOTAL[1]`'s numeral when both
                # fire -- so this is the safer spelling of a test equivalent to the phrase-span one
                # rather than a behaviour a fixture can pin, and it is written down here instead.
                span = m.span(1)
                if any(a < span[1] and span[0] < b for a, b in taken):
                    continue
                taken.append(span)
                yield dict(path=path, line=raw[:m.start()].count("\n") + 1, module=module,
                           stated=int(m.group(1)), about=None, kind="total", subject=None,
                           what=what, disposition=how,
                           text=" ".join(flat[m.start():m.start() + 90].split()))


def sentences(raw: str):
    """`(offset, text)` for each sentence of `raw`, over the newline-flattened text."""
    flat = raw.replace("\n", " ")
    pos = 0
    for m in BREAK.finditer(flat):
        yield pos, flat[pos:m.end()]
        pos = m.end()
    yield pos, flat[pos:]


def census_spans(sentence: str) -> list[tuple[int, int]]:
    """The spans of a census sentence this species reads, for `invisible` to blank.

    Shared with `census_claims` so that *what the reading list still carries* and *what the audit
    checks* cannot drift apart -- the failure row 2213 paid for was a per-sentence exclusion hiding
    a figure nobody checked, and the only defence against its mirror image is that one function
    decides both.  Returns `[]` for a sentence with no bucket in it, which is what keeps
    `CENSUS_UNCHECKED`'s *the other N* reading-list entry alive everywhere else in the tree.
    """
    if not BUCKET.search(sentence):
        return []
    spans = []
    for pat in (BUCKET, CENSUS_SUBJECT, CENSUS_OTHER, CENSUS_ALL):
        spans += [m.span() for m in pat.finditer(sentence)]
    return spans


def _identity_is_self(before: str) -> bool:
    """Whether the subject of *the only one of the **N*** is the file the sentence is in.

    By `attribute()`'s rule and not a looser one: collect the self-phrases and the module tokens
    that stand before the phrase and take the **last** of them.  *Is `this file` present anywhere
    earlier* and *is `this file` the nearest thing before the claim* are different questions, and
    they differ on exactly the sentences that name another module in between -- which is the normal
    way to write a comparison:

        This file is a leaf, and `FormalSchemes.X` is the only one of the 10 that reaches all five

    is a claim about `X`.  Reading it as a claim about this file makes `--tree` red on prose that is
    **true**, and a species that can do that has no business failing a build.  Whether a *named*
    module really is the only one is `attribute()`'s kind of question and not this species'.
    """
    anchors = [(m.start(), True) for m in SELF_PHRASE.finditer(before)]
    anchors += [(m.start(), False) for m in MODULE_TOKEN.finditer(before)]
    return bool(anchors) and max(anchors)[1]


def census_claims(mods: dict[str, str]):
    """Yield every tree census whose **buckets** this species can read, as a dict, resolved but
    not yet compared: the subject set, the universe, the bucket numerals with the index each is
    bound to, and the bucket indices the sentence names in words without a numeral.  `audit`
    does the walk and the comparison, exactly as it does for `claims`.

    A record carries `declined` instead when a gate refuses, and the gates are the whole design:
    **this species never guesses.**  Every decline path below is a reading this walk cannot pin,
    and a reading it cannot pin is one it must not go red on -- which is the rule row 2220 exists
    to state and the reason row 2214 left the buckets alone rather than checking them wrongly.

    The scan is sentence-by-sentence rather than over the flattened file, because two of the four
    readings are *positional*: the subject set may be one sentence back, and the bucket words have
    to be counted within the sentence that states them.  `BUCKET` is required in **prose** for the
    reason `invisible` gives about `SWEEPABLE` -- `reaches` is not Lean syntax but a numeral beside
    it in a proof body is not a census either, and a run of tactic script in this report would be
    read as advice about a sentence.
    """
    for module, path in sorted(mods.items()):
        raw = open(path, encoding="utf-8").read()
        masked = code_only(raw)
        sents = list(sentences(raw))
        for i, (off, s) in enumerate(sents):
            buckets = [b for b in BUCKET.finditer(s)
                       if not masked[off + b.start():off + b.end()].strip()]
            if not buckets:
                continue
            rec = dict(path=path, line=raw[:off].count("\n") + 1, module=module, kind="census",
                       subject=None, about=None, disposition=BUCKET_DISPOSITION,
                       text=" ".join(s.split())[:90])
            decline = lambda why: dict(rec, declined=why)
            if CENSUS_STRICT.search(s):
                yield decline("the sentence declares the strict convention for its own buckets,"
                              " which this species does not read")
                continue
            m = CENSUS_SUBJECT.search(s)
            if not m or m.group(1).lower() not in BUCKET_WORD:
                yield decline("no spelled cardinality for the set the census is of")
                continue
            spelled = BUCKET_WORD[m.group(1).lower()]
            # The sentence's own tokens first, then one hop back and only before that sentence's
            # colon -- see the grammar block on why the opener's post-colon tokens are not the
            # subject set.  The checksum decides between the two rather than an order preference:
            # a sentence whose own tokens happen to number `spelled` for an unrelated reason would
            # be read wrongly by an order rule, and here it has to number `spelled` *and* the hop
            # has to not, or the reading is refused below.
            own = sorted(set(MODULE_TOKEN.findall(s)))
            prev = sents[i - 1][1] if i else ""
            opener = prev[:prev.index(":") + 1] if ":" in prev else ""
            hop = sorted(set(MODULE_TOKEN.findall(opener)))
            candidates = [c for c in (own, hop) if len(c) == spelled]
            if len(candidates) != 1:
                yield decline("the set this census is of does not resolve to the %d it spells"
                              " (%d named here, %d in the opener one sentence back)"
                              % (spelled, len(own), len(hop)))
                continue
            subject = candidates[0]
            missing = [c for c in subject if c not in mods]
            if missing:
                yield decline("`%s` is not a module of this tree" % missing[0])
                continue
            other, whole = CENSUS_OTHER.search(s), CENSUS_ALL.search(s)
            if bool(other) == bool(whole):
                yield decline("the set being partitioned is not stated, or is stated twice")
                continue
            # `the other N` excludes exactly one module and the only module this sentence
            # distinguishes is the one whose docstring it is.  The other reading row 2214 names --
            # other than the subject set -- is arithmetically distinguishable now that the subject
            # set has resolved, and it gets this decline rather than a MISMATCH.  Population at
            # `2857956`: **0**.
            stated = int((other or whole).group(1))
            universe = sorted(set(mods) - {module}) if other else sorted(mods)
            if other and stated != len(universe) and stated == len(mods) - len(subject):
                yield decline("*the other* here excludes the set the census is of, not the module"
                              " this docstring is in -- two readings, and this species reads the"
                              " second")
                continue
            bound: dict[int, int] = {}
            for b in buckets:
                word = b.group(2).lower()
                if word not in BUCKET_WORD or BUCKET_WORD[word] > spelled:
                    bound = None
                    yield decline("bucket predicate `%s` is not an index into a set of %d"
                                  % (word, spelled))
                    break
                if BUCKET_WORD[word] in bound:
                    bound = None
                    yield decline("two numerals are bound to the same bucket")
                    break
                bound[BUCKET_WORD[word]] = int(b.group(1))
            if bound is None:
                continue
            yield dict(rec, subject_set=subject, spelled=spelled, universe=universe,
                       stated_universe=stated, buckets=bound,
                       worded={BUCKET_WORD[w.lower()] for w in BUCKET_ANY_WORD.findall(s)
                               if w.lower() in BUCKET_WORD} - set(bound),
                       # `the only one of the N` asserts that the top bucket holds exactly one
                       # module and that it is this one.  Checked by name rather than inferred from
                       # the shortfall, and only when the sentence says *this* of **this** claim --
                       # see `_identity_is_self` for why a self-phrase merely occurring earlier in
                       # the sentence is not enough, and for the fixture that settles it.
                       identity=bool(whole) and _identity_is_self(s[:whole.start()]))


def invisible(mods: dict[str, str]):
    """Every sentence that carries a numeral together with a `SWEEPABLE` marker and that
    `claims()` cannot see at all -- neither attributed nor declined.  Counted, never failed on.

    **The marker has to be in a comment**, and unlike `claims()` this cannot be taken on trust.
    `claims()` scans the whole file and says why that is safe: `CLOSURE` is *forward closure* /
    *reverse closure*, which is not Lean syntax, so a hit is prose wherever it lands.  `SWEEPABLE`
    leads with a bare case-insensitive `closure` instead, and **that is** Lean syntax --
    `AlgebraicClosure`, `integralClosure`.  Without this gate a proof body enters the reading list
    under advice meant for a sentence, and because `BREAK` is `[.;]\\s` and Lean code carries
    almost no sentence terminators, what is printed is a run of tactic script.  Worse, `--tree`'s
    header publishes the count as a coverage figure that reviewers hold fixed across a diff, so
    adding an unrelated algebraic-closure lemma anywhere would move it.

    The gate is on the **match**, not the sentence: a sentence legitimately runs out of a docstring
    into code, since `BREAK` cannot see `-/`.  The numeral is deliberately not gated as well --
    the population *marker in prose, every numeral in code* is empty on this tree, so a second
    clause would be a branch no fixture could reach.
    """
    for module, path in sorted(mods.items()):
        raw = open(path, encoding="utf-8").read()
        masked = code_only(raw)
        for off, s in sentences(raw):
            # A total `TOTAL` reads, or a census total `CENSUS` reads, is checked, so it is not a
            # reason to put its sentence on the reading list -- but it must not hide the sentence's
            # *other* unreadable figures either, which is what a per-sentence gate did until row
            # 2213.  Blanking the spans those species read, at equal length so every offset below
            # still lines up, makes this exclusion per **figure**, exactly as the `CLOSURE` one
            # beside it already is.  Measured at `d699026`: the sentence carrying this tree's one
            # checked total also carries the **140** of *"140 of the 586 modules … carry a redundant
            # import"*, which no species checks, and a per-sentence gate dropped that sentence for
            # it.  `CENSUS` is masked here rather than merely gated because `CENSUS_UNCHECKED`
            # matches the checked spelling too, being a prefix of it (row 2214), so without the
            # mask every checked census total would put its own sentence on the list.
            rest = s
            for pat in TOTAL + CENSUS:
                rest = pat.sub(lambda mm: " " * (mm.end() - mm.start()), rest)
            # And the spans the bucket species reads, on the same per-figure principle and for the
            # same reason: `CENSUS_UNCHECKED` matches every one of them, so without the mask a
            # census whose buckets are now checked would keep putting its own sentence on the
            # reading list.  `census_spans` is empty unless the sentence carries a bucket, which is
            # what leaves *the other N* on the list in the sentences that are not censuses -- and
            # the mask covers the declined censuses too, because a decline is itself a reading list
            # (`--tree`'s `census-declined` block) and a figure read twice is a figure whose
            # population moves when somebody rewords a sentence.
            for a, b in census_spans(rest):
                rest = rest[:a] + " " * (b - a) + rest[b:]
            m = SWEEPABLE.search(rest)
            if not m or not FIGURE.search(rest):
                continue
            if masked[off + m.start():off + m.end()].strip():
                continue
            if MATHLIB.search(s):
                continue
            # The `CLOSURE` exclusion is per sentence for the reason it exists -- a sentence with a
            # closure phrase in it is one `claims` has already seen, attributed or declined -- and
            # for the total species that is wrong: `RefinedOverlapTransition.lean`'s `## Placement`
            # states an unchecked total *and* a reverse-closure claim in one sentence, so the claim
            # beside the total is exactly what hid it from both instruments at once.  It is read per
            # figure, and it is why row 2209 found three numerals rotting under a MISMATCH 0.  A
            # census is in the same position for the same reason and since row 2214 is exempted with
            # it -- a bucket partition beside a closure claim would otherwise be hidden by the claim
            # exactly as the unpinned total was.  Population of *census and closure phrase in one
            # sentence* at `05a5fe2`: **0**; it is here because the mechanism is the one row 2209
            # paid for, not because the tree writes it today.
            # `PRICE` joins the two totals in this exemption rather than being gated by the
            # `CLOSURE` clause above, for the reason that clause's own comment gives and with a
            # population this time: `AwayCompletionAlgHomBasicOpen.lean` states an edge price and
            # the reverse closure it is argued from **in one sentence**, so the claim beside the
            # price is what hid the price -- and the price is the half of that sentence nothing on
            # this tree can check.  Adding the marker without this clause moves nothing at all,
            # which is worth knowing before reading the delta: at `2857956` this is the whole of
            # the +1.
            if CLOSURE.search(rest) and not (TOTAL_UNCHECKED.search(rest)
                                             or CENSUS_UNCHECKED.search(rest)
                                             or PRICE.search(rest)):
                continue
            yield dict(path=path, line=raw[:off].count("\n") + 1, module=module,
                       text=" ".join(s.split()))


def audit(root: str = ".",
          deps: dict[str, set] | None = None) -> tuple[list, list, list, list]:
    """Every claim in the tree, as `(mismatches, declined, size_declined, census_declined)`.

    Mismatches are one list because `--tree` fails on any of them; the three declined populations
    are kept apart because they are different coverage figures and a reader watching one of them
    move should not have the others mixed into it.

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
    size_declined, census_declined = [], []
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
            want = (size(c["module"]) + c["offset"] if kind == "self" else actual) + delta
            if stated != want:
                mismatches.append(dict(
                    c, stated=stated, actual=want, text="%s -- in `%s`" % (quoted, c["text"][:60]),
                    subject=c["module"] if kind == "self" else c["about"],
                    what="the %s closure of `%s`"
                         % (c["kind"], c["module"] if kind == "self" else c["about"])))
    for c in total_claims(mods):
        # `len(mods)` and nothing else: a total has no subject, so neither `deps` nor a claim's
        # convention can move what it should say.  That is also why `--edge` never reports one --
        # an added edge does not add a module -- and why `edge_species` leaves it unclassified.
        if c["stated"] != len(mods):
            mismatches.append(dict(c, actual=len(mods)))
    for c in census_claims(mods):
        if c.get("declined"):
            census_declined.append(c)
            continue
        # The histogram, over the universe the sentence named and under the self-counting
        # convention `CENSUS_STRICT` above is the opt-out from.  `deps` reaches it through
        # `forward`, which is why an `--edge` run moves a bucket at all -- see `edge_cost` for why
        # that mode does not price one.
        top = c["spelled"]
        hit = {m: len((forward[m] | {m}) & set(c["subject_set"])) for m in c["universe"]}
        hist = collections.Counter(hit.values())
        if c["stated_universe"] != len(c["universe"]):
            mismatches.append(dict(c, stated=c["stated_universe"], actual=len(c["universe"]),
                                   what="the size of the set this census partitions"))
        for k, stated in sorted(c["buckets"].items()):
            if stated != hist[k]:
                mismatches.append(dict(c, stated=stated, actual=hist[k],
                                       what="the modules reaching %d of the %d this census is of"
                                            % (k, top)))
        # Row 2224 section 3.3: the buckets the sentence states without a numeral are not inferred
        # from the shortfall, they are read off the walk -- and the sentence has to have *named*
        # them, in words, or the remainder cannot be accounted for.  That is what makes a module
        # landing in a bucket above every index the sentence mentions a MISMATCH here.
        remainder = len(c["universe"]) - sum(c["buckets"].values())
        accounted = sum(hist[k] for k in c["worded"])
        if remainder != accounted:
            mismatches.append(dict(
                c, stated=remainder, actual=accounted,
                what="the buckets this census names in words but not with a numeral"
                     " (indices %s)" % (", ".join(str(k) for k in sorted(c["worded"])) or "none")))
        # The identity, as **two** figures.  *"This module is the only one of the N"* asserts that
        # this file is in the top bucket and that nothing else is, and one comparison of a set
        # against `[module]` collapses them into a line that reads `states 1, walk gives 1`
        # whenever the count is right and the member is wrong -- which is the one population the
        # clause exists for.  Split, each half is a count the reader can act on, and the second
        # names what the walk found, because the repair is a name and the report has to carry it.
        if c["identity"]:
            only = sorted(m for m, n in hit.items() if n == top)
            others = [m for m in only if m != c["module"]]
            if c["module"] not in only:
                mismatches.append(dict(
                    c, stated=1, actual=0, disposition=IDENTITY_DISPOSITION,
                    what="this file among the modules reaching all %d, which this sentence says"
                         " it is the only one of" % top))
            if others:
                mismatches.append(dict(
                    c, stated=0, actual=len(others), disposition=IDENTITY_DISPOSITION,
                    what="the modules besides this one reaching all %d, which this sentence says"
                         " is none -- the walk gives %s" % (top, _module_list(others))))
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
    return mismatches, declined, size_declined, census_declined


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
    exhaustive as a matter of the graph and **0 is never a level**.  A census **bucket** figure is
    the one shape that breaks that sentence, since an edge moves a forward closure and a bucket is
    counted from forward closures; it never reaches here, because `edge_cost` filters it out with
    the argument for doing so beside it.  A claim that lands there is
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

    # A census bucket is the one new-since-row-2224 figure an edge **does** move, and it is
    # deliberately not priced here.  The three species below are exhaustive for **closure** figures
    # -- an import moves a forward closure for the importer and its consumers and a reverse closure
    # for what it brings in -- and a bucket is not one: it is a figure about the whole tree's
    # partition, whose subject is a set of modules and whose universe is every module.  Putting it
    # in the population would print it under `UNCLASSIFIED`, whose own line says *a claim shape
    # nobody has thought about, or a bug here*, which would be false advice about a figure `--tree`
    # checks.  Measured at `2857956`: the edges that move a bucket at all are the ones bringing a
    # member of a live census's subject set into a module that did not reach it, `--edge` is
    # byte-identical on every edge that does not, and the population this filter drops is **0** on
    # `--edge FormalSchemes.RefinedOverlapTransition:FormalSchemes.AwayCongrAlgebraMap` against
    # **9** on `--edge FormalSchemes.AdicRing:FormalSchemes.AwayCompletionUniversal`, where the
    # brought-in module is a member of both live censuses' subject sets.  Naming the number here
    # rather than only in a pull request is the point: the cap is not silent.  If a later row wants
    # these priced, the honest shape is a species of its own with a label of its own, not a fourth
    # meaning for `UNCLASSIFIED`.
    #
    # **`--stub` does price them, and the difference is not a disagreement.** The rule is **which
    # species can name the figure**, not which hypothetical moves it: both move it, and the 9 above
    # is this mode's own count of how many it moves here.  There is nowhere honest to file one --
    # the three species below are exhaustive for *closures*, a bucket is not a closure, and
    # `UNCLASSIFIED` is the only level left.  `stub_species` has a level that fits: a stub grows
    # `len(mods)`, a census's universe is a count of modules, so the figure moves for the same
    # reason the project total's does and stands beside it.  A reader finding one filter and not
    # the other should read this paragraph and `stub_cost`'s together.
    base = {_fingerprint(c) for c in audit(root, real)[0]}
    population = [c for c in audit(root, hypo)[0]
                  if c.get("kind") != "census" and _fingerprint(c) not in base]

    def species(c: dict) -> int:
        return edge_species(c, importer, consumers, brought)

    return dict(importer=importer, imported=imported, adding=adding, brought=sorted(brought),
                # `imported` already reaching `importer` makes the hypothetical graph cyclic, so
                # Lean would refuse the tree this report prices.  A label and never a filter:
                # nothing below is computed differently, because reachability in a cyclic digraph
                # is well defined and every figure here is that digraph's.  A deletion cannot
                # create a cycle, which is why this is read off the addition direction only -- a
                # guard no acyclic tree can observe, pinned by `--selftest` on one that is already
                # cyclic, where *would close a cycle* would be the wrong sentence to print.
                cycle=adding and importer in fwd_real[imported],
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
    if r["cycle"]:
        # At a fixed position, right under `priced by`, because a reader of this report diffs two
        # runs of it and a line that moves is a line that is missed.  The two modules are named
        # on the line above and are deliberately not repeated here: interpolating them makes this
        # the one paragraph of the report whose width is unbounded.
        print("  NOTE                       : the imported module already reaches the importing"
              " one, so this")
        print("                               edge would close an import cycle.  Lean would"
              " refuse the tree")
        print("                               priced below; the figures are that graph's, not a"
              " buildable")
        print("                               project's.")
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


def stub_species(c: dict, reached: set) -> int:
    """Which of the two species a mismatch belongs to, or **0**.

    A stub is a **leaf**: nothing imports it, so no forward closure anywhere can move, and it is a
    new file rather than a longer one, so no size figure can move either.  What is left is a project
    total or tree census -- `len(mods)` went up, so the tree's own count moved, and so did every
    census figure counted against a universe of *all the others*; neither has a subject whose
    position on the tree matters -- and a reverse closure of a module the stub reaches.  The two are
    exhaustive for that reason and **0 is never a level**: a claim landing there is a shape nobody
    has thought about, or a bug in this function.

    A census **bucket** figure is species **1**, beside the project total, and the `kind` test is
    what says so.  It reads `in ("total", "census")` rather than `== "total"` alone because
    `CENSUS[0]`'s total shares `kind="total"` while a bucket, a universe size and an identity carry
    `kind="census"` -- which is why the label has read *a project total or tree census* since before
    the buckets were priced.  A census is **not** a third species: what a stub moves about one is
    the same thing it moves about the tree's own count, namely a figure read off a walk of the whole
    tree rather than off any one module's closure, and giving it a level of its own would say the
    two need different repairs when they do not.  `--edge` is the other way round and
    `edge_species` says why.

    `reached` is checked rather than assumed, which is the whole value of returning 0: a reverse
    closure the stub does not reach cannot have moved, so a mismatch about one is either already on
    the tree -- and then the baseline subtraction should have taken it -- or evidence that something
    above here is wrong.  Keyed on `subject` and not on `about`, for `edge_species`' reason: a
    `self` companion's `about` is the module the sentence is comparing against.
    """
    if c.get("kind") in ("total", "census"):
        return 1
    if c.get("kind") == "reverse" and c.get("subject") in reached:
        return 2
    return 0


def stub_cost(root: str = ".", name: str = "", imports: tuple[str, ...] = ()) -> dict:
    """Price adding module `name`, importing exactly `imports` and nothing else, to `root`'s tree.

    `CONTRIBUTING.md`'s experiment run rather than described -- see the module docstring for why
    this copies the tree where `--edge` does not, and for the two rebuild conventions the report
    prints.  Nothing is written under `root`.
    """
    # Local for the reason the renderer's imports in `selftest` are: no other mode here materialises
    # a tree, and these two are the only lines in this file that could write one anywhere.
    import shutil
    import tempfile

    mods = project_modules(root)
    # Argument checks before the copy, so a mistyped name costs nothing and fails like any other
    # bad argument.  `--stub FormalSchemes.Gluing:…` is the interesting one: a name the tree already
    # has would be **silently overwritten** in the copy, and the report would then price a tree with
    # that module's contents deleted rather than a tree with one module more.
    if not STUB_NAME.fullmatch(name):
        raise SystemExit("`%s` is not a module name under FormalSchemes/" % name)
    if name in mods:
        raise SystemExit("`%s` is already a module of this tree" % name)
    if len(set(imports)) != len(imports):
        raise SystemExit("`%s` cannot import a module twice" % name)
    for i in imports:
        if i not in mods:
            raise SystemExit("`%s` is not a module under FormalSchemes/" % i)

    def rooted(cs: list, at: str) -> list:
        """Every mismatch's `path` made root-relative, with `os.sep` normalised.

        The two audits run under **different roots** and `_fingerprint` leads with `path`, so
        without this the baseline subtraction matches nothing and the price silently swallows every
        MISMATCH the tree already had -- a failure that reads as a large honest answer.  A
        `--selftest` case pins it from the other side, on a tree carrying a wrong figure the stub
        does not move.
        """
        return [dict(c, path=os.path.relpath(c["path"], at).replace(os.sep, "/")) for c in cs]

    with tempfile.TemporaryDirectory() as tmp:
        shutil.copytree(os.path.join(root, "FormalSchemes"), os.path.join(tmp, "FormalSchemes"))
        stub = os.path.join(tmp, *name.split(".")) + ".lean"
        os.makedirs(os.path.dirname(stub), exist_ok=True)
        with open(stub, "w", encoding="utf-8") as f:
            # The import lines and **nothing else**.  A docstring here would make the stub a claim
            # of its own and the price would include it, which is the one way this mode could
            # measure itself.
            f.write("".join("import %s\n" % i for i in imports))
        hypo = project_modules(tmp)
        _forward, reverse = closures(hypo)
        reached = _forward[name]
        population = rooted(audit(tmp)[0], tmp)

    # A census **bucket** figure is priced here, unlike in `--edge`, and the asymmetry is the point
    # rather than an oversight.  It is **not** that an import leaves a census alone: `edge_cost`
    # counts 9 it moves on one edge, and says so.  It is that species 1 here fits a census and
    # `edge_species`' three do not -- the universe grows, the new module lands in some bucket, and
    # it can land in one the sentence names nowhere, which is the project total's own motion at a
    # subject-carrying figure, while an edge moves a bucket without moving any *closure* and the
    # closure species are what `--edge` has.  So these figures are part of what a module costs, and
    # leaving them out understated the price.  Row 2227 lifted the filter this comment used to
    # argue for; the filter's own measurement of what it dropped -- three figures on
    # `--stub FormalSchemes.ZStub:FormalSchemes.RefinedOverlapTransition`, taking it from 44 at 43
    # positions to 47 at 45 -- is now what the mode reports rather than a note beside it.
    base = {_fingerprint(c) for c in rooted(audit(root)[0], root)}
    population = sorted((c for c in population if _fingerprint(c) not in base),
                        key=lambda c: (c["path"], c["line"]))
    files = sorted({c["path"] for c in population})
    edited = [f[:-len(".lean")].replace("/", ".") for f in files]

    def union(modules: list, inclusive: bool, drop: str = "", with_stub: bool = True) -> set:
        """The modules a repair in each of `modules` re-elaborates, unioned.

        `inclusive` counts an edited file as re-elaborating **itself**, which is the convention
        `CONTRIBUTING.md` writes and the one printed first; the strict reading counts only the
        modules that import an edited one.  `with_stub` decides whether the stub -- which is on the
        tree the repairs are made in, but which no repair edits -- is in the answer.  Those two
        flags are the three published figures this mode exists to stop being re-derived.
        """
        out: set = set()
        for m in modules:
            if m == drop:
                continue
            out |= reverse[m]
            if inclusive:
                out.add(m)
        return out if with_stub else out - {name}

    # Sorted so the largest contributor is deterministic on a tie, and by name so that a tie between
    # two files of equal reverse closure does not depend on the walk order.
    by_file = sorted(((f, len([c for c in population if c["path"] == f]), len(reverse[m]))
                      for f, m in zip(files, edited)), key=lambda t: (-t[2], t[0]))
    biggest = by_file[0][0][:-len(".lean")].replace("/", ".") if by_file else ""

    return dict(name=name, imports=list(imports), size=len(mods), hypo_size=len(hypo),
                population=population, files=files, by_file=by_file,
                positions=len({(c["path"], c["line"]) for c in population}),
                species={k: [c for c in population if stub_species(c, reached) == k]
                         for k in (1, 2, 0)},
                # Keyed on the phrase `audit` writes for that finding, which a `--selftest` case
                # pins: rewording it there fails the case rather than silently zeroing this.
                leaf_sentences=len([c for c in population
                                    if "calls a leaf" in (c.get("what") or "")]),
                baseline=len(base), biggest=biggest,
                biggest_size=len(reverse[biggest]) if biggest else 0,
                inclusive=union(edited, True), inclusive_no_stub=union(edited, True,
                                                                      with_stub=False),
                strict=union(edited, False), strict_no_stub=union(edited, False, with_stub=False),
                dropped=union(edited, True, drop=biggest),
                dropped_no_stub=union(edited, True, drop=biggest, with_stub=False))


def report_stub(r: dict) -> None:
    """`--stub`'s report, which is meant to be re-runnable from its own text: the stub, its imports,
    the tree's size with and without it, the price with the convention that counts it named, the
    files with what each one's repair re-elaborates, and the rebuild under both conventions.  Like
    `report_edge` it prints what the tree would say, and comparing that against what a paragraph
    does say is the reader's job."""
    print("stub                         : `%s`, which this tree does not have" % r["name"])
    print("  imports                    : %5d" % len(r["imports"]))
    for m in r["imports"]:
        print("    %s" % m)
    print("  priced by                  : the tree copied to a temporary directory with the stub"
          " written")
    print("                               into the copy; nothing written under this repository")
    print("modules under FormalSchemes/ : %5d   with the stub (%d without it)"
          % (r["hypo_size"], r["size"]))
    print("figure repairs the stub costs: %5d   in %d files, at %d distinct positions -- the"
          % (len(r["population"]), len(r["files"]), r["positions"]))
    print("                                       count is of figures, and one position can carry"
          " two")
    print("  by species                 : %d / %d, unclassified %d   (a project total or tree"
          " census /"
          % tuple(len(r["species"][k]) for k in (1, 2, 0)))
    print("                                a reverse closure of a module the stub reaches)")
    print("    of those, sentences calling their own file a leaf : %d   (rewritten, not renumbered)"
          % r["leaf_sentences"])
    print("  MISMATCHes already on this tree, excluded above : %d" % r["baseline"])
    # The rebuild, under both conventions and with the self-inclusion rule in the **text** rather
    # than only in a comment: three sessions published three different figures for one sentence of
    # this tree, and each of them had walked correctly under a different one of these four readings.
    # The colons are aligned across the block because a reader diffs two runs of this report.
    print("the rebuild those repairs cost, as the union of the edited modules' reverse closures,")
    print("walked on the tree the repairs are made in -- the one with the stub on it:")
    print("  %-48s : %5d   of %d" % ("counting an edited file as re-elaborating itself",
                                      len(r["inclusive"]), r["hypo_size"]))
    print("    %-46s : %5d" % ("without the stub, which no repair edits",
                               len(r["inclusive_no_stub"])))
    print("  %-48s : %5d" % ("counting only modules that import an edited one", len(r["strict"])))
    print("    %-46s : %5d" % ("without the stub", len(r["strict_no_stub"])))
    if r["files"]:
        print("  %-48s : `%s` at %d" % ("the largest single contributor", r["biggest"],
                                        r["biggest_size"]))
        print("  %-48s : %5d   (%d without the stub)"
              % ("the first union without that one file", len(r["dropped"]),
                 len(r["dropped_no_stub"])))
    print("files edited, with each one's own reverse closure -- the rebuild is their union and not")
    print("their sum, so these do not add up:")
    for path, repairs, consumers in r["by_file"]:
        # 65 is the longest path under `FormalSchemes/` at `2857956`; `--edge`'s 58 overflows on
        # four of this tree's files and the columns stop lining up where it does.
        print("    %-65s %3d repairs %5d" % (path, repairs, consumers))
    for k, what in ((1, "total/census"), (2, "reverse     "),
                    (0, "UNCLASSIFIED -- the two species are exhaustive for a leaf, so this is a "
                        "claim shape nobody has thought about, or a bug here")):
        for c in r["species"][k]:
            print("  %s  %s:%d  %s: states %d, the stub would give %d"
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
        mis, dec, _sz, _cd = audit(d)
        check("the walk follows `public import` and both figures of the correct file pass",
              [(m["module"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Top", 9, 3)])
        check("a file with no closure claim reports nothing at all",
              [c for c in mis + dec if c["module"] == "FormalSchemes.Quiet"], [])
        with open(os.path.join(d, "FormalSchemes", "Mid.lean"), encoding="utf-8") as f:
            broken = f.read().replace("(2 counted with itself)", "(7 counted with itself)")
        write("Mid", broken)
        mis, _, _sz, _cd = audit(d)
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
        mis, dec, _sz, _cd = audit(d)
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
        mis, _, _sz, _cd = audit(d)
        check("a file that calls itself a leaf and has a consumer is caught, once",
              [(m["module"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Mid", 0, 1)])
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! `FormalSchemes.Base`'s reverse closure is **2**, 5 before this\n"
                     "file. -/\n")
        mis, _, _sz, _cd = audit(d)
        check("`N before this leaf` also reads `file` and `module`",
              sorted((m["module"], m["stated"], m["actual"]) for m in mis),
              [("FormalSchemes.Mid", 0, 1), ("FormalSchemes.Top", 5, 1)])
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**, and this file is not a leaf. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! `FormalSchemes.Base`'s reverse closure is **2**, 1 before this\n"
                     "module. -/\n")
        mis, _, _sz, _cd = audit(d)
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
        mis, _, _sz, _cd = audit(d)
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
        # `Upstream`'s possessive total is **restricted** (`with a consumer`), so `TOTAL` refuses
        # it and this block stays about `--sweep` alone: an unrestricted `of this tree's N modules`
        # is a checked figure since row 2213, and a fixture whose tree grows from seven files to
        # eight two checks below could not state one truthfully at both sizes.  The restriction is
        # not a dodge -- it is the shape `SWEEPABLE`'s own possessive alternation exists for now
        # that `TOTAL` reads the unrestricted one, and nothing else here pins it.
        write("Upstream",
              "/-! It is upstream of 5 of this tree's 6 modules with a consumer. -/\n")
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

        # A `closure` token in **code**, which no fixture above has: `SWEEPABLE` leads with a bare
        # case-insensitive substring, and `AlgebraicClosure` matches it.  The numeral is what makes
        # this case sighted -- `FIGURE` is the other conjunct, so a code line without one is
        # rejected for a reason that has nothing to do with the gate, and a fixture built that way
        # passes with the gate backed out.  `StructureSheafStalkPowerSeriesUltrapower.lean` is
        # where this really happens and `(2 : AlgInt)` is really how, so that is the shape here.
        # The docstring carries a checked figure too, so the file is visible to `--tree` as well.
        before = [m for m, _ in blind]
        write("Code", "/-! Over nothing: forward closure **0**. -/\n"
                      "theorem two_ne : (2 : AlgebraicClosure Rat) = 2 := rfl\n")
        after = sorted((c["module"], c["text"][:24]) for c in invisible(project_modules(d)))
        check("a `closure` token inside Lean code is not a sentence of the reading list, even "
              "carrying a numeral, and adding a file that has one moves nothing else on it",
              [m for m, _ in after], before)
        check("and the file it is in is still audited: its own checked figure is not a mismatch",
              [(c["module"], c["stated"], c["actual"]) for c in audit(d)[0]], [])

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
        mis, _dec, sdec, _cd = audit(d)
        check("a size claim about another module is attributed to it and passes",
              ([(m["module"], m["stated"], m["actual"]) for m in mis], sdec), ([], []))

        # The wrong answer to reject is the comment-blind one: 6 is what a walk that reads
        # docstrings returns, and it would demand a repair against correct prose.
        write("Says", "/-! Appending to `FormalSchemes.Counted` was the alternative. It is\n"
                      "**%d** lines with **6** declarations. -/\n" % lines)
        mis, _dec, _sdec, _cd = audit(d)
        check("the comment-blind count is reported as a MISMATCH against the checked one",
              [(m["about"], m["noun"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Counted", "declarations", 6, 2)])

        write("Says", "/-! Appending to `FormalSchemes.Counted` was the alternative. It is\n"
                      "**%d** lines with **2** declarations. -/\n" % (lines + 1))
        mis, _dec, _sdec, _cd = audit(d)
        check("a stale line count is caught by the same walk",
              [(m["about"], m["noun"], m["stated"], m["actual"]) for m in mis],
              [("FormalSchemes.Counted", "lines", lines + 1, lines)])

        write("Says", "/-! Nothing here names a module, and something is 12 lines long. -/\n")
        mis, _dec, sdec, _cd = audit(d)
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
        mis, _dec, sdec, _cd = audit(d)
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

    # An edge whose imported end already reaches its importer would close a cycle.  The report
    # labels it; nothing else about the report changes, and that is what these cases pin --
    # a filter here would quietly drop the figures an author pricing a reversal came for.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        write("Bot", "/-! Over nothing: forward closure **0**, reverse closure **2**. -/\n")
        write("Top", "import FormalSchemes.Bot\n"
                     "/-! Over `FormalSchemes.Bot`: forward closure **1**, reverse\n"
                     "closure **0**. -/\n")
        write("Side", "import FormalSchemes.Bot\n"
                      "/-! Over `FormalSchemes.Bot`: forward closure **1**, reverse\n"
                      "closure **0**. -/\n")
        check("the cycle tree is green before any edge", audit(d)[0], [])

        straight = edge_cost(d, "FormalSchemes.Top", "FormalSchemes.Side")
        check("an edge whose imported end does not reach its importer is not a cycle",
              straight["cycle"], False)

        # `Top` already reaches `Bot`, so `Bot` importing `Top` closes one.
        looped = edge_cost(d, "FormalSchemes.Bot", "FormalSchemes.Top")
        check("an edge whose imported end already reaches its importer is one",
              (looped["cycle"], looped["adding"]), (True, True))
        check("and the label does not filter: the cycle edge still prices what it brings in, "
              "what moves and one figure of each species",
              (looped["brought"], looped["moved"], looped["unmoved"], looped["rev_moved"],
               sorted((c["path"].split(os.sep)[-1], c["stated"], c["actual"])
                      for c in looped["population"]),
               {k: len(v) for k, v in looped["species"].items()}, looped["baseline"]),
              (["FormalSchemes.Top"], ["FormalSchemes.Bot", "FormalSchemes.Side"],
               ["FormalSchemes.Top"], ["FormalSchemes.Top"],
               [("Bot.lean", 0, 1), ("Side.lean", 1, 2), ("Top.lean", 0, 2)],
               {1: 1, 2: 1, 3: 1, 0: 0}, 0))

        # A deletion removes an edge, so it can never close a cycle.  Which conjunct excludes
        # this one is worth reading off rather than assuming: `Bot` reaches nothing, so the
        # reachability test is already `False` here and `adding and ...` is not what fires.  The
        # tree that does exercise the direction guard is the cyclic one below, and it is the only
        # shape that can -- which is why that case exists and this one does not stand in for it.
        deleting = edge_cost(d, "FormalSchemes.Top", "FormalSchemes.Bot")
        bot_reaches_top = "FormalSchemes.Top" in deleting["forward"][0]["FormalSchemes.Bot"]
        check("a deletion whose imported end reaches nothing is not a cycle, and it is the "
              "reachability test rather than the direction that says so",
              (deleting["adding"], bot_reaches_top, deleting["cycle"]), (False, False, False))

        # The renderer, which nothing else here reads.  Both of the labels below have been
        # wrong on this tree -- `brings in` was printed in the deletion direction until issue
        # 2195's review -- and neither is visible from `edge_cost`'s return value.
        import contextlib
        import io

        def rendered(r):
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                report_edge(r)
            return buf.getvalue().splitlines()

        check("the NOTE is printed for a cycle edge, directly under `priced by`, and the two "
              "modules are not interpolated into it, so its width is bounded",
              [ln[31:] for ln in rendered(looped)[2:6]],
              ["the imported module already reaches the importing one, so this",
               "edge would close an import cycle.  Lean would refuse the tree",
               "priced below; the figures are that graph's, not a buildable",
               "project's."])
        check("no NOTE on an edge that is not one, and the direction word and the label agree "
              "with `adding` in both directions",
              [[ln for ln in rendered(r)
                if "NOTE" in ln or " gains " in ln or " drops " in ln
                or "brings in" in ln or "takes out" in ln]
               for r in (straight, deleting)],
              [["edge                         : `FormalSchemes.Top` gains `FormalSchemes.Side`",
                "modules the edge brings in   :     1"],
               ["edge                         : `FormalSchemes.Top` drops `FormalSchemes.Bot`",
                "modules the edge takes out   :     1"]])

    # `adding and ...` is the one conjunct of the flag that none of the cases above can observe.
    # On any tree Lean would load, a deletion's imported end does not reach its importer, so the
    # reachability test alone is already `False` there -- and by acyclicity, not by luck: at
    # `2875bd3` it was `False` for all 1247 of this tree's import edges.  The one world where the
    # guard is load-bearing is a real tree that is **already** cyclic, and there the NOTE would be
    # the wrong sentence: the edge does not *close* a cycle, the cycle is there, and deleting the
    # edge may be what breaks it.  So that is the tree this case is built on.  Backing the
    # `adding and` out turns it red and leaves every other case in this file green.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))
        for name, other in (("Ping", "Pong"), ("Pong", "Ping")):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write("import FormalSchemes.%s\n"
                        "/-! A tree Lean would refuse: these two import each other. -/\n" % other)
        check("the cyclic tree quotes no figure, so the case below asserts the flag and nothing "
              "else", audit(d)[0], [])
        cyclic = edge_cost(d, "FormalSchemes.Ping", "FormalSchemes.Pong")
        pong_reaches_ping = "FormalSchemes.Ping" in cyclic["forward"][0]["FormalSchemes.Pong"]
        check("a deletion is not labelled a cycle even where the imported end does reach the "
              "importing one, which is the only shape that guard is visible on",
              (cyclic["adding"], pong_reaches_ping, cyclic["cycle"]), (False, True, False))

    # `--edge`'s argument, which is the other thing a report can be silently wrong about.  The
    # empty string used to be **falsy** at `main`'s branch and fall through to the tree audit:
    # output byte-identical to `--tree`'s, and `--tree`'s exit code, from a flag asking for
    # something else entirely.  `main` tests `is not None` now and this is the gate it reaches.
    def edge_arg(a):
        try:
            return parse_edge(a)
        except SystemExit as e:
            return str(e)
    usage = "--edge takes `FormalSchemes.A:FormalSchemes.B`"
    check("a well-formed edge argument splits, and every malformed one is refused by name -- "
          "the empty string included, which is the one that used to run a different mode",
          [edge_arg(a) for a in ("FormalSchemes.A:FormalSchemes.B", "", "FormalSchemes.A",
                                 "A:B:C", ":")],
          [("FormalSchemes.A", "FormalSchemes.B"), usage, usage, usage, ("", "")])

    # ...and the same through `main`, because `parse_edge` alone does not pin the branch that
    # used to skip it.  A synthetic tree as the working directory is what makes this cheap: on
    # the falsy-test this ran a full audit of whatever `.` happened to be, and the check is that
    # it no longer looks at `.` at all.  No build and no repository state, as above.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))
        with open(os.path.join(d, "FormalSchemes", "Only.lean"), "w", encoding="utf-8") as f:
            f.write("/-! Over nothing: forward closure **0**. -/\n")
        argv, cwd = sys.argv, os.getcwd()
        try:
            os.chdir(d)
            got = []
            for a in ("", "FormalSchemes.Only"):
                sys.argv = ["closure_audit.py", "--edge", a]
                try:
                    got.append(main())
                except SystemExit as e:
                    got.append(str(e))
        finally:
            sys.argv = argv
            os.chdir(cwd)
        check("`--edge ''` is refused by `main` rather than falling through to the tree audit, "
              "which it used to run and report under a flag asking for something else",
              got, [usage, usage])

    # Project totals, which are their own species since row 2209 and were unreachable before it.
    # Every case below is a shape that really occurs on this tree or a shape one clause of the
    # grammar exists to refuse; the tree is three modules, so the total to state is **3**.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        LEAF = ("import FormalSchemes.Mid\n"
                "/-! A leaf over `FormalSchemes.Mid`: forward closure **2**, reverse closure\n"
                "**0**. -/\n")

        # `Mid` states the total in the spelling this tree writes, in a sentence carrying **no**
        # closure phrase at all -- `RefinedOverlapTransition.lean:107`'s shape, and the reason the
        # species cannot be a companion.  `Top` states it *before* the figure of the claim in its
        # own sentence, which is the other position out of a companion's reach (`:118`'s shape,
        # except that this one is in the checked spelling).
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **2**. -/\n")
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  It is one of the **3** modules under `FormalSchemes/` today. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! A leaf over `FormalSchemes.Mid`: editing 2 of the **3** modules under\n"
                     "`FormalSchemes/` re-elaborates this file, whose forward closure is **2**,\n"
                     "and its reverse closure is **0**. -/\n")
        check("a total in the tree's own spelling is checked in a sentence with no closure claim, "
              "and in one where it stands before the claim's own figure",
              (audit(d)[0], sorted((c["module"], c["stated"])
                                   for c in total_claims(project_modules(d)))),
              ([], [("FormalSchemes.Mid", 3), ("FormalSchemes.Top", 3)]))
        check("and a checked total is not on the reading list as well",
              [c["module"] for c in invisible(project_modules(d))], [])

        # From here `Top` carries no total, so every case below reports `Mid`'s and nothing else.
        write("Top", LEAF)

        # The positive control, which a `--selftest` fixture of the grammar alone cannot stand in
        # for: a stale total is a MISMATCH, at its own line, with no subject and its own `what`.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  It is one of the **9** modules under `FormalSchemes/` today. -/\n")
        check("a stale project total is a MISMATCH against the walk, at its own line",
              [(c["path"].split(os.sep)[-1], c["line"], c["stated"], c["actual"],
                c["subject"], c["what"]) for c in audit(d)[0]],
              [("Mid.lean", 3, 9, 3, None, "the number of modules under `FormalSchemes/`")])

        # The incumbent spelling `CONTRIBUTING.md` documents, which was a companion until this row:
        # it is checked in the same place, and now also where no claim hosts it.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**, which is 1 of the project's **3** modules. -/\n")
        check("the documented `of the project's N modules` spelling is still checked",
              (audit(d)[0], [c["stated"] for c in total_claims(project_modules(d))]), ([], [3]))
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  This is 1 of the project's **9** modules. -/\n")
        check("and stale in that spelling is a MISMATCH too, from a sentence of its own",
              [(c["line"], c["stated"], c["actual"]) for c in audit(d)[0]], [(3, 9, 3)])

        # Two spellings in one sentence are two claims, read independently: neither pattern
        # shadows the other, and a sentence in both is not a numeral counted twice, because the two
        # cannot read one numeral -- `total_claims` says why, and this is the case that would break
        # if a third pattern made them able to.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**, 1 of the project's **3** modules, which is the **3** modules under\n"
                     "`FormalSchemes/` today. -/\n")
        check("two spellings in one sentence are two claims and neither shadows the other",
              (audit(d)[0], [c["stated"] for c in total_claims(project_modules(d))]), ([], [3, 3]))
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**, 1 of the project's **9** modules, which is the **3** modules under\n"
                     "`FormalSchemes/` today. -/\n")
        check("and only the stale one of the two is reported",
              [(c["stated"], c["actual"]) for c in audit(d)[0]], [(9, 3)])

        # A **tree census** (row 2214).  `the only one of the N modules under `FormalSchemes/`` is
        # the one census spelling checked, and the relative clause after the path is why it needs a
        # species of its own: it restricts *the only one*, not *the N modules*, so `TOTAL[1]`'s
        # guard refuses a true total there.  The case below asserts both halves at once -- one claim
        # from `CENSUS`, and `TOTAL` alone yielding nothing for the same sentence.
        CENSUS_WHAT = ("the number of modules under `FormalSchemes/`, as the size of the set this"
                       " sentence is a census of")
        CENSUS_FIXTURE = ("import FormalSchemes.Base\n"
                          "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                          "**1**.  This module is the only one of the **3** modules under\n"
                          "`FormalSchemes/` that reaches `FormalSchemes.Base` twice. -/\n")
        write("Mid", CENSUS_FIXTURE)
        check("a census total pinned by the path is checked, and the clause after the path does "
              "not refuse it",
              (audit(d)[0], [(c["stated"], c["what"])
                             for c in total_claims(project_modules(d))],
               [any(p.search("the only one of the **3** modules under `FormalSchemes/` that r")
                    for p in TOTAL)]),
              ([], [(3, CENSUS_WHAT)], [False]))
        check("and a checked census total does not put its own sentence on the reading list",
              [c["module"] for c in invisible(project_modules(d))], [])

        # The positive control row 2214 §3 asks for in terms: a census sentence true at N modules, a
        # module added, and the instrument going red.  The stale numeral is the census total and
        # nothing else moves, because the added module reaches none of the three.
        write("Extra", "/-! Over nothing: forward closure **0**, reverse closure **0**. -/\n")
        check("adding a module falsifies a census total and `--tree` goes red",
              [(c["line"], c["stated"], c["actual"], c["what"]) for c in audit(d)[0]],
              [(3, 3, 4, CENSUS_WHAT)])

        # The remedy that red prints, which is the census's and not the total's.  Post-modifying the
        # noun phrase -- what the total's line tells an author to do -- is a no-op on a census,
        # because `CENSUS[0]` carries no trailing guard; printing the total's line here would leave
        # whoever tripped it with three edits that all stay red and no fourth suggestion.
        check("and the remedy it prints is the census's, not the total's",
              ([c["disposition"] for c in audit(d)[0]],
               CENSUS_DISPOSITION == TOTAL_DISPOSITION),
              ([CENSUS_DISPOSITION], False))
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  The **3** modules under `FormalSchemes/` carry a docstring. -/\n")
        check("and a stale *total* in the same tree prints the total's, which for a total works",
              [c["disposition"] for c in audit(d)[0]], [TOTAL_DISPOSITION])
        write("Mid", CENSUS_FIXTURE)
        os.remove(os.path.join(d, "FormalSchemes", "Extra.lean"))
        check("and removing it again is green, so that case is the module and not the prose",
              audit(d)[0], [])

        # The dedup `total_claims` now carries.  With **no** clause after the path, `TOTAL[1]` reads
        # the same numeral as `CENSUS[0]`, and both want `len(mods)` -- so the verdict never
        # differed and only the *count* did.  The first pattern to reach the numeral keeps it, and
        # `TOTAL` is scanned first, so the `what` here is the total's and not the census's.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  This module is the only one of the **3** modules under\n"
                     "`FormalSchemes/` reaches `FormalSchemes.Base` twice. -/\n")
        check("a census total in the unrestricted spelling is one claim, not two",
              (audit(d)[0], [(c["stated"], c["what"])
                             for c in total_claims(project_modules(d))]),
              ([], [(3, "the number of modules under `FormalSchemes/`")]))

        # `the other **N**` is the census total this row **declines** to check, in every spelling
        # including the pinned one, because `the other` needs an antecedent for what is excluded and
        # no regex has it.  The disposition is the reading list, and that is the whole of goal 2.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  The best any of the other **2** modules under `FormalSchemes/`\n"
                     "does is one. -/\n")
        check("`the other N` is not checked even pinned to the path, and it is on the reading list",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # The elided spelling, which is the one the tree actually writes and the reason goal 1's
        # choice has population 0 either way: with the noun gone there is nothing pinning the count
        # to the module set, and *"the only one of the **6** imports"* is the same words.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  This module is the only one of the **3** that reaches\n"
                     "`FormalSchemes.Base` twice. -/\n")
        check("a census total with the noun elided is not checked, and it is swept",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # The negative controls row 2214 §3 names: the same words about something that is **not**
        # the module set.  Neither is checked -- which is the failure goal 1 exists to avoid -- and
        # both are on the reading list, which costs nothing because the list is read and not failed
        # on.  Population of either shape under `FormalSchemes/` at `05a5fe2`: **0**.
        #
        # The row spells the first one *"the other **3** declarations in this file"*.  `sections`
        # stands in for `declarations` here because `N declarations` is the `SIZE` species' own noun
        # phrase, so the row's literal wording is read as a **size** claim about
        # `FormalSchemes.Base` and reports a size MISMATCH rather than nothing -- a correct reading
        # by a different species, and one that would make this case assert the wrong thing.
        for census in ("the other **3** sections in this file are about the base",
                       "it is the only one of the **6** imports that is not transitive"):
            write("Mid", "import FormalSchemes.Base\n"
                         "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                         "**1**.  %s. -/\n" % census)
            check("`%s…` is not a tree census" % census[:34],
                  (audit(d)[0], list(total_claims(project_modules(d)))), ([], []))

        # A **subtree** census is the same words about a subset of the tree, and the path
        # alternation is what refuses it -- the same clause, for the same reason, as in `TOTAL[1]`.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  This module is the only one of the **2** modules under\n"
                     "`FormalSchemes/Sub` that reaches `FormalSchemes.Base` twice. -/\n")
        check("a census of a subtree is not a census of the tree",
              (audit(d)[0], list(total_claims(project_modules(d)))), ([], []))

        # And the bare spelling of that deeper path, which needs its own case for the reason
        # `TOTAL[1]`'s pair does: the backticked fixture above refuses `FormalSchemes/Sub` because
        # the *opening* backtick is not what the unbackticked branch starts with, so it does not
        # pin that branch's `(?![A-Za-z])` at all.  Without the guard, *FormalSchemes/Sub* reads as
        # the tree.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  This module is the only one of the **2** modules under\n"
                     "FormalSchemes/Sub that reaches `FormalSchemes.Base` twice. -/\n")
        check("a census of a subtree with the path unbackticked is not one either",
              (audit(d)[0], list(total_claims(project_modules(d)))), ([], []))

        # The bucket figures.  **Row 2224 rewrote this case and the one below it, and the rewrite is
        # the finding rather than a repair.**  They were written to assert that a bucket figure is
        # nobody's checked species and is on `--sweep` instead, on the ground that a partition needs
        # the instrument to know *which* modules the sentence partitions.  It can now -- when the
        # sentence spells that set's cardinality -- and neither of these two sentences does, so
        # neither is checked here either.  What changed is **where the unread figure is read**: a
        # sentence carrying a bucket is a sentence `census_claims` has seen, so `census_spans` masks
        # its bucket span and it moves off `--sweep` and into `--tree`'s `census-declined` block,
        # which names the reason.  That is the one-reading-list-per-figure rule `invisible`'s own
        # docstring states for `claims` -- *neither attributed nor declined* -- applied to the new
        # species, and it is a relocation and not a loss: both counts are published in a header.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  Of the rest, **1** reaches none and **1** reaches exactly one. -/\n")
        check("bucket figures with no spelled cardinality are still not checked, and have moved "
              "from --sweep to the census decline block, which names why",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))],
               [(c["module"], c["declined"]) for c in audit(d)[3]]),
              ([], [], [],
               [("FormalSchemes.Mid",
                 "no spelled cardinality for the set the census is of")]))

        # And what makes the loose `N reach` marker load-bearing rather than merely equivalent on
        # this tree: *"**1** reaches it"* is a bucket predicate worded the way the next author will
        # word it, and an alternation of *none* / *exactly one* / *two* would not have it.  The two
        # spellings put the same two sentences on this tree's list today, so the live measurement
        # cannot tell them apart and this case is the only thing that does.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  Of the rest, **1** reaches it and the last does not. -/\n")
        check("a bucket predicate not worded `reaches none` is seen by the new species too, so it "
              "declines with a reason instead of leaving both lists",
              (audit(d)[0], [c["module"] for c in invisible(project_modules(d))],
               [c["declined"] for c in audit(d)[3]]),
              ([], [], ["no spelled cardinality for the set the census is of"]))

        # And the exemption from the per-sentence `CLOSURE` exclusion, which is row 2209's mechanism
        # applied to this species: a census beside a closure claim would otherwise be hidden by the
        # claim, which is exactly how the unpinned total rotted.  Population on this tree: 0.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1** and reverse closure\n"
                     "**1**, and the best any of the other **2** does is one. -/\n")
        check("a census sharing its sentence with a closure claim is still on the reading list",
              (audit(d)[0], [c["module"] for c in invisible(project_modules(d))]),
              ([], ["FormalSchemes.Mid"]))

        # From here on the totals block's own fixture is restored, so the cases below are unchanged.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  It is one of the **3** modules under `FormalSchemes/` today. -/\n")

        # The negative controls, which are where the boundary was drawn.  A subset count and a
        # subtree count are the same words about something that is not the tree; both are refused,
        # and both land on the reading list instead, which is the disposition the row asked for.
        # The subset count shares its sentence with a checked closure claim, which is `:118`'s
        # shape and the only shape the per-figure reading of the `CLOSURE` exclusion is visible on.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1** and reverse closure\n"
                     "**1**, and 1 of the **2** modules that import it is this one. -/\n")
        check("a subset count in the same words is not a project total",
              (audit(d)[0], list(total_claims(project_modules(d)))), ([], []))
        check("and it is on the reading list rather than invisible, though the closure claim in "
              "its own sentence is checked",
              [(c["module"], "modules that import it" in c["text"])
               for c in invisible(project_modules(d))],
              [("FormalSchemes.Mid", True)])
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  It is 1 of the **2** modules under `FormalSchemes/Tate`. -/\n")
        check("a subtree count is not a project total either",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # `under` with no path is the incumbent grammar's reading and is refused now, which is the
        # one decision row 2209 left open.  The figure is deliberately **wrong** for this tree, so
        # loosening the clause back does not pass quietly: it reports a MISMATCH against prose that
        # is measuring something else.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**, counted over the **2** modules under it. -/\n")
        check("`under` with no path is not a project total, and it is on the reading list",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # The bare spelling of a deeper path, which the backticked alternative cannot reach and so
        # needs its own case: without `(?![A-Za-z])` on that branch, *FormalSchemes/Tate* reads as
        # the tree.  The backticked fixture above does not pin this clause -- it is refused there
        # because the *opening* backtick is not what the bare branch starts with.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  It is 1 of the **2** modules under FormalSchemes/Tate. -/\n")
        check("a subtree count with the path unbackticked is not a project total either",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # The other half of the boundary, and the one the first cut of this row left open: a
        # restricting clause **after** the path is the same subset-in-the-same-words shape as
        # *under it* before it, and the prose here is **true** -- the reverse closure of
        # `FormalSchemes.Base` really is the two other modules -- so a grammar that read its
        # numeral as the total would report a MISMATCH against a correct sentence.  Both the
        # relative-pronoun and the participial spelling are refused, and both land on the reading
        # list, which is where a total this grammar declines to read belongs.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  Exactly the **2** modules under `FormalSchemes/` that import\n"
                     "`FormalSchemes.Base` pay for an edit there. -/\n")
        check("a clause restricting the path is not a project total, and it is on the reading list",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  Exactly the **2** modules under `FormalSchemes/` importing\n"
                     "`FormalSchemes.Base` pay for an edit there. -/\n")
        check("a participle restricting the path is refused the same way",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # The path without backticks, which is how prose outside a docstring writes it -- row 2209's
        # own title, for one -- and it is the same claim.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  It is one of the **9** modules under FormalSchemes/ today. -/\n")
        check("the path is read with or without its backticks",
              [(c["stated"], c["actual"]) for c in audit(d)[0]], [(9, 3)])

        # Row 2213's own fixture, and the boundary `RESTRICTION` was widened to draw.  The sentence
        # is **true** -- the reverse closure of `FormalSchemes.Base` really is the two other modules
        # -- so reading its **2** as the tree's count is a MISMATCH against correct prose, which is
        # the one outcome this species cannot let happen: it has no decline.  A bare preposition
        # after the path is the shape row 2209 shipped with and named as its residue.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  Exactly the **2** modules under `FormalSchemes/` with a redundant\n"
                     "import pay for an edit there. -/\n")
        check("a bare preposition restricting the path is not a project total, and it is on the "
              "reading list",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # A **past** participle is the other half of the participial shape, and the one that reads
        # as ordinary prose on this tree (*"#807's 17 repaired files"*).  `\w+ed` refuses a
        # preterite main verb with it, which is a total merely swept -- the safe direction, and the
        # reason the positive control two cases below has to be here rather than assumed.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  The **2** modules under `FormalSchemes/` repaired by #807 pay for\n"
                     "an edit there. -/\n")
        check("a past participle restricting the path is refused too, and swept",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # The positive control the narrowing owes: a real total in the **same words**, distinguished
        # only by what follows the path being a finite verb.  A narrowing demonstrated only by what
        # it refuses has not been demonstrated.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  The **3** modules under `FormalSchemes/` carry a docstring. -/\n")
        check("a finite verb after the path leaves the total checked, in the same words the two "
              "cases above are refused in",
              (audit(d)[0], [c["stated"] for c in total_claims(project_modules(d))],
               [c["module"] for c in invisible(project_modules(d))]), ([], [3], []))

        # The other side of that control, and the reason the preposition list is the *restrictive*
        # half of the closed class rather than all of it: an anchor is not a restriction, and
        # `CONTRIBUTING.md` asks authors to write one.  `at` is deliberately absent from the guard.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  The **3** modules under `FormalSchemes/` at that commit are\n"
                     "these. -/\n")
        check("a commit anchor after the path is not a restriction and the total stays checked",
              (audit(d)[0], [c["stated"] for c in total_claims(project_modules(d))]), ([], [3]))

        # `TOTAL[0]` carried no guard at all until row 2213, on either side of its possessive, and
        # row 2209's widening of it to `**` and to whole files is what made that reachable: at
        # `267efe3` the bolded spelling could not match and the unbolded one only in a companion's
        # window.  Same shape, same sentence, same disposition as the path's.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  1 of the project's **2** modules that import it is this one. -/\n")
        check("a clause restricting the possessive is refused as well, and swept",
              (audit(d)[0], list(total_claims(project_modules(d))),
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [], ["FormalSchemes.Mid"]))

        # The possessive is one spelling, not the project's plus two swept ones.  `SWEEPABLE` has
        # always listed all three; `TOTAL` read only `the project's` until row 2213.
        for possessive in ("this tree's", "the library's", "this project's"):
            write("Mid", "import FormalSchemes.Base\n"
                         "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                         "**1**.  That is 1 of %s **3** modules. -/\n" % possessive)
            check("`of %s N modules` is a checked total too" % possessive,
                  (audit(d)[0], [c["stated"] for c in total_claims(project_modules(d))],
                   [c["module"] for c in invisible(project_modules(d))]), ([], [3], []))
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  That is 1 of this tree's **9** modules. -/\n")
        check("and stale in a newly read possessive is a MISMATCH, not a silent widening",
              [(c["line"], c["stated"], c["actual"]) for c in audit(d)[0]], [(3, 9, 3)])

        # The two shapes no regex separates from a finite verb, and the disposition that replaces a
        # decline path for them: `that` or `that are` turns each into a relative clause the guard
        # does refuse.  Both halves are asserted, because the residue without its remedy is a note
        # and the remedy without the residue is untestable.
        ADJ = ("import FormalSchemes.Base\n"
               "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
               "**1**.  The **2** modules under `FormalSchemes/` %sreachable from it pay\n"
               "for an edit there. -/\n")
        write("Mid", ADJ % "")
        check("an adjective phrase after the path is the residue no regex settles: still read",
              [(c["stated"], c["actual"]) for c in audit(d)[0]], [(2, 3)])
        write("Mid", ADJ % "that are ")
        check("and inserting `that are` is the one-clause disposition, with no numeral touched",
              (audit(d)[0], [c["module"] for c in invisible(project_modules(d))]),
              ([], ["FormalSchemes.Mid"]))
        ZERO = ("import FormalSchemes.Base\n"
                "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                "**1**.  The **2** modules under `FormalSchemes/` %s`FormalSchemes.Base`\n"
                "reaches pay for an edit there. -/\n")
        write("Mid", ZERO % "")
        check("a zero relative after the path is the other residue: still read",
              [(c["stated"], c["actual"]) for c in audit(d)[0]], [(2, 3)])
        write("Mid", ZERO % "that ")
        check("and inserting `that` disposes of it the same way",
              (audit(d)[0], [c["module"] for c in invisible(project_modules(d))]),
              ([], ["FormalSchemes.Mid"]))

        # The checked-total exclusion in `invisible` is per **figure** since row 2213.  This is the
        # case a per-sentence gate fails: the sentence's total is checked, and the delta beside it
        # (*"from 1 to 2"*) is a figure no species reads, so the sentence belongs on the reading
        # list for the delta and not in spite of it.  The case above -- *a checked total is not on
        # the reading list as well* -- is the other half, and both are needed: a gate that never
        # fires and a gate that always fires each pass one of them.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**1**.  Importing it would take the closure from 1 to 2 across the **3**\n"
                     "modules under `FormalSchemes/`. -/\n")
        check("a checked total does not hide the unreadable figure beside it in its own sentence",
              (audit(d)[0], [c["stated"] for c in total_claims(project_modules(d))],
               [c["module"] for c in invisible(project_modules(d))]),
              ([], [3], ["FormalSchemes.Mid"]))

    # `--edge` and a total: the figure is wrong whatever the edge is, so it is the baseline's and
    # never the edge's, and it leaves `unclassified` empty rather than filling it.  An edge cannot
    # add a module -- that is the whole argument for reading a total against `len(mods)` alone --
    # and this is the case that checks it rather than asserting it.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **1**. -/\n")
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure\n"
                     "**0**.  It is one of the **9** modules under `FormalSchemes/`. -/\n")
        write("Side", "/-! Over nothing: forward closure **0**, reverse closure **0**. -/\n")
        check("the total is the only thing wrong with the tree the edge is priced against",
              [(c["path"].split(os.sep)[-1], c["stated"], c["actual"]) for c in audit(d)[0]],
              [("Mid.lean", 9, 3)])
        r = edge_cost(d, "FormalSchemes.Side", "FormalSchemes.Mid")
        check("a stale total is the baseline's mismatch and not the edge's, and nothing the edge "
              "falsifies is left unclassified",
              (r["baseline"], sorted((c["path"].split(os.sep)[-1], c["stated"], c["actual"])
                                     for c in r["population"]),
               {k: len(v) for k, v in r["species"].items()}),
              (1, [("Base.lean", 1, 2), ("Mid.lean", 0, 1), ("Side.lean", 0, 2)],
               {1: 1, 2: 0, 3: 2, 0: 0}))

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

    # The **report writer** (row 2218), which until this row no case here read.  `main`'s three
    # remaining print loops -- the per-mismatch block with its disposition lines, `declined` and
    # `size-declined` -- were the only part of this file no fixture observed, and the gap was never
    # a missing harness: both halves of one already existed above.  `report_edge` is rendered
    # through `contextlib.redirect_stdout` in the `--edge` block, and `main()` is already called
    # under a synthetic working directory with `sys.argv` and `os.getcwd()` restored in a `finally`.
    # This composes those two and adds nothing else.  The imports are local again rather than
    # hoisted, for the reason the first pair are: nothing outside `--selftest` renders anything.
    import contextlib
    import io

    def tree_report(root: str, *mode: str) -> tuple[int, list[str]]:
        """A mode's own stdout on the tree at `root`, as `(exit code, lines)`; `--tree` by default.

        Through `main` rather than through `audit`, because here the text *is* the subject and the
        exit code comes free.  `os.sep` is normalised so a case can quote a rendered path without
        assuming the platform, exactly as the `split(os.sep)[-1]` cases above do.

        `mode` was added by row 2221 for `--stub`, whose report is read the same way; every call
        site written for `--tree` is unchanged by it, which is why it is a default and not a
        parameter the existing cases had to grow.
        """
        argv, cwd, buf = sys.argv, os.getcwd(), io.StringIO()
        try:
            os.chdir(root)
            sys.argv = ["closure_audit.py"] + list(mode or ("--tree",))
            with contextlib.redirect_stdout(buf):
                rc = main()
        finally:
            sys.argv = argv
            os.chdir(cwd)
        return rc, [ln.replace(os.sep, "/") for ln in buf.getvalue().splitlines()]

    def rows(lines: list[str]) -> list[str]:
        """The report from its first `MISMATCH` **row** onwards -- what `audit`'s return value
        cannot show, and where *which line sits under which* is the claim.

        The header's count line and a report row both open `  MISMATCH  `; the row is the one that
        continues with a path, which is what the prefix here tests rather than the keyword.
        """
        at = [i for i, ln in enumerate(lines) if ln.startswith("  MISMATCH  FormalSchemes/")]
        return lines[at[0]:] if at else []

    # Goal 1's tree carries a stale **total** *and* a stale closure figure, and the total is in the
    # file that sorts **first**, which is the whole design of the fixture rather than an accident:
    # the report is sorted by path, so with the total last, printing the advisory per mismatch and
    # printing it once at the foot produce byte-identical output and the case cannot tell them
    # apart.  With the total first they differ, and that is the mutation row 2218 §3 names third.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure"
                     " **9**. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! Over `FormalSchemes.Mid`: forward closure **2**, reverse closure"
                     " **0**. -/\n")
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **2**.  It is one"
                      " of the\n**9** modules under `FormalSchemes/`. -/\n")
        # The block by value, which pins five things no single assertion could: the advisory's
        # **wording**, that it sits directly under the total's own two lines, that it sits *above*
        # the next mismatch rather than at the foot, that the closure mismatch carries none, and the
        # continuation lines' indentation, which is what keeps it readable under a file name.  Row
        # 2218 §3 asks for the text and not the presence, and the precedent is the two `report_edge`
        # cases above: the defect they were written for was a wrong *word* in a line whose presence
        # was never in doubt.
        rc, lines = tree_report(d)
        check("a stale total prints its three advisory lines directly under its own text and above "
              "the next mismatch, which carries none",
              (rc, rows(lines)),
              (1,
               ["  MISMATCH  FormalSchemes/Base.lean:1  the number of modules under"
                " `FormalSchemes/`: states 9, walk gives 3",
                "            the **9** modules under `FormalSchemes/`. -/",
                "            (if that numeral is not the tree's module count, the sentence is"
                " right and the reading is",
                "             wrong: post-modify the noun phrase -- `that`, `which`, a participle"
                " or `with` -- and it",
                "             goes to --sweep instead.  Do not change the numeral.)",
                "  MISMATCH  FormalSchemes/Mid.lean:2  the reverse closure of `FormalSchemes.Mid`:"
                " states 9, walk gives 1",
                "            reverse closure **9**. -/"]))

        # The same tree with that total written as a **census**, which is the case that separates
        # *the printer prints the claim's own disposition* from *the printer prints the total's*.
        # The row 2214 cases above assert which disposition a claim carries and that the two differ;
        # this is the only case that reads either of them through `main`, so a printer hard-coding
        # `TOTAL_DISPOSITION` passes every one of those and fails only here.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **2**.  It is the"
                      " only\none of the **9** modules under `FormalSchemes/` that reaches"
                      " none. -/\n")
        check("and a stale census prints the census's advisory in the same position, not the "
              "total's",
              rows(tree_report(d)[1])[2:5],
              ["            (if that numeral is not the tree's module count, the sentence is right"
               " and the reading is",
               "             wrong: post-modifying it does not help here -- elide the noun (`the"
               " only one of the N`)",
               "             or name the subset, and it goes to --sweep instead.  Do not change"
               " the numeral.)"])

        # And the gate from the other side.  The closure mismatch is left in place deliberately, so
        # the report is still non-empty and still exits 1: the same case on a green tree would pass
        # with the advisory deleted, printed twice, or printed under every mismatch there is.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **2**. -/\n")
        rc, lines = tree_report(d)
        check("no advisory anywhere in a report whose only mismatch is a closure figure, which is "
              "the species that can be declined and therefore needs none",
              (rc, rows(lines),
               [ln for ln in lines if "post-modif" in ln or "change the numeral" in ln]),
              (1,
               ["  MISMATCH  FormalSchemes/Mid.lean:2  the reverse closure of `FormalSchemes.Mid`:"
                " states 9, walk gives 1",
                "            reverse closure **9**. -/"], []))

    # Goal 2: the `declined` and `size-declined` loops.  One tree carries a mismatch, a declined
    # closure claim and a declined size claim at once, because the **order** of the three blocks is
    # what a reader of a red run relies on and no other case here observes it.  `size_declined`'s
    # population on this tree is **0 or 1** depending on the head -- 0 at `75e9484`, and 1 with PR
    # #820 on top of it, which adds a `+5` / `+6` declaration delta whose anchor is an anaphor --
    # so the tree is not a reliable exercise of that line either way, and this fixture is.  A
    # transposed `%s` there would otherwise ship on a run that happened to have nothing declined.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: the reverse closure of `FormalSchemes.Mid`\n"
                     "is **1** and its forward closure is **1** module. -/\n")
        write("Says", "/-! Nothing here names a module, and something is **12** lines long. -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! Over `FormalSchemes.Mid`: forward closure **2**, reverse closure"
                     " **0**. -/\n")
        # Row 2225 goal 4.  A second declined claim, in a file sorting **above** `Mid.lean` and with
        # a different reason, so the block below has an order to get wrong.  It imports nothing, so
        # `FormalSchemes.Base`'s reverse closure -- the mismatch this fixture turns on -- is
        # still 2.
        #
        # **What this pins is the rendered order, not the `sorted` beside the print loop**, and the
        # distinction is the whole of why row 2218's recipe for this did not work.  Three clauses
        # guarantee that order independently: `project_modules` sorts its `glob`, the four walks
        # take `sorted(mods.items())`, and the two print loops sort on `(path, line)`.  Measured at
        # `ab0a3b4`: deleting **both** print sorts leaves `--tree` byte-identical on the tree's own
        # **26** declined entries with every case green, and so does reversing the `glob` on top of
        # that.  No single-clause mutation of a redundant guarantee can be caught by anything, which
        # is why a fixture that writes one file after another -- the shape row 2218 proposed -- pins
        # nothing at all: write order is not walk order here.  What this case does catch is the last
        # of the three going: with all four walks on the dict, the `glob` reversed **and** the print
        # loops unsorted, it fails and so does the case below, while the same mutation with the
        # print loops left alone is green and the live tree's declined block is unmoved -- same 26
        # entries in the same order.  That is the sense in which the sort is the guarantee, and
        # this case is its witness.
        write("Also", "/-! Nothing here names a module either, and a module has reverse closure"
                      " **3**. -/\n")
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **9**. -/\n")
        rc, lines = tree_report(d)
        check("the mismatch, the declined closure claims and the declined size claim render in "
              "that order, each with its own reason and text, and the two declines are in path "
              "order rather than in the order the walk happened to reach them",
              (rc, rows(lines)),
              (1,
               ["  MISMATCH  FormalSchemes/Base.lean:1  the reverse closure of"
                " `FormalSchemes.Base`: states 9, walk gives 2",
                "            reverse closure **9**. -/",
                "  declined  FormalSchemes/Also.lean:1  no anchor -- reverse closure **3**. -/",
                "  declined  FormalSchemes/Mid.lean:3  possessive pronoun: its antecedent is the"
                " subject, not the last module named -- forward closure is **1** module. -/",
                "  size-declined  FormalSchemes/Says.lean:1  no anchor -- **12** lines long. -/"]))

        # And with nothing stale left, both declines still print and the run is **green**: a decline
        # is a reading a reviewer judges, not a failure, and the exit code is the only place that
        # distinction lives.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **2**. -/\n")
        rc, lines = tree_report(d)
        check("and both still print on a tree with no mismatch at all, which exits 0 -- a decline "
              "is read, not failed on",
              (rc, lines[-2:]),
              (0,
               ["  declined  FormalSchemes/Mid.lean:3  possessive pronoun: its antecedent is the"
                " subject, not the last module named -- forward closure is **1** module. -/",
                "  size-declined  FormalSchemes/Says.lean:1  no anchor -- **12** lines long. -/"]))

    # `--stub` (row 2221), the mode that prices a module this tree does not have.  Two things are
    # asserted in two ways on purpose, which is the division the `--edge` cases above already draw:
    # the **arithmetic** against `stub_cost`'s returned dict, where a case can be precise and cannot
    # rot on a reworded label, and the **rendering** against `main`'s own stdout, because a label
    # sitting beside the wrong number is a defect no structural assertion can see.  Row 2221's
    # design decisions are three and every one of them has a case here: which count is the number,
    # which union convention, and that the stub's imports are the experiment rather than a detail.

    def stub_figures(r: dict) -> tuple:
        """The price of a stub, as the tuple a case can read: figures, files, positions, the two
        species with the unclassified bucket, the leaf sub-count, and the baseline.

        `figures` and `positions` are both here because they are **different numbers** and the
        tree's prose quotes both -- one position can carry two figures, which is what a companion
        figure is, and a report that conflated them would still pass a case asserting either alone.
        """
        return (len(r["population"]), len(r["files"]), r["positions"],
                tuple(len(r["species"][k]) for k in (1, 2, 0)),
                r["leaf_sentences"], r["baseline"])

    def rebuild(r: dict) -> tuple:
        """The four union figures, in the order the report prints them, with the contributor it
        drops.  Row 2221 §2b is one sentence of this tree published with three different figures by
        three sessions, none of whom miswalked anything; these four are what they were each walking.
        """
        return (len(r["inclusive"]), len(r["inclusive_no_stub"]),
                len(r["strict"]), len(r["strict_no_stub"]),
                r["biggest"], r["biggest_size"], len(r["dropped"]), len(r["dropped_no_stub"]))

    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        # Three modules in a chain, every figure of them **correct**, so that everything below is
        # the stub's own cost and not the fixture's.  `Mid` states its reverse closure twice, in the
        # two conventions the tree writes, which is one position carrying two figures -- the
        # distinction row 2221 §3 asks the report to name, and the reason `stub_figures` returns
        # both counts.
        write("Base", "/-! Over nothing: forward closure **0**, reverse closure **2**. -/\n")
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure **1**"
                     " (2 counted with itself). -/\n")
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! Over `FormalSchemes.Mid`: forward closure **2**, reverse closure **0**."
                     "  It is one of the\n**3** modules under `FormalSchemes/`. -/\n")
        check("the tree the --stub cases are read against is itself green", audit(d)[0], [])

        # The `unclassified` bucket, tested on the function and not through the mode, because
        # **the mode cannot produce one**: every mismatch in the price is caused by the stub, and a
        # stub can only move a project total or a reverse closure of a module it reaches.  That is
        # exactly why the guard is worth having and exactly why it needs a case here -- dropping the
        # `reached` test would be invisible to every fixture below.
        check("a reverse closure of a module the stub does not reach is unclassified rather than "
              "counted, which is the one shape the mode's own report cannot produce",
              [stub_species(c, {"FormalSchemes.Near"})
               for c in ({"kind": "total", "subject": None},
                         {"kind": "reverse", "subject": "FormalSchemes.Near"},
                         {"kind": "reverse", "subject": "FormalSchemes.Far"},
                         {"kind": "forward", "subject": "FormalSchemes.Near"})],
              [1, 2, 0, 0])

        S = "FormalSchemes.ZStub"
        check("a stub over the tail of a chain costs one figure per module it reaches, plus the "
              "project total, and its five figures stand at three positions",
              stub_figures(stub_cost(d, S, ("FormalSchemes.Top",))),
              (5, 3, 3, (1, 4, 0), 0, 0))
        check("and its rebuild is four figures, not one: the stub is on the tree the repairs are "
              "made in, and an edited file re-elaborates itself",
              rebuild(stub_cost(d, S, ("FormalSchemes.Top",))),
              (4, 3, 3, 2, "FormalSchemes.Base", 3, 3, 2))

        # The decision row 2221 §3 calls unmissable: the same stub name over a different import is a
        # different experiment.  Over `Base` the stub reaches one module instead of three, and
        # nothing but that module's own figure and the total moves -- so a mode that inferred the
        # imports, or that silently read a sibling as a module over this one, would answer this with
        # the five above.
        check("the stub's imports are the experiment: the same name over `Base` instead of `Top` "
              "costs two figures, not five",
              stub_figures(stub_cost(d, S, ("FormalSchemes.Base",))), (2, 2, 2, (1, 1, 0), 0, 0))
        check("and a stub that imports nothing prices the project total alone, which is the "
              "cheapest experiment there is and the one no reverse closure can reach",
              stub_figures(stub_cost(d, S)), (1, 1, 1, (1, 0, 0), 0, 0))
        check("a stub whose name is in a subdirectory the tree does not have is priced the same, "
              "which is the whole of what the `makedirs` in the copy is for",
              stub_figures(stub_cost(d, "FormalSchemes.Sub.ZStub", ("FormalSchemes.Top",))),
              (5, 3, 3, (1, 4, 0), 0, 0))

        # The rendering, which is the half `stub_cost` cannot be wrong about: these six lines are
        # the four conventions with their labels, and a report that transposed two of the numbers
        # would satisfy every structural case above.  Asserted by value, and with the colons aligned
        # as the block is printed, because a reader diffs two runs of this report.
        rc, lines = tree_report(d, "--stub", "%s:FormalSchemes.Top" % S)
        check("the report says how big the tree would be and how big it is, which is the other "
              "half of a union figure being reproducible from the report alone",
              [ln for ln in lines if ln.startswith("modules under")],
              ["modules under FormalSchemes/ :     4   with the stub (3 without it)"])
        at = [i for i, ln in enumerate(lines) if ln.startswith("  counting an edited file")]
        check("the rebuild block renders each convention beside its own figure, and says which one "
              "counts the stub",
              (rc, lines[at[0]:at[0] + 6] if at else lines),
              (0,
               ["  counting an edited file as re-elaborating itself :     4   of 4",
                "    without the stub, which no repair edits        :     3",
                "  counting only modules that import an edited one  :     3",
                "    without the stub                               :     2",
                "  the largest single contributor                   : `FormalSchemes.Base` at 3",
                "  the first union without that one file            :     3   (2 without the"
                " stub)"]))
        check("a mode that prices a tree that does not exist cannot fail, so the run exits 0 even "
              "though every figure in it is about to be reported as a repair",
              (rc, [ln for ln in lines if "unclassified" in ln]),
              (0, ["  by species                 : 1 / 4, unclassified 0   (a project total or tree"
                   " census /"]))

        # Row 2225 goal 2: the `by_file` table, whose two clauses -- **the per-file repair count**
        # and the tie-break -- were read by nothing.  Asserted as rendered rather than off the dict,
        # because the defect this exists for is a column of numbers that add up to something a
        # reader will quote: replacing `len([c for c in population if c["path"] == f])` with
        # `len(population)` prints the whole population on every row, which on the live tree at
        # `ab0a3b4` is `44 repairs` eighteen times, and it survived all 142 cases.
        check("each file's own repair count is its own, not the population's, and the rebuild "
              "table renders one row per file ordered by what a repair there re-elaborates",
              [ln for ln in lines if ln.startswith("    FormalSchemes/")],
              ["    FormalSchemes/Base.lean                                             1 repairs"
               "     3",
               "    FormalSchemes/Mid.lean                                              2 repairs"
               "     2",
               "    FormalSchemes/Top.lean                                              2 repairs"
               "     1"])

        # Row 2221 §2a as a case rather than as a paragraph: **the price moves because a docstring
        # elsewhere in the fixture grew**, with the stub unchanged.  That is the mechanism that made
        # one live figure wrong at six consecutive heads -- the authoring pull request's own prose
        # kept adding sentences the stub would falsify -- and a mode whose only evidence is that the
        # tree stays green has not been shown to see it.
        write("Top", "import FormalSchemes.Mid\n"
                     "/-! Over `FormalSchemes.Mid`: forward closure **2**, reverse closure **0**."
                     "  It is one of the\n**3** modules under `FormalSchemes/`.  The reverse"
                     " closure of `FormalSchemes.Base` is\n**2**. -/\n")
        check("the price moves when a docstring elsewhere in the tree grows, with the same stub "
              "over the same module -- which is how a figure measured mid-development goes stale",
              stub_figures(stub_cost(d, S, ("FormalSchemes.Top",))), (6, 3, 4, (1, 5, 0), 0, 0))

        # And the baseline, which is the one clause here a reader cannot check by eye.  The two
        # audits run under different roots, so the population subtraction is on paths made relative
        # to each -- without that the price swallows every MISMATCH the tree already had, and the
        # answer is larger and looks more thorough.  `Mid`'s figure is wrong at both ends and is the
        # baseline's; the companion beside it is right now and wrong with the stub, so it is the
        # stub's, which is what makes this case about the subtraction and not about the file.
        write("Mid", "import FormalSchemes.Base\n"
                     "/-! Over `FormalSchemes.Base`: forward closure **1**, reverse closure **9**"
                     " (2 counted with itself). -/\n")
        check("a MISMATCH the tree already has is the baseline's and not the stub's, and the "
              "companion beside it that only the stub falsifies still is",
              (len(audit(d)[0]), stub_figures(stub_cost(d, S, ("FormalSchemes.Top",)))),
              (1, (5, 3, 4, (1, 4, 0), 0, 1)))

        # The argument checks, all of which land before the copy is made, so a mistyped name costs
        # nothing.  `FormalSchemes.Base` as the *name* is the one worth a case: the stub would be
        # written over that file in the copy, and the report would then price a tree with a module's
        # contents **deleted** rather than a tree with one module more.
        def refused(name, imports):
            try:
                stub_cost(d, name, imports)
                return "no error"
            except SystemExit as e:
                return str(e)
        check("a stub name the tree already has is refused rather than overwriting that module in "
              "the copy, and so are a name outside the walk, two names that would make the stub "
              "absent from the tree it prices, an import that is not a module and a repeated "
              "import",
              [refused(n, i) for n, i in ((("FormalSchemes.Base"), ("FormalSchemes.Top",)),
                                          ("Elsewhere.Zed", ()),
                                          ("FormalSchemes.", ()),
                                          ("FormalSchemes.Sub/Zed", ()),
                                          (S, ("FormalSchemes.Nope",)),
                                          (S, ("FormalSchemes.Top", "FormalSchemes.Top")))],
              ["`FormalSchemes.Base` is already a module of this tree",
               "`Elsewhere.Zed` is not a module name under FormalSchemes/",
               "`FormalSchemes.` is not a module name under FormalSchemes/",
               "`FormalSchemes.Sub/Zed` is not a module name under FormalSchemes/",
               "`FormalSchemes.Nope` is not a module under FormalSchemes/",
               "`FormalSchemes.ZStub` cannot import a module twice"])

        # Row 2221 §6: if the mode writes a file anywhere it deletes it on every exit path, and
        # there is a case for the run that **raised**.  This mode writes nothing under the tree at
        # all -- the stub goes into a `tempfile.TemporaryDirectory` -- so what is asserted is the
        # stronger property, byte-for-byte, and the raising run is asserted after the successful one
        # because a leak would otherwise be masked by the order.
        def snapshot() -> list:
            out = []
            for here, _dirs, names in os.walk(d):
                for n in sorted(names):
                    p = os.path.join(here, n)
                    out.append((os.path.relpath(p, d).replace(os.sep, "/"),
                                open(p, "rb").read()))
            return sorted(out)
        before = snapshot()
        stub_cost(d, S, ("FormalSchemes.Top",))
        after = snapshot()
        refused(S, ("FormalSchemes.Nope",))
        check("the tree is byte-identical after a run, and after a run that raised -- nothing is "
              "written under it and there is no exit path on which something is",
              (before == after, before == snapshot(), len(before)), (True, True, 3))

    # The other half of goal 2: what the table does when two files re-elaborate **the same number**
    # of modules, which the chain above cannot exhibit because its three reverse closures are 3, 2
    # and 1.  Two leaves quoting a figure about the stub's own import have reverse closure 0 apiece
    # and different repair counts, so the tie is real and the rendered order says how it is broken.
    #
    # **The `key`'s second component cannot be killed by any fixture, and that is a fact about the
    # input rather than a gap here.** `files` is `sorted({...})`, so `by_file`'s input is already in
    # path order and Python's sort is stable: deleting `t[0]` from the key leaves every row where it
    # was, on this fixture and on the tree. What a case *can* pin is that the tie is broken by the
    # **name** and not by something correlated with it -- `-t[1]` would put `Zeta` above `Alpha`
    # here, since it carries the second repair -- and that is what this asserts.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        # Every figure correct before the stub and falsified by it, so the price is the stub's: the
        # two leaves state `Hub`'s reverse closure, `Hub` states its own, and none of the three
        # imports anything, which is what makes the two closures equal.
        write("Hub", "/-! Over nothing: forward closure **0**, reverse closure **0**. -/\n")
        write("Alpha", "/-! The reverse closure of `FormalSchemes.Hub` is **0**. -/\n")
        write("Zeta", "/-! The reverse closure of `FormalSchemes.Hub` is **0**.  Nothing imports"
                      " it, so the\nreverse closure of `FormalSchemes.Hub` is **0** here too. -/\n")
        # A module carrying no figure at all, which is what makes the **over-match** control bite:
        # every module of the chain fixture above is an edited one, so a table with a row per module
        # of the tree renders identically there and only this fixture can tell the two apart.
        write("Quiet", "/-! Nothing here is a measurement of anything. -/\n")
        check("the tie-break fixture is itself green, so what the table shows is the stub's cost",
              audit(d)[0], [])
        check("two files whose repairs re-elaborate equally many modules are ordered by name and "
              "not by their repair counts, and the file the stub reaches sorts above both",
              [ln for ln in tree_report(d, "--stub", "FormalSchemes.ZStub:FormalSchemes.Hub")[1]
               if ln.startswith("    FormalSchemes/")],
              ["    FormalSchemes/Hub.lean                                              1 repairs"
               "     1",
               "    FormalSchemes/Alpha.lean                                            1 repairs"
               "     0",
               "    FormalSchemes/Zeta.lean                                             2 repairs"
               "     0"])

    # A stub's arrival makes a sentence that calls its own file a **leaf** false, and the repair is
    # a rewrite rather than a `+1` -- so the report counts those separately inside the reverse-
    # closure species.  Two trees differing in one word, because the sub-count is keyed on the
    # phrase `audit` writes for that finding and a case has to fail if that phrase is reworded.
    for opener, leaves, figures in (("A new leaf over", 1, 2), ("Over", 0, 1)):
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "FormalSchemes"))
            with open(os.path.join(d, "FormalSchemes", "Only.lean"), "w", encoding="utf-8") as f:
                f.write("/-! %s nothing: forward closure **0**, reverse closure **0**. -/\n"
                        % opener)
            check("a sentence opening `%s` is counted as a leaf sentence %d time(s) by a stub "
                  "over it, and carries %d figure(s)" % (opener, leaves, figures),
                  stub_figures(stub_cost(d, "FormalSchemes.ZStub", ("FormalSchemes.Only",)))[:5],
                  (figures, 1, 1, (0, figures, 0), leaves))

    def stub_arg(a):
        try:
            return parse_stub(a)
        except SystemExit as e:
            return str(e)
    STUB_USAGE = ("--stub takes `FormalSchemes.New:FormalSchemes.A,FormalSchemes.B`, or"
                  " `FormalSchemes.New` for a stub that imports nothing")
    check("a well-formed stub argument splits, and every malformed one is refused by name -- the "
          "empty string and a bare trailing colon included, since those two differ by a character "
          "nobody would see in a shell history",
          [stub_arg(a) for a in ("FormalSchemes.N:FormalSchemes.A,FormalSchemes.B",
                                 "FormalSchemes.N", "", "FormalSchemes.N:", "FormalSchemes.N:A,,B",
                                 "A:B:C", ":")],
          [("FormalSchemes.N", ("FormalSchemes.A", "FormalSchemes.B")),
           ("FormalSchemes.N", ()), STUB_USAGE, STUB_USAGE, STUB_USAGE, STUB_USAGE, STUB_USAGE])

    # ...and the same through `main`, for the reason the `--edge ''` case above gives: `parse_stub`
    # alone does not pin the branch, and a falsy test there would run a full audit of whatever `.`
    # happened to be instead of reporting a bad argument.
    #
    # The **redirect** is row 2225 goal 1, and the `--edge` case above needs none only by accident:
    # both of its arguments are malformed, so `main` raises before printing anything.  Here the
    # second one is well formed on purpose -- that is the half of the case asserting a good
    # invocation returns `0` -- so without this, `report_stub` writes its 20 lines into the middle
    # of `--selftest`'s own case list, which was **162 lines for 142 cases** at `ab0a3b4`.  Only the
    # return value is the subject; `tree_report` is the way to assert the text.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))
        with open(os.path.join(d, "FormalSchemes", "Only.lean"), "w", encoding="utf-8") as f:
            f.write("/-! Over nothing: forward closure **0**. -/\n")
        argv, cwd = sys.argv, os.getcwd()
        try:
            os.chdir(d)
            got = []
            for a in ("", "FormalSchemes.Zed:FormalSchemes.Only"):
                sys.argv = ["closure_audit.py", "--stub", a]
                try:
                    with contextlib.redirect_stdout(io.StringIO()):
                        got.append(main())
                except SystemExit as e:
                    got.append(str(e))
        finally:
            sys.argv = argv
            os.chdir(cwd)
        check("`--stub ''` is refused by `main` rather than falling through to the tree audit, "
              "and a well-formed one reports and exits 0", got, [STUB_USAGE, 0])

    # `PRICE` and `--sweep` (row 2221 goal 4).  A counterfactual price is read by no species and
    # cannot be -- its subject is a tree that does not exist -- so the answer is the reading list,
    # and these four cases are the whole of what that decision buys.  The third is the one that
    # matters: a price stated **beside a closure claim** was invisible because of the claim, which
    # is the per-figure-versus-per-sentence mechanism row 2209 paid for.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        write("Alone", "/-! A new module over this one would cost **15** figure repairs in **9**"
                       " files. -/\n")
        write("Beside", "/-! Over nothing: forward closure **0**.  The reverse closure of"
                        " `FormalSchemes.Alone` is\n**0**, so the edge costs **8** figure repairs"
                        " in **4** files. -/\n")
        write("Wordy", "/-! Declarations only: **3** of them, no module, no edge and no figure"
                       " repairs at all. -/\n")
        # The whole sentence and not a prefix of it, because the numeral is the reason the
        # sentence is on the list and a slice short enough to be readable here would cut it off.
        blind = sorted((c["module"], c["text"]) for c in invisible(project_modules(d)))
        check("a counterfactual price with no closure word and no project total beside it is on "
              "the reading list, which is the whole point: nothing else on this tree reads it",
              [t for m, t in blind if m == "FormalSchemes.Alone"],
              ["/-! A new module over this one would cost **15** figure repairs in **9** files."])
        check("and a price stated beside a closure claim is on it too -- the claim is what hid the "
              "price until the `CLOSURE` exclusion was read per figure rather than per sentence",
              [t for m, t in blind if m == "FormalSchemes.Beside"],
              ["The reverse closure of `FormalSchemes.Alone` is **0**, so the edge costs **8**"
               " figure repairs in **4** files."])
        check("a price of *none*, written in words, is not a measurement and is not listed: "
              "there is nothing in it to re-run, and the sentence carries a numeral of its own so "
              "it is the marker's adjacency that refuses it rather than `FIGURE`",
              [m for m, _ in blind if m == "FormalSchemes.Wordy"], [])
        # Goal 4's other half: the shape is on the list, and the list's own header says its remedy
        # is not the one the header prescribes for everything else.  A reader who follows *rewrite
        # it in the checked spelling* on a counterfactual price is being sent somewhere that does
        # not exist.
        header = tree_report(d, "--sweep")[1]
        cut = [i for i, ln in enumerate(header) if "A counterfactual price" in ln]
        check("and `--sweep`'s header says what to do with a price, which is not what to do with "
              "the rest of the list",
              header[cut[0]:cut[0] + 3] if cut else header,
              [" is such a measurement.  A counterfactual price -- `N figure repairs` -- is the"
               " one",
               " shape here that cannot be rewritten that way at all, because its subject is a"
               " tree",
               " that does not exist: re-run `--edge` or `--stub`, and date what you write.)"])


    # ---------------------------------------------------------------------------------------------
    # The **census bucket** species (row 2224).  Two trees, because the two live censuses resolve
    # their subject set two different ways and one fixture cannot exercise both: `:393` names its
    # three modules in its own sentence and `:305` names its six in the `## Placement` opener one
    # sentence back, before that opener's colon.  Both mechanisms have a positive control here, and
    # every decline path has a negative one -- a species that can go red needs the second more than
    # the first, which is the standing reason this file's fixtures come in pairs.
    #
    # The trees are copied from the shapes the tree writes, per row 2224 goal 3: a set of modules
    # named in the sentence, a universe stated as *the other N* or *the only one of the N*, buckets
    # as `N reach <word>`, and one bucket stated in words with no numeral at all.
    def census_tree(d, write, cen_imports="A1 A2 A3 A4 A5", rival_imports="A1 A2 A3 A4",
                    sentence=None, extra=None, quiet_body=None):
        """The `only one of the N` tree: ten modules, a subject set of five, and a histogram with a
        hole at 3 that the sentence names nowhere -- which is what makes the remainder clause
        testable at all.  Returns nothing; the caller audits `d`.

        `A1`..`A5` reach one each (themselves), `Q` none, `S1` one, `S2` two, `Rival` four and
        `Cen` five, so the walk is `0 -> 1, 1 -> 6, 2 -> 1, 4 -> 1, 5 -> 1` over all ten.
        """
        for i in range(1, 6):
            write("A%d" % i, "/-! Nothing measured here. -/\n")
        write("Q", quiet_body or "/-! Nothing measured here. -/\n")
        write("S1", "import FormalSchemes.A1\n/-! Nothing measured here. -/\n")
        write("S2", "import FormalSchemes.A1\nimport FormalSchemes.A2\n"
                    "/-! Nothing measured here. -/\n")
        write("Rival", "".join("import FormalSchemes.%s\n" % m for m in rival_imports.split())
                       + "/-! Nothing measured here. -/\n")
        write("Cen", "".join("import FormalSchemes.%s\n" % m for m in cen_imports.split())
                     + "/-! " + (sentence or
                                 "Over `FormalSchemes.A1`, `FormalSchemes.A2`,"
                                 " `FormalSchemes.A3`, `FormalSchemes.A4` and `FormalSchemes.A5`:"
                                 " this module is the only one of the 10 that reaches all five --"
                                 " 1 reaches none, 6 reach exactly one, 1 reaches two and"
                                 " 1 reaches four") + ". -/\n")
        if extra:
            write(*extra)

    def census_run(cen_imports="A1 A2 A3 A4 A5", rival_imports="A1 A2 A3 A4",
                   sentence=None, extra=None, quiet_body=None):
        """`(mismatches, census declines)` on a freshly written census tree, each reduced to what a
        case can read: `(stated, actual, what)` and the decline reason."""
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "FormalSchemes"))

            def write(name, body):
                with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                          encoding="utf-8") as f:
                    f.write(body)

            census_tree(d, write, cen_imports, rival_imports, sentence, extra, quiet_body)
            mis, _dec, _sz, cdec = audit(d)
            return ([(c["stated"], c["actual"], c["what"]) for c in mis
                     if c.get("kind") == "census"],
                    [c["declined"] for c in cdec],
                    [(c["stated"], c["actual"], c.get("what")) for c in mis
                     if c.get("kind") != "census"])

    check("the census tree is green: four buckets, a universe and an identity all agree with the "
          "walk, and nothing else on the tree is stale either", census_run(), ([], [], []))

    # `_module_list` directly, because its **cap** is the one thing about it a census fixture
    # cannot reach -- the live tree has one module in the top bucket and the trees above have one
    # rival, so nothing here ever renders four.  A cap that stops speaking is the silent-truncation
    # failure `stub_cost`'s comment argues against, one report line long instead of one mode long,
    # and it would read as *the walk gives these three* when the walk gave five.
    check("a module list says it was truncated rather than ending silently, and an empty one is "
          "a word rather than a blank",
          (_module_list([]),
           _module_list(["FormalSchemes.A", "FormalSchemes.B", "FormalSchemes.C"]),
           _module_list(["FormalSchemes.A", "FormalSchemes.B", "FormalSchemes.C",
                         "FormalSchemes.D", "FormalSchemes.E"])),
          ("nothing",
           "`FormalSchemes.A`, `FormalSchemes.B`, `FormalSchemes.C`",
           "`FormalSchemes.A`, `FormalSchemes.B`, `FormalSchemes.C` and 2 more"))

    # **Positive control 1, the one row 2224 goal 3 calls the interesting one.**  One bucket
    # moved by one, nothing else touched.  Two independent witnesses fire and that is the design
    # rather than noise: the bucket's own predicate, and the remainder, which is what says the
    # sentence's numerals no longer partition the set it named.  A grammar that read the multiset
    # of numerals instead of the predicates would report the first as a different bucket's and the
    # second not at all.
    check("a single bucket numeral moved by one is caught, by its own predicate and by the "
          "remainder",
          census_run(sentence="Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
                              " `FormalSchemes.A4` and `FormalSchemes.A5`: this module is the only"
                              " one of the 10 that reaches all five -- 1 reaches none, 7 reach"
                              " exactly one, 1 reaches two and 1 reaches four")[0],
          [(7, 6, "the modules reaching 1 of the 5 this census is of"),
           (0, 1, "the buckets this census names in words but not with a numeral (indices 5)")])

    # **Positive control 2: a module lands on the tree and the prose is left alone.**  This is row
    # 2214's measured cost -- seven numerals falsified silently while `--tree` said MISMATCH 0 --
    # and the two witnesses are the ones that matter.  `New` reaches three of the five, which is the
    # bucket this sentence names **nowhere**: not with a numeral and not in words.  So the remainder
    # cannot account for it, and that half is exactly what row 2220 measured the arithmetic to be
    # blind to.
    landed = ("New", "import FormalSchemes.A1\nimport FormalSchemes.A2\nimport FormalSchemes.A3\n"
                     "/-! Nothing measured here. -/\n")
    check("a module added to the tree with the prose untouched is caught twice: the set being "
          "partitioned grew, and its own bucket is one the sentence names nowhere",
          census_run(extra=landed)[0],
          [(10, 11, "the size of the set this census partitions"),
           (2, 1, "the buckets this census names in words but not with a numeral (indices 5)")])

    # And with the universe numeral repaired and nothing else, the remainder is **still** red.  That
    # is the property the arithmetic species row 2220 measured does not have: there, repairing the
    # total makes a one-short sum look right again.
    check("repairing only the universe numeral leaves the unnamed bucket reported",
          census_run(sentence="Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
                              " `FormalSchemes.A4` and `FormalSchemes.A5`: this module is the only"
                              " one of the 11 that reaches all five -- 1 reaches none, 6 reach"
                              " exactly one, 1 reaches two and 1 reaches four",
                     extra=landed)[0],
          [(2, 1, "the buckets this census names in words but not with a numeral (indices 5)")])

    # **Positive control 3: the identity, and the one population where it is the only witness.**
    # `Cen` and `Rival` swap which of them reaches all five.  The histogram is **byte-identical** --
    # one module at 4 and one at 5, before and after -- so every bucket numeral, the universe and
    # the remainder all still agree, and the only false thing in the sentence is *this module is
    # the only one*.  Row 2224 §1 reads that bucket's member by name rather than inferring it
    # from the shortfall; this is why.
    #
    # **It is reported as two figures and the second names `Rival`.**  One comparison of the top
    # bucket against `[module]` is enough to *detect* this, and that is what row 2224 shipped; it
    # is not enough to *report* it, because `stated=1, actual=len(only)` renders as `states 1,
    # walk gives 1` on exactly this population -- the count is right and the member is wrong.  The
    # assertion below is on the `what` strings and not only on the pair, which is the one thing a
    # structured fixture can do about a rendering defect.
    check("the only-one claim is checked by name, and when the top bucket's member changes "
          "without its size changing both halves are reported and the walk's module is named",
          census_run(cen_imports="A1 A2 A3 A4", rival_imports="A1 A2 A3 A4 A5")[0],
          [(1, 0, "this file among the modules reaching all 5, which this sentence says it is"
                  " the only one of"),
           (0, 1, "the modules besides this one reaching all 5, which this sentence says is"
                  " none -- the walk gives `FormalSchemes.Rival`")])

    # The other half of the same claim, alone: nobody at all reaches the whole set, so there is no
    # rival to name and the sentence is still false.  `Cen` and `Rival` both reach four of the five
    # here, which is why the buckets below are not the default tree's.  A `len(only) != 1` reading
    # of the identity would pass this, and so would one that only looked for a rival.
    check("a sentence claiming the top bucket when the top bucket is empty is caught, with no "
          "second figure because there is no other module to name",
          census_run(cen_imports="A1 A2 A3 A4",
                     sentence="Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
                              " `FormalSchemes.A4` and `FormalSchemes.A5`: this module is the only"
                              " one of the 10 that reaches all five -- 1 reaches none, 6 reach"
                              " exactly one, 1 reaches two and 2 reach four")[0],
          [(1, 0, "this file among the modules reaching all 5, which this sentence says it is"
                  " the only one of")])

    # The subject set resolved **one hop back, before the opener's colon** -- `:305`'s mechanism,
    # and the one the `## Placement` idiom needs.  A separate tree, because this census's universe
    # is *the other N* and its subject module must not itself reach the whole set.
    def hop_run(sentence=None, extra=None):
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "FormalSchemes"))

            def write(name, body):
                with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                          encoding="utf-8") as f:
                    f.write(body)

            for i in range(1, 4):
                write("A%d" % i, "/-! Nothing measured here. -/\n")
            write("Q", "/-! Nothing measured here. -/\n")
            write("S2", "import FormalSchemes.A1\nimport FormalSchemes.A2\n"
                        "/-! Nothing measured here. -/\n")
            write("Hop", "import FormalSchemes.A1\nimport FormalSchemes.A2\n"
                         "/-! A leaf over `FormalSchemes.A1`, `FormalSchemes.A2` and"
                         " `FormalSchemes.A3`: the forward closure of `FormalSchemes.Hop` is"
                         " **2**.  " + (sentence or
                                        "No module reaches all three of the above -- the best any"
                                        " of the other 5 does is two, and only 1 of them manages"
                                        " that: 1 reaches none and 3 reach exactly one") + ". -/\n")
            if extra:
                write(*extra)
            mis, _dec, _sz, cdec = audit(d)
            return ([(c["stated"], c["actual"], c["what"]) for c in mis],
                    [c["declined"] for c in cdec])

    check("the subject set resolves from the opener one sentence back, before its colon, and that "
          "tree is green too", hop_run(), ([], []))
    check("a bucket moved by one is caught when the subject set came from the hop",
          hop_run(sentence="No module reaches all three of the above -- the best any of the other 5"
                           " does is two, and only 1 of them manages that: 2 reach none and 3 reach"
                           " exactly one")[0],
          [(2, 1, "the modules reaching 0 of the 3 this census is of"),
           (0, 1, "the buckets this census names in words but not with a numeral (indices 2, 3)")])

    # The negative controls.  Every one of these is a **decline**, printed and never failed on, and
    # each is a reading this walk cannot pin rather than a sentence it has caught out.
    subj = ("Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
            " `FormalSchemes.A4` and `FormalSchemes.A5`: ")
    for name, sentence, why in [
            ("a cardinality that does not match the modules named declines, and does not fire",
             subj + "this module is the only one of the 10 that reaches all four -- 1 reaches none,"
                    " 6 reach exactly one, 1 reaches two and 1 reaches four",
             "the set this census is of does not resolve to the 4 it spells (5 named here, 0 in"
             " the opener one sentence back)"),
            ("a census naming no cardinality at all declines",
             subj + "this module is the only one of the 10 -- 1 reaches none, 6 reach exactly one,"
                    " 1 reaches two and 1 reaches four",
             "no spelled cardinality for the set the census is of"),
            ("a census with no universe phrase declines rather than picking one",
             subj + "this module reaches all five -- 1 reaches none, 6 reach exactly one, 1 reaches"
                    " two and 1 reaches four",
             "the set being partitioned is not stated, or is stated twice"),
            ("a census stating both universes declines",
             subj + "this module is the only one of the 10 that reaches all five, and the other 9"
                    " do not -- 1 reaches none, 6 reach exactly one, 1 reaches two and 1 reaches"
                    " four",
             "the set being partitioned is not stated, or is stated twice"),
            ("a bucket predicate outside the closed vocabulary declines",
             subj + "this module is the only one of the 10 that reaches all five -- 1 reaches"
                    " nothing, 6 reach exactly one, 1 reaches two and 1 reaches four",
             "bucket predicate `nothing` is not an index into a set of 5"),
            ("a bucket index larger than the set declines",
             subj + "this module is the only one of the 10 that reaches all five -- 1 reaches none,"
                    " 6 reach exactly one, 1 reaches two and 1 reaches nine",
             "bucket predicate `nine` is not an index into a set of 5"),
            ("two numerals bound to one bucket declines",
             subj + "this module is the only one of the 10 that reaches all five -- 1 reaches none,"
                    " 2 reach none, 1 reaches two and 1 reaches four",
             "two numerals are bound to the same bucket"),
            ("a sentence declaring the strict convention for its own buckets declines",
             subj + "this module is the only one of the 10 that reaches all five, not counting"
                    " itself -- 1 reaches none, 6 reach exactly one, 1 reaches two and 1 reaches"
                    " four",
             "the sentence declares the strict convention for its own buckets, which this species"
             " does not read"),
            ("a subject set naming something that is not a module of this tree declines",
             "Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
             " `FormalSchemes.A4` and `FormalSchemes.Absent`: this module is the only one of the 10"
             " that reaches all five -- 1 reaches none, 6 reach exactly one, 1 reaches two and"
             " 1 reaches four",
             "`FormalSchemes.Absent` is not a module of this tree")]:
        got = census_run(sentence=sentence)
        check(name, got[:2], ([], [why]))

    # Row 2214's own shape, and the only reading of *the other N* this species refuses: the
    # exclusion is the set the census is **of** rather than the module the docstring is in.  Ten
    # modules and a subject set of five, so the two readings are 9 and 5 and the numeral says
    # which -- that is what makes this a decline here and a MISMATCH nowhere.  Population on the
    # tree at `2857956`: **0**.
    check("`the other N` excluding the census's own subject set declines, which is row 2214's "
          "objection met rather than overruled",
          census_run(sentence=subj + "no module reaches all five -- the best any of the other 5"
                                     " does is four, and 1 reaches none, 6 reach exactly one and"
                                     " 1 reaches two")[:2],
          ([], ["*the other* here excludes the set the census is of, not the module this docstring"
                " is in -- two readings, and this species reads the second"]))

    # The gate that keeps every other *the other N* in the tree on the reading list.  `census_spans`
    # is empty without a bucket in the sentence, so a sentence carrying the phrase and no census is
    # untouched by this species and stays exactly where row 2214 put it.
    check("a `the other N` sentence with no bucket in it is not a census, so this species reads no "
          "span of it and it keeps the --sweep entry row 2214 gave it",
          census_spans("Of the other 12 modules under `FormalSchemes/`, none matters here."), [])
    check("and a sentence that is one has its two bucket spans, its cardinality and its universe "
          "read, which is exactly what --sweep stops carrying",
          len(census_spans("this module is the only one of the 10 that reaches all five -- 1"
                           " reaches none and 6 reach exactly one")), 4)

    # The identity's `this file` gate, from the side that makes it a gate rather than decoration.
    # The swapped tree again -- `Rival` is what reaches all five -- but now the sentence says so by
    # **name** instead of saying *this module*, and it resolves its subject set through the hop
    # because its own tokens are `Rival` alone.  Whether a named module really is the only one is
    # `attribute()`'s kind of question and not this species', so the identity is not asserted and
    # this tree is green.  Drop the gate and the same tree goes red against a sentence that is, on
    # this fixture, simply true.
    check("`the only one of the N` said of a named module is not an assertion about this file",
          census_run(cen_imports="A1 A2 A3 A4", rival_imports="A1 A2 A3 A4 A5",
                     sentence="Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
                              " `FormalSchemes.A4` and `FormalSchemes.A5`: nothing is measured"
                              " here.  `FormalSchemes.Rival` is the only one of the 10 that"
                              " reaches all five -- 1 reaches none, 6 reach exactly one,"
                              " 1 reaches two and 1 reaches four"),
          ([], [], []))

    # **And the over-match control for that gate, which is the case the one above cannot make.**
    # The case above has no self-phrase in the census sentence at all, so it measures that the gate
    # is *present*; it says nothing about how the gate decides when there is one.  Here the same
    # true sentence -- `Rival` really is the only one of the ten -- opens with four words about
    # this file, which is the ordinary way to write a comparison.  Asking *is a self-phrase
    # anywhere before the claim* reds this tree; asking `attribute()`'s question, *is a
    # self-phrase the **last** anchor before the claim*, does not.  See `_identity_is_self`.
    check("a self-phrase earlier in the sentence does not make a named module's only-one claim "
          "an assertion about this file, and the true sentence stays green",
          census_run(cen_imports="A1 A2 A3 A4", rival_imports="A1 A2 A3 A4 A5",
                     sentence="Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
                              " `FormalSchemes.A4` and `FormalSchemes.A5`: nothing is measured"
                              " here.  This file is a leaf, and `FormalSchemes.Rival` is the only"
                              " one of the 10 that reaches all five -- 1 reaches none, 6 reach"
                              " exactly one, 1 reaches two and 1 reaches four"),
          ([], [], []))

    # **The checksum's *ambiguous* case, which row 2224 decision 1 calls out by name --
    # *"do not try both and accept either"* -- and which nothing pinned until row 2227's mutation
    # battery asked.** Every case above resolves through exactly one of `own` and `hop` because only
    # one of them numbers the spelled cardinality, so they measure that the checksum is **there**;
    # they say nothing about what it does when **both** number it and the two sets differ.  Here the
    # opener names `A1`..`A5` and the census's own sentence names `A1`..`A4` and `Rival` -- five
    # each, different sets -- and every numeral is correct for the opener's reading.  The species
    # must **decline**: a resolver preferring one source outright answers this silently and
    # correctly by luck, which is the failure mode the checksum exists to make impossible rather
    # than unlikely.
    check("two candidate subject sets both numbering the spelled cardinality is a decline, not a "
          "preference for one of them",
          census_run(sentence="Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
                              " `FormalSchemes.A4` and `FormalSchemes.A5`: nothing else is measured"
                              " here.  It needs `FormalSchemes.A1`, `FormalSchemes.A2`,"
                              " `FormalSchemes.A3`, `FormalSchemes.A4` and `FormalSchemes.Rival` at"
                              " once, and this module is the only one of the 10 that reaches all"
                              " five -- 1 reaches none, 6 reach exactly one, 1 reaches two and"
                              " 1 reaches four"),
          ([], ["the set this census is of does not resolve to the 5 it spells"
                " (5 named here, 5 in the opener one sentence back)"], []))

    # **`IDENTITY_DISPOSITION`'s first remedy, followed on a live tree in both census idioms, which
    # is where the two come apart.**  The remedy reads *say it of the module the walk gives*, and a
    # `--selftest` case asserting which remedy a mismatch carries does not say whether following it
    # helps -- #815 was rejected for advice that did nothing, so the rule on this file is to run
    # every branch.  Both trees below start genuinely red (`Rival` reaches all five, the sentence
    # says this module does) and both go green under the repair.  What differs is whether the census
    # is still **read** afterwards, and it turns on where the subject set is written:
    #
    # * **the subject set one sentence back, before the opener's colon** -- naming the rival adds a
    #   token to the census's own sentence, `own` becomes 1 against a spelled 5, the hop still
    #   numbers 5, so the checksum still resolves to exactly one candidate and the four buckets, the
    #   universe and the remainder stay checked.  The identity itself is gone, correctly: the claim
    #   is now about a named module and `_identity_is_self` says so;
    # * **the subject set in the census's own sentence** -- the same repair takes `own` from 5 to 6
    #   against a spelled 5, the hop numbers 0, no candidate matches, and the **whole census
    #   declines**.  Green, with the reason spelled out, and no longer checked.
    #
    # Both are safe and the disposition keeps its promise, which is to dispose of the red.  But an
    # author repairing a live census of the second shape loses the check without being told, so
    # `CONTRIBUTING.md`'s census bullets say which idiom survives the repair and this pins both
    # halves of that sentence.
    HOP = ("Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`, `FormalSchemes.A4`"
           " and `FormalSchemes.A5`: nothing else is measured here.  And %s is the only one of the"
           " 10 that reaches all five -- 1 reaches none, 6 reach exactly one, 1 reaches two and"
           " 1 reaches four")
    OWN = ("Nothing else is measured here.  It needs `FormalSchemes.A1`, `FormalSchemes.A2`,"
           " `FormalSchemes.A3`, `FormalSchemes.A4` and `FormalSchemes.A5` at once, and %s is the"
           " only one of the 10 that reaches all five -- 1 reaches none, 6 reach exactly one,"
           " 1 reaches two and 1 reaches four")
    swapped = dict(cen_imports="A1 A2 A3 A4", rival_imports="A1 A2 A3 A4 A5")
    check("both census idioms red on the identity, so the repair below is a repair and not a "
          "no-op",
          (census_run(sentence=HOP % "this module", **swapped)[0],
           census_run(sentence=OWN % "this module", **swapped)[0]),
          ([(1, 0, "this file among the modules reaching all 5, which this sentence says it is"
                   " the only one of"),
            (0, 1, "the modules besides this one reaching all 5, which this sentence says is"
                   " none -- the walk gives `FormalSchemes.Rival`")],) * 2)
    check("following the identity's own remedy keeps the census checked when the subject set is "
          "one sentence back, and declines it when the subject set is in the census's own sentence",
          (census_run(sentence=HOP % "`FormalSchemes.Rival`", **swapped),
           census_run(sentence=OWN % "`FormalSchemes.Rival`", **swapped)),
          (([], [], []),
           ([], ["the set this census is of does not resolve to the 5 it spells"
                 " (6 named here, 0 in the opener one sentence back)"], [])))

    # And the same shape the other way round, so the pair is not one-sided: a *named* module
    # standing earlier in the sentence does not stop the claim being about this file when the
    # self-phrase is what the claim is made of.  This is `:393`'s own word order -- *"it needs `A`,
    # `B` and `C` at once, and this module is the only one of the 587"* -- and a gate that took the
    # last **named** module instead of the last anchor would lose the tree's one live identity.
    check("a module named earlier in the sentence does not stop `this module is the only one` "
          "being about this file",
          census_run(cen_imports="A1 A2 A3 A4", rival_imports="A1 A2 A3 A4 A5",
                     sentence="It needs `FormalSchemes.A1`, `FormalSchemes.A2`,"
                              " `FormalSchemes.A3`, `FormalSchemes.A4` and `FormalSchemes.A5` at"
                              " once, and this module is the only one of the 10 that reaches all"
                              " five -- 1 reaches none, 6 reach exactly one, 1 reaches two and"
                              " 1 reaches four")[0],
          [(1, 0, "this file among the modules reaching all 5, which this sentence says it is"
                  " the only one of"),
           (0, 1, "the modules besides this one reaching all 5, which this sentence says is"
                  " none -- the walk gives `FormalSchemes.Rival`")])

    # And the prose gate, which `invisible`'s docstring gives the general argument for: `reaches` is
    # not Lean syntax but a numeral beside it in a proof body is not a census either, and a census
    # report quoting a run of tactic script would be read as advice about a sentence.  Without the
    # gate this tree acquires a decline it has no sentence for.
    check("a bucket-shaped phrase in code is not a census",
          census_run(quiet_body="/-! Nothing measured here. -/\n"
                                "theorem two_reaches : 2 reaches two := trivial\n"),
          ([], [], []))

    # `the only one of the N` needs its `only`.  *One of the N* is a membership statement and names
    # no universe -- there are N of them and this is one -- so a sentence spelling it that way has
    # not said what set its buckets partition, and the species declines rather than assuming the
    # tree.  Every figure in this fixture is otherwise correct, which is what makes the decline the
    # assertion.
    check("`one of the N` without `only` states no universe, so the census declines",
          census_run(sentence="Over `FormalSchemes.A1`, `FormalSchemes.A2`, `FormalSchemes.A3`,"
                              " `FormalSchemes.A4` and `FormalSchemes.A5`: this module is one of"
                              " the 10 that reaches all five -- 1 reaches none, 6 reach exactly"
                              " one, 1 reaches two and 1 reaches four")[:2],
          ([], ["the set being partitioned is not stated, or is stated twice"]))

    # `--edge` does not price a bucket, and this is the pair of cases that says so without the
    # assertion being vacuous.  `Q` gaining `FormalSchemes.A1` moves it out of the *reaches none*
    # bucket, so the figures really do move -- the first case writes that import and watches the
    # census go red -- and the second prices the same edge on the tree without it and finds nothing,
    # with `UNCLASSIFIED` empty.  A bucket is a figure about the whole tree's partition rather than
    # any module's closure, so the three species `--edge` reports are not exhaustive for it and its
    # `UNCLASSIFIED` line would be the wrong thing to print; see `edge_cost`.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        census_tree(d, write)
        r = edge_cost(d, "FormalSchemes.Q", "FormalSchemes.A1")
        check("the edge moves a bucket, and --edge prices none of them",
              ([(stated, actual) for stated, actual, _what in census_run(
                  quiet_body="import FormalSchemes.A1\n/-! Nothing measured here. -/\n")[0]],
               len(r["brought"]), r["population"], r["species"][0]),
              ([(1, 0), (6, 7)], 1, [], []))

        # And `--stub`, where the answer is the **opposite** and `stub_cost`'s comment says why: a
        # stub over `Cen` reaches all five, so it lands in the top bucket and moves both the
        # universe and the only-one claim -- which is a module's price and not an import's.  This
        # case is the rewrite of row 2224's *"--stub prices no census figure either"*, which existed
        # to make the day the filter was lifted loud rather than silent; row 2227 lifted it, and the
        # assertion is now that the figures arrive, that they arrive in **species 1** beside the
        # project total rather than under `UNCLASSIFIED`, and that nothing at all reaches species 0.
        # Asserted by value and not by count: a count would pass on three figures about the wrong
        # thing, and the `what` strings are what say which assertion each one is.
        # And the same population **rendered**, because species 1's body label is the only place a
        # reader learns which species a figure landed in and `stub_cost`'s return value cannot be
        # wrong about a word.  It read `total` while a census could not reach it; a report calling
        # a census bucket *total* would satisfy every structural case here.
        check("the report files a census figure under a label that names a census, not under the "
              "project total's",
              tree_report(d, "--stub", "FormalSchemes.ZStub:FormalSchemes.Cen")[1][-2:],
              ["  total/census  FormalSchemes/Cen.lean:1  the size of the set this census"
               " partitions: states 10, the stub would give 11",
               "  total/census  FormalSchemes/Cen.lean:1  the modules besides this one reaching"
               " all 5, which this sentence says is none -- the walk gives"
               " `FormalSchemes.ZStub`: states 0, the stub would give 1"])

        s = stub_cost(d, "FormalSchemes.ZStub", ("FormalSchemes.Cen",))
        check("a stub lands in the top bucket, and --stub prices every census figure it moves",
              (s["size"], s["hypo_size"], len(s["population"]), s["species"][0], s["species"][2],
               [(c["stated"], c["actual"], c["what"]) for c in s["species"][1]]),
              (10, 11, 2, [], [],
               # Two and not three: the stub joins the top bucket, so *this file is in it* stays
               # true and only the exclusivity half of the identity fires.  That asymmetry is the
               # two-figure split working, and a count alone would not show it.
               [(10, 11, "the size of the set this census partitions"),
                (0, 1, "the modules besides this one reaching all 5, which this sentence says is"
                       " none -- the walk gives `FormalSchemes.ZStub`")]))

    # **The identity, rendered.**  Every other census case above reads `audit`'s return value, and
    # on this population that is not enough: the defect the two-figure split repairs was a
    # *rendering* -- `stated=1, actual=len(only)` printed as `states 1, walk gives 1`, under a
    # remedy telling the reader to re-run a walk that gives the same number.  A fixture reading
    # `(stated, actual, what)` asserts the tuple it is handed and cannot see the sentence built
    # from it, which is the gap row 2218 built `tree_report` to close for the incumbents.  So this
    # is the block **by value**: both figures, the module the walk found spelled inside the first
    # line rather than left to the reader, and `IDENTITY_DISPOSITION` under each instead of
    # `BUCKET_DISPOSITION`.  A tree of its own because `census_tree`'s `Cen` has no sentence break
    # before its census, so its rendered `text` line is a run of `import` statements.
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "FormalSchemes"))

        def write(name, body):
            with open(os.path.join(d, "FormalSchemes", name + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)

        for i in (1, 2, 3):
            write("A%d" % i, "/-! Nothing measured here. -/\n")
        write("Rival", "import FormalSchemes.A1\nimport FormalSchemes.A2\nimport FormalSchemes.A3\n"
                       "/-! Nothing measured here. -/\n")
        write("Cen", "import FormalSchemes.A1\n/-!\nNothing else is measured here.\n"
                     "Over `FormalSchemes.A1`, `FormalSchemes.A2` and `FormalSchemes.A3`: this"
                     " module is\nthe only one of the 5 that reaches all three -- 4 reach exactly"
                     " one.\n-/\n")
        text = ("            Over `FormalSchemes.A1`, `FormalSchemes.A2` and `FormalSchemes.A3`:"
                " this module is the onl")
        advice = ["            (this one is not a numeral.  The sentence names which module is the"
                  " top bucket's sole",
                  "             member and the walk names a different set, so the repair is the"
                  " **name** -- say it of",
                  "             the module the walk gives, or drop the claim.  To refuse the"
                  " reading instead, elide the",
                  "             spelled cardinality or drop the `N reach ...` spelling.)"]
        rc, lines = tree_report(d)
        check("the identity prints as two figures, names the module the walk found, and carries "
              "its own remedy rather than the bucket species'",
              (rc, rows(lines)),
              (1,
               ["  MISMATCH  FormalSchemes/Cen.lean:4  this file among the modules reaching all 3,"
                " which this sentence says it is the only one of: states 1, walk gives 0",
                text] + advice +
               ["  MISMATCH  FormalSchemes/Cen.lean:4  the modules besides this one reaching all 3,"
                " which this sentence says is none -- the walk gives `FormalSchemes.Rival`:"
                " states 0, walk gives 1",
                text] + advice))

    return 1 if bad else 0


def parse_edge(arg: str) -> tuple[str, str]:
    """`A:B` split in two, or the usage message.

    Its own function so that `--selftest` can pin it: the empty string used to reach `main`'s
    `if args.edge:` as **falsy** and fall through to the tree audit, which neither reports nor
    fails but silently answers a different question.  `main` now tests `is not None` and this
    arity check is what the empty string meets."""
    if arg.count(":") != 1:
        raise SystemExit("--edge takes `FormalSchemes.A:FormalSchemes.B`")
    a, b = arg.split(":")
    return a, b


def parse_stub(arg: str) -> tuple[str, tuple[str, ...]]:
    """`NAME:A,B,C` split into the stub's name and its imports, or the usage message.

    `NAME` with **no colon** is a stub importing nothing -- a legal experiment and the cheapest one,
    since it prices the project totals alone.  `NAME:` is refused rather than read as that, because
    the two spellings would otherwise differ by a character nobody would notice in a shell history.

    Its own function for `parse_edge`'s reason, and against the same trap: `--stub ''` has to reach
    an arity check rather than fall past `main`'s branch into the tree audit, which neither reports
    nor fails but silently answers a different question.
    """
    usage = ("--stub takes `FormalSchemes.New:FormalSchemes.A,FormalSchemes.B`, or"
             " `FormalSchemes.New` for a stub that imports nothing")
    if arg.count(":") > 1:
        raise SystemExit(usage)
    name, colon, rest = arg.partition(":")
    imports = tuple(rest.split(",")) if colon else ()
    # `all` catches every empty component at once: a trailing comma, a doubled comma and a bare
    # `NAME:` are one mistake with three spellings, and an empty module name reaching `stub_cost`
    # would be reported there as *not a module of this tree*, which names the wrong defect.
    if not name or not all(imports):
        raise SystemExit(usage)
    return name, imports


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
    g.add_argument("--stub", metavar="NAME:A,B,...",
                   help="price adding a module NAME importing exactly A,B,... -- the experiment"
                        " CONTRIBUTING.md's `What adding a module costs` prescribes.  Reports a"
                        " tree that does not exist, so it never fails")
    args = ap.parse_args()
    if args.selftest:
        # `--selftest`'s **output shape** is part of its contract and nothing read it until row 2225
        # goal 3: one line per case, so the tail of the output is the last case and `grep -c ok` is
        # the case count.  Goal 1 above is what happens without this -- a case that calls `main`
        # for its return value prints a whole report into the middle of the list, and the run still
        # exits 0, so the first reader to notice was counting lines a week later.
        #
        # **A literal case count was the other candidate and is declined here, with the reason.** It
        # catches a different defect -- a block of cases skipped by an early `return`, which the
        # shape says nothing about -- at the price of one numeral to bump per case added, on a file
        # that gained 22 cases in one day; and four rows quoted that count stale inside one day
        # without it ever being wrong in the file.  What is cheap is to *publish* it rather than
        # assert it: the line below is a live measurement of both figures, so a dropped block shows
        # up as a count a reader can diff across two runs, exactly as `--tree`'s header counts do.
        # Whoever wants the assertion should read this comment first and say why the churn is worth
        # it, rather than take the silence for an oversight.
        #
        # Buffered rather than teed, which costs the streaming: `--selftest` is **0.15 s** at
        # `ab0a3b4`, so there is nothing to stream, and a `finally` keeps the output of a run that
        # raised.  Locals for the reason `selftest`'s own imports are local -- no other mode here
        # captures a stream.
        import contextlib
        import io
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf):
                rc = selftest()
        finally:
            sys.stdout.write(buf.getvalue())
        # A diagnostic line under a FAIL is eight spaces in: that is `check`'s own spelling and the
        # only third shape this output has.
        stray = [ln for ln in buf.getvalue().splitlines()
                 if not ln.startswith(("ok  ", "FAIL", "        "))]
        # This line is itself one, and it is the last, so `grep -c ok` over the whole run is the
        # figure below plus one -- said here because a count quoted off this output has been wrong
        # four times in a week and an off-by-one is the cheapest way for that to happen again.
        print("%s  %s: %d of them cases, %d stray"
              % ("ok  " if not stray else "FAIL",
                 "every line --selftest printed is a case line, which is what makes `grep -c ok` a"
                 " reading of the case count",
                 len([ln for ln in buf.getvalue().splitlines() if ln.startswith(("ok  ", "FAIL"))]),
                 len(stray)))
        for ln in stray[:3]:
            print("        stray: %s" % ln[:100])
        return rc or bool(stray)
    # `is not None`, not truthiness: `--edge ''` is a malformed argument and has to reach
    # `parse_edge`, not fall past this branch into the tree audit.
    if args.edge is not None:
        report_edge(edge_cost(".", *parse_edge(args.edge)))
        return 0
    # `is not None` for `--edge`'s reason, and it is the same bug: `--stub ''` is a malformed
    # argument and has to reach `parse_stub`.
    if args.stub is not None:
        report_stub(stub_cost(".", *parse_stub(args.stub)))
        return 0

    mods = project_modules()
    if args.sweep:
        blind = list(invisible(mods))
        print("sentences --tree cannot see (a numeral with a closure marker, a counterfactual"
              " price, or an unreadable project total or tree census): %d" % len(blind))
        print("(Mathlib-closure sentences excluded; most of the rest are deltas, intersections or\n"
              " numerals that are not closure figures -- this is a reading list, not a failure\n"
              " list.  A plain measurement of this tree in here should be rewritten in the\n"
              " `forward closure` / `reverse closure` spelling, and one endpoint of every delta\n"
              " is such a measurement.  A counterfactual price -- `N figure repairs` -- is the"
              " one\n"
              " shape here that cannot be rewritten that way at all, because its subject is a"
              " tree\n"
              " that does not exist: re-run `--edge` or `--stub`, and date what you write.)")
        for c in blind:
            print("  invisible %s:%d  %s" % (c["path"], c["line"], c["text"][:150]))
        return 0

    mismatches, declined, size_declined, census_declined = audit()
    attributed = [c for c in claims(mods) if c["about"] is not None]
    sized = [c for c in size_claims(mods) if c["about"] is not None]
    censuses = [c for c in census_claims(mods) if not c.get("declined")]
    print("modules under FormalSchemes/ : %5d" % len(mods))
    print("closure claims attributed    : %5d" % len(attributed))
    print("  figures checked            : %5d   (the claims and their companion figures)"
          % (len(attributed) + sum(len(c["companions"]) for c in attributed)))
    print("project totals checked       : %5d   (the tree's own module count; no subject, and no"
          % len(list(total_claims(mods))))
    print("                                       host claim needed -- see the docstring)")
    print("  MISMATCH                   : %5d" % len(mismatches))
    print("  declined (see below)       : %5d" % len(declined))
    print("  invisible (run --sweep)    : %5d   (not a failure: spellings `CLOSURE` cannot read)"
          % len(list(invisible(mods))))
    print("size claims attributed       : %5d   (`N lines` / `M declarations`; commit counts are"
          % len(sized))
    print("  declined (see below)       : %5d    out of reach -- see the module docstring)"
          % len(size_declined))
    print("census buckets checked       : %5d   (a partition of the tree by how much of a"
          % sum(len(c["buckets"]) for c in censuses))
    print("                                       named set each module reaches -- the subject")
    print("                                       set, its spelled cardinality and the universe")
    print("                                       are all read from the sentence)")
    print("  censuses read              : %5d" % len(censuses))
    print("  declined (see below)       : %5d" % len(census_declined))
    for c in sorted(mismatches, key=lambda c: (c["path"], c["line"])):
        what = c.get("what") or "the %s closure of `%s`" % (c["kind"], c["about"])
        print("  MISMATCH  %s:%d  %s: states %d, walk gives %d"
              % (c["path"], c["line"], what, c["stated"], c["actual"]))
        print("            %s" % c["text"])
        # A total is the one species with no decline, so the one line of advice it needs is the
        # disposition for a sentence that is **right** and is being read as the wrong thing.  It is
        # printed per mismatch and not once at the foot on purpose: the author who trips this reads
        # the line under their own file's name, and a footnote after 24 declines is not read at all.
        # The claim carries its own lines because the remedy is the **species'** and `TOTAL` and
        # `CENSUS` share a `kind`, with opposite remedies -- see `TOTAL_DISPOSITION` (row 2214).
        for line in c.get("disposition") or ():
            print("            %s" % line)
    for c in sorted(declined, key=lambda c: (c["path"], c["line"])):
        print("  declined  %s:%d  %s -- %s" % (c["path"], c["line"], c["declined"], c["text"]))
    for c in sorted(size_declined, key=lambda c: (c["path"], c["line"])):
        print("  size-declined  %s:%d  %s -- %s"
              % (c["path"], c["line"], c["declined"], c["text"]))
    for c in sorted(census_declined, key=lambda c: (c["path"], c["line"])):
        print("  census-declined  %s:%d  %s -- %s"
              % (c["path"], c["line"], c["declined"], c["text"]))
    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
