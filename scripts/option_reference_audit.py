#!/usr/bin/env python3
"""Check that a comment saying *"the same transparency requirement as `X`"* is true of `X`.

This tree justifies every `set_option` in an adjacent comment, and a large number of those
comments are **cross-references**:

    set_option linter.style.setOption false in
    set_option backward.isDefEq.respectTransparency false in
    -- Same transparency requirement as `completion_glue_condition`, for the same reason.

That sentence is a claim about `completion_glue_condition`, **not about the file it sits in**.
The moment a refactor removes the option from `completion_glue_condition`, the sentence is false
-- and the sentence can be anywhere on the tree, in a file the refactor never opened.

Nothing else here can see that.  `closure_audit.py` is byte-identical across such a repair: these
sentences carry no anchor-plus-figure, so they are not in its population at all.
`citation_audit.py` resolves the name fine -- the declaration exists; what is false is a
*property* attributed to it, which the audit does not model.  `docstring_signature_scan.py` reads
docstrings against signatures, and these are `--` line comments about something not in the
signature.  And `lake build` cannot read English: **removing an option cannot fail a build**, so
the whole class is invisible to CI by construction.

It is not hypothetical.  Issue 2064 removed `backward.isDefEq.respectTransparency false` from four
declarations.  Its author found one stale cross-reference by eye, repaired it, and wrote *"every
docstring is repaired, including the cross-references"*; a reviewer reading the diff by hand found
**three** more, one of them in a file the pull request never touched.  That is not carelessness --
it is what happens when the only instrument is a human reading a diff.

Usage, from the repository root -- no build needed, this reads sources:

    python3 scripts/option_reference_audit.py --tree
    python3 scripts/option_reference_audit.py --selftest

`--tree` exits 1 on any `MISMATCH` and 0 otherwise.  Run it from any row that **removes** a
`set_option`, which is the edit that falsifies these sentences.

## What is checked, and what is deliberately not

One thing: *does the declaration this sentence names still carry an option of the family the
sentence claims?*  Whether the stated **reason** is the true reason is not mechanically decidable
and is out of scope -- a sentence can say "for the same reason" about two genuinely different
reasons and no scanner will know.

## Both spellings of `set_option`, kept apart

An option reaches a declaration two ways, and this tree uses the second one far more:
`set_option NAME VALUE in` attaches to the next declaration, while a bare `set_option NAME VALUE`
applies to the rest of the enclosing scope and so is carried by every declaration below it until
the `end` of the `section` or `namespace` it sits in.  **258 of this tree's 406 non-linter
options are the second kind, and all 258 are budget raises** -- so a table built only from the
`... in` form answers *"carries nothing"* for most of the tree and reports a false `MISMATCH` on
every true sentence about a budget.  The census is beside `SET_OPTION` below.

The two are recorded separately rather than unioned, because they are different strengths of
truth: a declaration that carries its own raise is a stronger subject than one that merely sits
below a file-scoped raise.  `--tree` marks the weaker case `file-scoped` on the line it checks,
so a reader can see which answered without opening the file.

File-scoped `linter.*` options are the one exclusion, and it is load-bearing rather than tidy --
every module carries `linter.style.header false`, so attributing it would make the fallback
family `any` vacuously true tree-wide.  Measured: it turns both of the tree's standing
`MISMATCH`es into passes.  A *scoped* `linter.style.setOption false in` is a different thing and
stays in; it is written one declaration at a time, beside the option it suppresses the linter for.

## The scope stack, and the figure that watches it

*"The rest of the enclosing scope"* means the scanner has to know where scopes open and close,
and it learns that from three regexes: `NAMESPACE`, `SECTION` and `END`.  Two things ride on the
same stack -- which `namespace` qualifies a declaration's name, and which `end` reverts a bare
`set_option` -- so an opening line one of them misses is a hole in both at once.  Measured
against Lean rather than reasoned about, with a command that prints `getOptions` at each point:
a raise written at namespace scope still reads `some 400000` after an inner section's `end`, and
one written inside that section reads `none` immediately after it.  Both readings are pinned by
a case.

`SECTION` read only the bare spelling until issue 2130, and **`noncomputable section` is 546 of
this tree's 975 section-opening lines** -- so 239 of the 582 files closed a scope the walk had
never opened, and each of those `end`s popped the enclosing *namespace* instead.  Nothing said
so: the two guards that stop the stack popping past empty are exactly where a missed opener goes
quiet.  So `option_table` now returns the underflow count as well, and `--tree` prints it as
`scope stack underflows`.  It is **0** on this tree and the point of it is the day it is not:
**a blind spot that prints no number is indistinguishable from no blind spot.**

## The family question: matched on the English word

`maxHeartbeats` and `backward.isDefEq.respectTransparency` are the two options that carry
cross-references on this tree today, and the words the sentences use are *transparency*,
*defeq*, *budget*, *heartbeats* and *raise*.  The classification here is on the **English word**
and not on the option name, because the English word is what the sentence actually claims: a
comment saying *"the same transparency requirement"* about a declaration that carries only a
`maxHeartbeats` raise is exactly the near-miss worth catching, and a scanner that collapsed both
into "carries some option" would pass it.

The cost of that choice is sentences whose noun names no family at all -- *"the same option"*,
*"the same accommodation"*.  Those fall back to the family `any`, which asks only that the anchor
carry some option at all; that is weak, and it is reported as an attributed check rather
than hidden, because a declaration that carries **no** option at all is the case these sentences
actually go wrong in.  The measurement that justifies keeping the split is in `--tree`'s
`by family` line: the tree's cross-references are majority-`transparency`, so the strong
classification is the common case and not the exception.

## Declined, and why history is one of its reasons

`declined` is copied from `closure_audit.py`, including its posture: it is the honest statement
that the scanner could not rule, it is **not** a failure, and it is printed in full so it can be
walked by hand rather than counted.  Four reasons:

* **not on this tree** -- the anchor resolves to nothing under `FormalSchemes/`; it is a Mathlib
  declaration, or a name this tree only ever mentions.  Their options are not this tree's to know.
* **ambiguous** -- two declarations answer to the name and they **disagree** about the family.
  When namesakes *agree* the sentence is judged anyway, because it is then false (or true) under
  either reading; only a genuine disagreement is declined.  Both cases are pinned in `--selftest`.
* **anchor not a module of this tree** -- a `.lean` path or dotted module name with no file
  answering to it.
* **history** -- the sentence is in the past tense (*"`X` above needed the same option until issue
  2064 rerouted it"*).  That is this tree's repair idiom for exactly the defect this script
  checks, so firing on it would un-repair the repair.  It is declined rather than skipped so that
  a change to the idiom shows up in the report instead of silently shrinking the population.

## A module anchor is checked, not declined

Nine of this tree's cross-references name a **module** rather than a declaration -- *"the same
accommodation `ThickeningCocone.lean` carries"*, *"as `FormalSchemes/SpfBasicOpenCover.lean`
records for the same field"*.  Issue 2106 expected those to be the commonest *declined* case, and
on the reading that the scanner must pick which of the file's declarations is meant, they would
be: that is a guess `closure_audit.py` would refuse to make and so does this.

But the sentence does not claim anything about a particular declaration.  It claims the **module**
makes the accommodation, and that is checkable without choosing: does any declaration in that
module carry an option of the family?  So they are attributed, against the union of the options
the module's declarations carry.  The check is weaker than the per-declaration one -- a module
keeps passing while
one of thirty declarations still carries the option -- and it is exactly as strong as the sentence
is, which is the property that matters.  It fires when the module drops the accommodation
altogether, which is the way these sentences actually go wrong.

The measured cost of declining them instead: `--tree` reports **12** attributed against **15**
declined, a scanner whose declined block is bigger than the population it rules on -- which issue
2106 names as the sign of one that is measuring nothing.  Checking them makes it **22** against
**5**, and turns one of the two standing `MISMATCH`es from invisible into reported.

## Which backtick is the anchor

The sentence usually names several.  *"Same transparency requirement as `range_specLRSGlueData_f`
above, and for the same reason: the glue datum is a `def`, so `D.specLRSGlueData.J` does not
reduce to `D.J`"* names four, and only the first is the claim's subject.  So a token is an anchor
only when the grammar makes it one: **preceded by a comparison connective** (`as`, `as in`,
`that`, `than`, or `and` continuing a list that already has one) **or followed by a cross-reference
verb** (`needs`, `carries`, `makes`, `records`, `requires`, `uses`, `wants`).

`does` and `has` are deliberately **not** cross-reference verbs, even though *"exactly as `X`
does"* is a real spelling here: in that spelling the `as` already makes `X` an anchor, while
admitting a bare *"`Y` does"* would make an anchor of `D.specLRSGlueData.J` in the sentence above.
The rule that matters is pinned by a loosening in `--selftest`.
"""

import argparse
import contextlib
import glob
import io
import os
import re
import sys

# `set_option NAME VALUE in` -- the form that attaches to the next declaration, and
# `set_option NAME VALUE` with no `in` -- the form that applies to the rest of the enclosing
# scope.  **Both are carried by the declarations below them**, and the second is where this
# tree spells most of its budget raises.  Censused over `FormalSchemes/**/*.lean` (582 files)
# through `code_only`, at `0c91a57`:
#
#     form                   total   non-linter   which options
#     scoped, `... in`         312          148   92 backward.isDefEq.respectTransparency,
#                                                 42 maxHeartbeats, 8 synthInstance.maxHeartbeats,
#                                                 5 backward.defeqAttrib.useBackward, 1 maxRecDepth
#     file-scoped, no `in`    1015          258   132 maxHeartbeats,
#                                                 120 synthInstance.maxHeartbeats, 6 maxRecDepth
#                                                 -- and nothing else
#
# So of the two families below, `transparency` is 97/97 scoped and fully covered, while
# `heartbeats` is 51 scoped against 258 file-scoped across 132 of the 582 files.  Reading only
# the `... in` form left ~83% of the budget population invisible and every sentence about a
# file-scoped raise a false `MISMATCH`.
SET_OPTION = re.compile(r"^\s*set_option\s+([A-Za-z0-9_.]+)\s+\S+\s+in\s*$")
FILE_SET_OPTION = re.compile(r"^\s*set_option\s+([A-Za-z0-9_.]+)\s+\S+\s*$")

# The one form that is boilerplate, and the only reason the old comment's "582" looked right:
# `linter.style.header false` is exactly one line in each of the 582 modules.  File-scoped
# `linter.*` options are excluded from the table, and that exclusion is load-bearing rather than
# tidy -- attributing them would give **every** module an option, which makes the fallback
# family `any` vacuously true tree-wide.  Measured: it turns both standing `MISMATCH`es
# (`FormalSchemes.Gluing`, `AlgebraicGeometry.ChartedSchemeDatum.specGD_f`) into passes, because
# each of those files carries `linter.style.header` and nothing else file-scoped.  A *scoped*
# `linter.style.setOption false in` is a different thing and stays in: it is written one
# declaration at a time, beside the option it is suppressing the linter for.
FILE_SCOPED_BOILERPLATE = re.compile(r"^linter\.")

# `set_option ... in example` -- an `example` is a command, so it consumes the pending options
# and they must not fall through to the next named declaration.  The population of that shape is
# **0** on this tree, so this changes no verdict here; it is written because this loop is where
# such a hole would live and a table nobody has watched go wrong is not a table.
EXAMPLE = re.compile(r"^\s*example\b")

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                  r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)"
                  r"\s+([^\s({\[:⦃⟨]+)")
# The three openers the scope stack is built from.  Two things ride on that stack -- qualifying
# a declaration by its `namespace`, and the scope a bare `set_option` reverts at -- so an opening
# line one of these misses is a hole in both.  Censused over `FormalSchemes/**/*.lean` (582
# files) through `code_only`:
#
#     regex       matches   opening lines of its kind that it misses
#     NAMESPACE       850   0
#     SECTION         975   0   -- 429 bare `section`, 546 `noncomputable section`
#     END            1518   0   -- and 0 of them indented, which would be a false pop
#
# `SECTION` read only the bare spelling until issue 2130, which missed all 546 of the other one
# and left 239 files closing a scope the scanner never opened.  `noncomputable` is the only
# modifier admitted, and the reason is Lean's parser rather than this tree's habits: `private
# section` and `protected section` are both rejected at the `section` token itself
# (`unexpected token 'section'; expected 'lemma'`, measured), so admitting them would be
# admitting syntax that cannot occur, not syntax this tree happens not to write.
NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")
SECTION = re.compile(r"^\s*(?:noncomputable\s+)?section\b\s*(\S*)")
END = re.compile(r"^\s*end\b\s*(\S*)")

# The option families, keyed by the English word a sentence uses for them.  `any` is the fallback
# and is not in here: it accepts every scoped option name.
FAMILIES = {
    "transparency": re.compile(r"Transparency|defeqAttrib"),
    "heartbeats": re.compile(r"[Hh]eartbeats|maxRecDepth"),
}
FAMILY_WORDS = [
    ("transparency", re.compile(r"\b(?:transparency|defeq)\b", re.I)),
    ("heartbeats",
     re.compile(r"\b(?:heartbeats?|budget|raise[sd]?|elaboration\s+budget)\b", re.I)),
]

# The nouns a comparison has to be *about* before it is one of ours.  `reason` is pointedly
# absent: "for the same reason" is in most of these sentences and is never itself the claim.  So
# is `rule` -- see `is_candidate` for the sentence that cost.
SUBJECT = (r"heartbeats?|budget|raises?|allowance|accommodation|"
           r"options?|requirements?|suppressions?|set_option")
SAME = re.compile(r"\bsame\b", re.I)
SUBJECT_RE = re.compile(r"\b(?:%s)\b" % SUBJECT, re.I)
ANY_FAMILY = re.compile(r"\b(?:transparency|defeq|heartbeats?|budget)\b", re.I)
CARRY_VERB = re.compile(r"\b(?:needs?|carr(?:y|ies)|sets?|takes?|requires?|uses?|raises?|wants?)"
                        r"\s+(?:the\s+|an?\s+)?$", re.I)

# `same reason` is a connective and `reason` is not a noun, which is not a contradiction: *"for
# the same reason `thickeningMap_comp` does"* points at a declaration, while *"for the same
# reason: the glue datum is a `def`"* -- the far commoner shape -- has a colon between them and
# so does not end with the connective.
CONNECTIVE = re.compile(r"(?:\b(?:as|as\s+in|that|than)|\bsame\s+reason)\s+$", re.I)
CONJUNCTION = re.compile(r"\b(?:and|or|,)\s+$", re.I)
# A qualifier in parentheses, a locator and a comma all routinely sit between the anchor and its
# verb on this tree -- *"`specTwoPatch_glue` (`FormalSchemes.CompletionTwoPatchToScheme`) needed"*,
# *"`specAwayMap_comp_specι` below, needed"*.  Skipping them is what lets the repaired past-tense
# notes be *seen* and declined as history rather than being silently outside the population.
XREF_VERB = re.compile(r"^\s*(?:\([^)]*\))?\s*(?:above|below|here|itself)?,?\s*"
                       r"(?:needs?|needed|carr(?:y|ies|ied)|makes?|records?|requires?|uses?|"
                       r"wants?)\b", re.I)

# Past-tense markers.  The repair idiom issue 2064 established is to demote a cross-reference to
# history rather than delete it, so these sentences are the *fixed* ones and must not fire.
HISTORY = re.compile(r"\b(?:needed|used\s+to|no\s+longer|formerly|until|has\s+since|had)\b", re.I)

BACKTICK = re.compile(r"`([^`\n]+)`")
IDENTIFIER = re.compile(r"^[^\s`]+$")


def comment_only(text: str) -> str:
    """`text` with every *code* character blanked, keeping line and column positions.

    The mirror of `closure_audit.py`'s `code_only`, and blanked rather than deleted for the same
    reason: an offset in the result is an offset in the file on disk, so a match can be reported
    at the line it is actually on.  `/- ... -/` nests; `--` runs to end of line outside one.
    String literals are not tracked, which on this tree is a population of zero.
    """
    out, depth = [], 0
    for line in text.split("\n"):
        buf, i = [], 0
        while i < len(line):
            if depth == 0 and line.startswith("--", i):
                buf.append(line[i:])
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
            buf.append(line[i] if depth else " ")
            i += 1
        out.append("".join(buf))
    return "\n".join(out)


def code_only(text: str) -> str:
    """`text` with every comment blanked, keeping line and column positions.

    Pass 1 reads this and not the raw file: a module docstring that quotes a `set_option` line in
    a fenced example would otherwise be read as a declaration carrying that option, which is the
    failure that looks plausible -- it would make a stale sentence *pass*.
    """
    out, depth = [], 0
    for line in text.split("\n"):
        buf, i = [], 0
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


OWN, INHERITED = "own", "file"


def _merge(into: dict[str, str], carried: dict[str, str]) -> None:
    """Union `carried` into `into`, never downgrading an `own` record to an `INHERITED` one."""
    for option, scope in carried.items():
        if into.get(option) != OWN:
            into[option] = scope


def option_table(sources: dict[str, str]) -> tuple[dict[str, dict[str, str]],
                                                   dict[str, dict[str, str]],
                                                   dict[str, int]]:
    """Pass 1: the options carried, by declaration and by module, each tagged with its scope.

    A `set_option ... in` binds to the next declaration, across any number of intervening
    comments, attributes and other `... in` modifiers, so the pending set is cleared by a
    declaration and by nothing else -- `@[reassoc]` and `include ... in` on lines of their own
    are 363 and 672 lines of this tree and are correctly transparent here.  Names are qualified
    by the `namespace` stack because this tree really does declare one stem twice --
    `mono_coequalizer_π_c_app` exists in both `AlgebraicGeometry.PresheafedSpace` and
    `AlgebraicGeometry.SheafedSpace`, and a sentence that writes the qualifier means the one it
    wrote.

    A `set_option` with no `in` applies to the **rest of the enclosing scope**, so it is carried
    by every declaration below it and reverts at the `end` of the `section` or `namespace` it
    was written in.  That is why the scope stack keeps a dict per level rather than only a name:
    `end` pops the options the level introduced along with the level.

    The two scopes are kept apart in the record -- `OWN` against `INHERITED` -- rather than
    unioned into one set, because they are different strengths of truth.  A sentence about a
    declaration that carries its own raise says more than one about a declaration that merely
    sits below a file-scoped raise, and `report` prints which of the two answered so the reader
    can tell.

    The third return is the **underflow census**: files where an `end` closed a scope this walk
    never opened, keyed by path and counted.  It is the walk's own account of whether it
    understood the file, and it is returned rather than swallowed because the two guards below
    (`if stack` and `if len(levels) > 1`) are otherwise where a missed opener goes quiet -- the
    stack simply stops popping and no figure moves.  Issue 2130 is exactly that: `SECTION` did
    not know `noncomputable section`, 239 of the 582 files underflowed, and nothing said so.
    `report` prints the count, so the next opener a regex misses is a number rather than
    nothing.
    """
    table: dict[str, dict[str, str]] = {}
    by_module: dict[str, dict[str, str]] = {}
    underflows: dict[str, int] = {}
    for path in sorted(sources):
        module = module_name(path)
        by_module.setdefault(module, {})
        stack, pending = [], []
        levels: list[dict[str, None]] = [{}]
        for line in code_only(sources[path]).split("\n"):
            m = SET_OPTION.match(line)
            if m:
                pending.append(m.group(1))
                continue
            m = FILE_SET_OPTION.match(line)
            if m:
                if not FILE_SCOPED_BOILERPLATE.match(m.group(1)):
                    levels[-1][m.group(1)] = None
                continue
            m = NAMESPACE.match(line)
            if m:
                stack.append(("ns", m.group(1)))
                levels.append({})
                continue
            if SECTION.match(line):
                stack.append(("sec", SECTION.match(line).group(1)))
                levels.append({})
                continue
            if END.match(line):
                if stack:
                    stack.pop()
                if len(levels) > 1:
                    levels.pop()
                else:
                    underflows[path] = underflows.get(path, 0) + 1
                continue
            if EXAMPLE.match(line):
                pending = []
                continue
            m = DECL.match(line)
            if m:
                prefix = ".".join(n for kind, n in stack if kind == "ns")
                name = (prefix + "." + m.group(1)) if prefix else m.group(1)
                carried = {o: INHERITED for level in levels for o in level}
                carried.update({o: OWN for o in pending})
                _merge(table.setdefault(name, {}), carried)
                _merge(by_module[module], carried)
                pending = []
    return table, by_module, underflows


def module_name(path: str) -> str:
    return path[:-5].replace(os.sep, ".").replace("/", ".")


def as_module(token: str, modules: set[str]) -> str | None:
    """The module the anchor names, or `None` if it does not name one at all.

    A sentence spells a module three ways here -- `Gluing.lean`, the path
    `FormalSchemes/SpfBasicOpenCover.lean`, and the dotted
    `FormalSchemes.TateInvOverlapDiscontinuous` -- and the last is spelled exactly like a
    declaration, so the tree's own module list is what tells them apart rather than the
    punctuation.
    """
    if token in modules:
        return token
    if token.endswith(".lean"):
        stem = module_name(token).split(".")[-1]
        hits = sorted(m for m in modules if m.split(".")[-1] == stem)
        return hits[0] if len(hits) == 1 else ""
    return None


MODULE_UNRESOLVED = ""


def names_an_option(sentence: str, vocabulary: set[str]) -> bool:
    """Does the sentence backtick an option name the tree actually sets?

    *"`thickeningMap_comp_locallyRingedSpaceMap` needs `backward.isDefEq.respectTransparency
    false` for the same reason `thickeningMap_comp` does"* names no option **noun** at all and is
    in a module docstring, so neither other gate reaches it -- and it is as plain a claim of this
    species as the tree has.  The vocabulary is read off pass 1 rather than hard-coded, so a
    sentence naming an option this tree has stopped using does not quietly keep qualifying.

    The option must be **carried**, not merely mentioned, and that clause is not decoration:
    `FormalSchemes/TateXGluedIso.lean:111` says *"the right-associated term is the same map but
    not the same term, and unifying the two is what `maxRecDepth`/`whnf` timeouts are made of"*.
    Its `same` is about terms, its `maxRecDepth` is a noun about timeouts, and without the verb
    it is a confident `MISMATCH` against a sentence that is entirely true.
    """
    for m in BACKTICK.finditer(sentence):
        if m.group(1).split()[0] in vocabulary and CARRY_VERB.search(sentence[:m.start()]):
            return True
    return False


def is_candidate(sentence: str, justifies_an_option: bool, vocabulary: set[str]) -> bool:
    """Is this sentence a claim about the options another declaration carries?

    Two gates, and it takes `same` plus one of them.  The first is an **option noun** --
    *requirement*, *option*, *accommodation*, *suppression*, *raise*.  The second exists for one
    real spelling that has none: *"the two are `rfl` but not at `instances` transparency, as
    `FormalSchemes/SpfBasicOpenCover.lean` records for the same field"*, which is unmistakably one
    of these and calls the thing a *field*.  It is admitted because the comment it sits in is
    **adjacent to a `set_option ... in`** -- the comment is the justification of an option, so a
    comparison inside it is a comparison of options.

    Dropping the bare family words from the noun list is what that second gate pays for.  Without
    it, `FormalSchemes/TateInvNodeLocus.lean:197` -- *"produces a term that is not type-correct at
    `instances` transparency ... (`FormalSchemes.TateInvOverlapDiscontinuous` records the same
    rule)"* -- is read as an option claim and reported as a `MISMATCH`, and it is not one: the
    anchor module carries no `set_option` and never claimed to.  Both files work around the same
    defeq failure *without* an option, and say so in prose.  A standing false alarm is how an
    instrument gets turned off, so the word `rule` is not an option noun and the sentence is
    outside the population rather than inside it and wrong.
    """
    if not SAME.search(sentence):
        return False
    if SUBJECT_RE.search(sentence) or names_an_option(sentence, vocabulary):
        return True
    return bool(justifies_an_option and ANY_FAMILY.search(sentence))


def family_of(sentence: str) -> str:
    """Which option family the sentence claims, by its English word.  `any` when it names none."""
    for name, pattern in FAMILY_WORDS:
        if pattern.search(sentence):
            return name
    return "any"


def matching(options: dict[str, str], family: str) -> list[str]:
    """The options of `options` that answer `family`; `any` accepts them all."""
    if family == "any":
        return sorted(options)
    return sorted(o for o in options if FAMILIES[family].search(o))


def carries(options: dict[str, str], family: str) -> bool:
    return bool(matching(options, family))


def answered_by(options: dict[str, str], family: str) -> str:
    """Which scope makes the sentence true: its own option, or one it inherits, or neither.

    A declaration carrying both is reported as `OWN`, which is the stronger reading and the one
    the sentence is most likely to have meant.
    """
    scopes = {options[o] for o in matching(options, family)}
    if not scopes:
        return ""
    return OWN if OWN in scopes else INHERITED


def mask_backticks(sentence: str) -> str:
    """`sentence` with backtick spans replaced by same-length runs of `x`.

    Only used for splitting: a Lean name is full of periods (`D.J`, `Foo.lean`) and every one of
    them would otherwise end a sentence.
    """
    return BACKTICK.sub(lambda m: "`" + "x" * len(m.group(1)) + "`", sentence)


def sentences(region: str, first_line: int, line_of: list[int]):
    """Split a joined comment region into sentences, yielding `(text, line)`.

    `line_of[i]` is the source line of character `i`, so a sentence is reported at the line it
    starts on even though the region it came from spans several.
    """
    masked = mask_backticks(region)
    start = 0
    for m in re.finditer(r"[.;]\s+", masked):
        end = m.end()
        if region[start:end].strip():
            yield region[start:end].strip(), line_of[start] if line_of else first_line
        start = end
    if region[start:].strip():
        yield region[start:].strip(), line_of[start] if line_of else first_line


def comment_regions(text: str):
    """Maximal runs of consecutive commented lines, joined, with a per-character line map.

    A cross-reference routinely wraps across three `--` lines, so matching line by line would see
    *"Same transparency requirement as"* and *"`range_specLRSGlueData_f` above"* as two unrelated
    fragments -- which is how a grep-shaped version of this check misses most of the population.
    """
    lines = comment_only(text).split("\n")
    scoped = {n for n, line in enumerate(code_only(text).split("\n"), 1)
              if SET_OPTION.match(line)}
    run, run_start = [], 0
    for n, line in enumerate(lines, 1):
        stripped = line.strip().lstrip("-").lstrip("!").strip()
        if line.strip():
            if not run:
                run_start = n
            run.append((n, stripped))
        elif run:
            yield _join(run, run_start, scoped)
            run = []
    if run:
        yield _join(run, run_start, scoped)


def _join(run, run_start, scoped):
    text, line_of = "", []
    for n, piece in run:
        if text:
            text += " "
            line_of.append(n)
        text += piece
        line_of.extend([n] * len(piece))
    justifies = bool({run_start - 1, run[-1][0] + 1} & scoped)
    return text, run_start, line_of, justifies


def anchors_in(sentence: str) -> list[str]:
    """The backticked tokens the grammar makes anchors: see the module docstring's last section."""
    found, previous_was_anchor = [], False
    for m in BACKTICK.finditer(sentence):
        token = m.group(1)
        before, after = sentence[:m.start()], sentence[m.end():]
        if not IDENTIFIER.match(token):
            previous_was_anchor = False
            continue
        if (CONNECTIVE.search(before) or XREF_VERB.match(after)
                or (previous_was_anchor and CONJUNCTION.search(before))):
            found.append(token)
            previous_was_anchor = True
        else:
            previous_was_anchor = False
    return found


def resolve(token: str, table: dict[str, set[str]]) -> list[str]:
    """Every declaration of the tree the anchor could name, by `.`-component suffix.

    A sentence writes `specGD_f` for `AlgebraicGeometry.specGD_f` and
    `SheafedSpace.mono_coequalizer_π_c_app` for the longer thing, so matching is on the suffix and
    the sentence's own qualifier is what narrows it.
    """
    if token in table:
        return [token]
    parts = token.split(".")
    return sorted(n for n in table if n.split(".")[-len(parts):] == parts)


def references(sources: dict[str, str], table: dict[str, set[str]],
               by_module: dict[str, set[str]]):
    """Pass 2: every cross-reference sentence in the tree's comments, judged or declined."""
    modules = set(by_module)
    vocabulary = {o for options in table.values() for o in options}
    for path in sorted(sources):
        for region, first_line, line_of, justifies in comment_regions(sources[path]):
            for sentence, line in sentences(region, first_line, line_of):
                if not is_candidate(sentence, justifies, vocabulary):
                    continue
                found = anchors_in(sentence)
                if not found:
                    continue
                family = family_of(sentence)
                history = bool(HISTORY.search(sentence))
                for token in found:
                    base = dict(path=path, line=line, text=sentence, anchor=token, family=family)
                    module = as_module(token, modules)
                    if history:
                        yield dict(base, declined="history: a past-tense note, not a live claim")
                    elif module == MODULE_UNRESOLVED and module is not None:
                        yield dict(base, declined="not on this tree: no module answers to `%s`"
                                   % token)
                    elif module is not None:
                        yield dict(base, declined=None, candidates=[module], kind="module",
                                   ok=carries(by_module[module], family))
                    else:
                        candidates = resolve(token, table)
                        if not candidates:
                            yield dict(base, declined="not on this tree: `%s` is not a declaration"
                                       " under FormalSchemes/" % token)
                        elif len({carries(table[c], family) for c in candidates}) > 1:
                            yield dict(base, declined="ambiguous: %d declarations answer to `%s`"
                                       " and they disagree" % (len(candidates), token))
                        else:
                            yield dict(base, declined=None, candidates=candidates,
                                       kind="declaration",
                                       ok=carries(table[candidates[0]], family))


def audit(sources: dict[str, str]):
    """Every cross-reference in `sources`, as `(mismatches, attributed, declined)`."""
    table, by_module, _ = option_table(sources)
    mismatches, attributed, declined = [], [], []
    for ref in references(sources, table, by_module):
        if ref["declined"]:
            declined.append(ref)
            continue
        attributed.append(ref)
        if not ref["ok"]:
            mismatches.append(ref)
    return mismatches, attributed, declined


def read_tree(root: str = ".") -> dict[str, str]:
    out = {}
    for path in sorted(glob.glob(os.path.join(root, "FormalSchemes", "**", "*.lean"),
                                 recursive=True)):
        with open(path, encoding="utf-8") as fh:
            out[os.path.relpath(path, root)] = fh.read()
    return out


def render(options: dict[str, str]) -> str:
    return ", ".join("%s%s" % (o, "" if options[o] == OWN else " (file-scoped)")
                     for o in sorted(options))


def describe(ref: dict, options: dict[str, str]) -> str:
    return ("%s `%s` carries {%s}, which is no `%s` option"
            % (ref["kind"], ref["candidates"][0], render(options) or "nothing", ref["family"]))


def options_of(ref: dict, table, by_module) -> dict[str, str]:
    source = by_module if ref["kind"] == "module" else table
    return source.get(ref["candidates"][0], {})


def report(sources: dict[str, str]) -> int:
    table, by_module, underflows = option_table(sources)
    mismatches, attributed, declined = audit(sources)
    own = {n for n, o in table.items() if OWN in o.values()}
    inherited = {n for n, o in table.items() if o} - own
    counts: dict[str, int] = {}
    for ref in attributed + declined:
        counts[ref["family"]] = counts.get(ref["family"], 0) + 1
    print("modules under FormalSchemes/   : %5d" % len(sources))
    print("declarations with a set_option : %5d   (of %d declarations seen; %d carry their own,"
          " %d only inherit a file-scoped one)"
          % (len(own) + len(inherited), len(table), len(own), len(inherited)))
    print("scope stack underflows         : %5d   (files where an `end` closed a scope this"
          " walk never opened)" % len(underflows))
    for path in sorted(underflows)[:5]:
        print("    %s  (%d)" % (path, underflows[path]))
    if len(underflows) > 5:
        print("    ... and %d more" % (len(underflows) - 5))
    print("cross-references attributed    : %5d" % len(attributed))
    print("  MISMATCH                     : %5d" % len(mismatches))
    print("  declined (see below)         : %5d   (not a failure: see the module docstring)"
          % len(declined))
    print("  by family                    : %s"
          % ", ".join("%s %d" % (k, counts[k]) for k in sorted(counts)))
    for ref in sorted(attributed, key=lambda r: (r["path"], r["line"])):
        scope = answered_by(options_of(ref, table, by_module), ref["family"])
        print("  %s  %s:%d  %s `%s` (%s%s)"
              % ("MISMATCH" if not ref["ok"] else "checked ", ref["path"], ref["line"],
                 ref["kind"], ref["candidates"][0], ref["family"],
                 ", file-scoped" if scope == INHERITED else ""))
    for ref in sorted(mismatches, key=lambda r: (r["path"], r["line"])):
        print("  MISMATCH  %s:%d  %s"
              % (ref["path"], ref["line"], describe(ref, options_of(ref, table, by_module))))
        print("            %s" % ref["text"])
    for ref in sorted(declined, key=lambda r: (r["path"], r["line"])):
        print("  declined  %s:%d  %s" % (ref["path"], ref["line"], ref["declined"]))
        print("            %s" % ref["text"])
    return 1 if mismatches else 0


# --------------------------------------------------------------------------------------------
# `--selftest`.  Canned sources, no `lake`, no tree: every rule the module docstring states is
# reachable from a dict of strings, which is the whole reason `audit` takes one.


def _src(*body: str) -> str:
    return "\n".join(body) + "\n"


CARRIER = _src(
    "namespace AlgebraicGeometry",
    "set_option backward.isDefEq.respectTransparency false in",
    "theorem anchor_with_transparency : True := trivial",
    "",
    "set_option maxHeartbeats 400000 in",
    "theorem anchor_with_budget : True := trivial",
    "",
    "theorem anchor_with_nothing : True := trivial",
    "end AlgebraicGeometry")


def selftest() -> int:
    bad = 0

    def check(name, got, want):
        nonlocal bad
        ok = got == want
        bad += not ok
        print("%s  %s" % ("ok  " if ok else "FAIL", name))
        if not ok:
            print("        want %r\n        got  %r" % (want, got))

    def run(comment: str, extra: dict | None = None):
        sources = {"FormalSchemes/Carrier.lean": CARRIER,
                   "FormalSchemes/Site.lean": _src("-- " + comment)}
        sources.update(extra or {})
        mis, att, dec = audit(sources)
        return ([r["anchor"] for r in mis], [r["anchor"] for r in att],
                [r["declined"].split(":")[0] for r in dec])

    # The rule itself, in both directions.  The first case is the one that must never fire: a
    # scanner that cannot stay quiet on a true sentence would be turned off within a week.
    check("a sentence whose anchor still carries the option is attributed and passes",
          run("Same transparency requirement as `anchor_with_transparency`, for the same reason."),
          ([], ["anchor_with_transparency"], []))
    check("a sentence whose anchor lost the option is a MISMATCH",
          run("Same transparency requirement as `anchor_with_nothing`, for the same reason."),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # The family split, which is the design decision the module docstring argues for.  Both
    # sentences are about a declaration that carries *an* option; only the word differs.
    check("a transparency claim about a heartbeats-only anchor is a MISMATCH, not a pass",
          run("Same transparency requirement as `anchor_with_budget`, for the same reason."),
          (["anchor_with_budget"], ["anchor_with_budget"], []))
    check("the same claim in the anchor's own family passes",
          run("The same heartbeats raise as `anchor_with_budget` needs, for the same reason."),
          ([], ["anchor_with_budget"], []))
    check("a familyless noun falls back to `any` and passes on any option at all",
          run("The same accommodation as `anchor_with_budget`, for the same reason."),
          ([], ["anchor_with_budget"], []))
    check("a familyless noun still fires when the anchor carries nothing",
          run("The same accommodation as `anchor_with_nothing`, for the same reason."),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # A module anchor, which is nine of the tree's cross-references.  Checked against the union
    # of the module's options, and so able to fire -- see the module docstring's argument for
    # preferring that to declining, which is what issue 2106 expected.
    check("a module anchor is checked against the module's own options, and passes",
          run("The same accommodation as `FormalSchemes.Carrier` makes, for the same reason."),
          ([], ["FormalSchemes.Carrier"], []))
    check("a module anchor fires when the module carries no such option at all",
          run("The same accommodation as `FormalSchemes.Site` makes, for the same reason."),
          (["FormalSchemes.Site"], ["FormalSchemes.Site"], []))
    check("a module anchor written as a path resolves to the same module",
          run("The same accommodation `FormalSchemes/Carrier.lean` makes, for the same reason."),
          ([], ["FormalSchemes/Carrier.lean"], []))
    check("a module anchor written as a bare basename resolves too",
          run("The same accommodation `Carrier.lean` makes, for the same reason."),
          ([], ["Carrier.lean"], []))
    check("a transparency claim about a module that only raises heartbeats still fires",
          run("Same transparency requirement as `FormalSchemes.Budget` makes, same reason.",
              {"FormalSchemes/Budget.lean": _src(
                  "set_option maxHeartbeats 400000 in",
                  "theorem only_a_raise : True := trivial")}),
          (["FormalSchemes.Budget"], ["FormalSchemes.Budget"], []))

    # Declined, one case per remaining reason.
    check("a path naming no module of this tree declines rather than being judged",
          run("The same accommodation `Nowhere.lean` makes, for the same reason."),
          ([], [], ["not on this tree"]))
    check("an anchor that is not a declaration of this tree declines",
          run("Same transparency requirement as `Mathlib.Order.Basic.le_refl`, same reason."),
          ([], [], ["not on this tree"]))
    check("a past-tense note is declined, not fired on -- it is the repair, not the defect",
          run("`anchor_with_nothing` above needed the same option until issue 2064 rerouted it"
              " through `anchor_with_transparency`."),
          ([], [], ["history"]))
    check("the same note in the present tense is a live claim and fires",
          run("`anchor_with_nothing` above needs the same transparency option, for the same"
              " reason."),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # Namesakes.  `resolve` matches on `.`-component suffix, so a bare stem can hit two
    # declarations; the module docstring pins which way each case goes.
    twin_split = {"FormalSchemes/Twin.lean": _src(
        "namespace AlgebraicGeometry.Other",
        "set_option backward.isDefEq.respectTransparency false in",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry.Other")}
    check("namesakes that disagree about the family decline rather than guess",
          run("Same transparency requirement as `anchor_with_nothing`, same reason.", twin_split),
          ([], [], ["ambiguous"]))
    check("the sentence's own qualifier narrows the namesakes and it is judged",
          run("Same transparency requirement as `Other.anchor_with_nothing`, same reason.",
              twin_split),
          ([], ["Other.anchor_with_nothing"], []))
    twin_agree = {"FormalSchemes/Twin.lean": _src(
        "namespace AlgebraicGeometry.Other",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry.Other")}
    check("namesakes that agree are judged anyway -- the sentence is false either way",
          run("Same transparency requirement as `anchor_with_nothing`, same reason.", twin_agree),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # Which backtick is the anchor.  The first is the live rule this tree's prose most needs; the
    # second is the reason `does` is not a cross-reference verb.
    check("only the connective's token is the anchor, not every name in the sentence",
          run("Same transparency requirement as `anchor_with_transparency` above, and for the"
              " same reason: the datum is a `def`, so `Foo.J` does not reduce to `D.J`."),
          ([], ["anchor_with_transparency"], []))
    check("a conjoined list takes both anchors once the first is one",
          run("It is the same option, for the same reason, that `anchor_with_transparency` and"
              " `anchor_with_nothing` carry."),
          (["anchor_with_nothing"],
           ["anchor_with_transparency", "anchor_with_nothing"], []))
    check("a sentence about options that names no anchor grammatically is not reported at all",
          run("The same transparency requirement applies here, and `Foo.J` is the reason."),
          ([], [], []))

    # The gates on being a candidate at all.  The `rule` case is the one that matters: it is a
    # real sentence from `FormalSchemes/TateInvNodeLocus.lean:197`, it is entirely true, and an
    # earlier draft of this script reported it as a confident MISMATCH.
    check("a sentence with a comparison but no option noun is not this script's business",
          run("The same argument as `anchor_with_nothing` gives, in the other direction."),
          ([], [], []))
    check("a sentence about options that makes no comparison is not one either",
          run("This needs the transparency option, as `anchor_with_nothing` shows."),
          ([], [], []))
    check("a prose rule cross-referenced in a docstring is not an option claim",
          run("A term not type-correct at `instances` transparency, because the index type needs"
              " unfolding (`FormalSchemes.Carrier` records the same rule)."),
          ([], [], []))
    check("the same sentence inside a `set_option` justification *is* an option claim",
          run("x", {"FormalSchemes/Site.lean": _src(
              "-- A term not type-correct at `instances` transparency",
              "-- (`FormalSchemes.Bare` records the same rule).",
              "set_option backward.isDefEq.respectTransparency false in",
              "theorem here : True := trivial"),
              "FormalSchemes/Bare.lean": _src("theorem nothing_here : True := trivial")}),
          (["FormalSchemes.Bare"], ["FormalSchemes.Bare"], []))

    # Naming the option outright, which is the only gate that reaches a module docstring with no
    # option noun in it.  The second case is `FormalSchemes/TateXGluedIso.lean:111`, where the
    # option is a noun about timeouts and the `same` is about terms -- also once a false MISMATCH.
    check("an option the sentence says the anchor needs is a claim with no option noun at all",
          run("`anchor_with_nothing` needs `backward.isDefEq.respectTransparency false` for the"
              " same reason `anchor_with_transparency` does."),
          (["anchor_with_nothing"],
           ["anchor_with_nothing", "anchor_with_transparency"], []))
    check("an option name merely mentioned as a noun is not a claim that anything carries it",
          run("The term is the same map but not the same term, and unifying the two is what"
              " `maxHeartbeats`/`whnf` timeouts are made of, as `anchor_with_nothing` uses."),
          ([], [], []))
    check("`for the same reason: ...` is an explanation, not a cross-reference",
          run("The same transparency requirement, for the same reason: the datum is a `def` and"
              " `anchor_with_nothing` is where it shows."),
          ([], [], []))

    # Pass 1 must read code and not prose: a fenced `set_option` in a module docstring would
    # otherwise make a stale sentence *pass*, which is the failure that looks plausible.
    quoted = {"FormalSchemes/Carrier.lean": _src(
        "/-- Example:",
        "set_option backward.isDefEq.respectTransparency false in",
        "theorem anchor_with_nothing : True := trivial",
        "-/",
        "namespace AlgebraicGeometry",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry")}
    check("a `set_option` quoted inside a docstring does not count as one the anchor carries",
          run("Same transparency requirement as `anchor_with_nothing`, same reason.", quoted),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # A cross-reference wrapped over three `--` lines, which is the shape most of the tree's are.
    # Matching line by line sees two unrelated fragments and reports nothing.
    wrapped = {"FormalSchemes/Site.lean": _src(
        "-- The glue datum is a `def`, so the rewrite is otherwise rejected as",
        "-- ill-typed. Same transparency requirement as",
        "-- `anchor_with_nothing` above, for the same reason.")}
    check("a cross-reference wrapped across three comment lines is still one sentence",
          run("nothing to see here", wrapped),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # A file-scoped `set_option` with no `in` applies to the rest of the enclosing scope, so it
    # is carried by every declaration below it *and* by the module.  This is where this tree
    # spells 258 of its 406 non-linter options and 258 of its 309 budget raises, so the
    # `heartbeats` family is only reachable at all through this shape -- which is why both
    # halves are asserted here rather than only the declaration one.  The case this replaces
    # asserted the declaration half and carried a comment claiming the module half; the code
    # implemented neither, so the false half was never watched.
    file_scoped = {"FormalSchemes/Carrier.lean": _src(
        "set_option maxHeartbeats 400000",
        "set_option synthInstance.maxHeartbeats 1000000",
        "namespace AlgebraicGeometry",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry")}
    check("a file-scoped `set_option` is carried by the declaration below it",
          run("The same heartbeats raise as `anchor_with_nothing` needs, same reason.",
              file_scoped),
          ([], ["anchor_with_nothing"], []))
    check("a file-scoped `set_option` is carried by the module too",
          run("The same budget raise `FormalSchemes.Carrier` makes, for the same reason.",
              file_scoped),
          ([], ["FormalSchemes.Carrier"], []))
    check("a familyless noun passes on a file-scoped option, as it does on a scoped one",
          run("The same accommodation as `FormalSchemes.Carrier` makes, same reason.",
              file_scoped),
          ([], ["FormalSchemes.Carrier"], []))
    check("a transparency claim about a file-scoped budget raise still fires",
          run("Same transparency requirement as `anchor_with_nothing`, same reason.",
              file_scoped),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # The scope really is a scope: `end` reverts it.  Without this the fix would be "attribute
    # to the rest of the file", which is a different and wrong rule.
    sectioned = {"FormalSchemes/Carrier.lean": _src(
        "namespace AlgebraicGeometry",
        "section",
        "set_option maxHeartbeats 400000",
        "theorem anchor_with_transparency : True := trivial",
        "end",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry")}
    check("a file-scoped option inside a `section` reaches a declaration in it",
          run("The same heartbeats raise as `anchor_with_transparency` needs, same reason.",
              sectioned),
          ([], ["anchor_with_transparency"], []))
    check("and does not reach one after the matching `end`",
          run("The same heartbeats raise as `anchor_with_nothing` needs, same reason.",
              sectioned),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # `noncomputable section` is how this tree opens a section -- 546 of its 975 section-opening
    # lines -- and `SECTION` did not match it until issue 2130.  The two shapes below are the
    # two the old regex got *backwards*, in opposite directions, so each needs its own case.
    # Both were measured against Lean itself rather than reasoned about, with a `#opt` command
    # that prints `getOptions` at each point: in (a) the raise reads `some 400000` after the
    # section's `end` and `none` only after `end AlgebraicGeometry`; in (b) it reads `none`
    # immediately after the `end`.
    nc_namespace = {"FormalSchemes/Carrier.lean": _src(
        "namespace AlgebraicGeometry",
        "set_option maxHeartbeats 400000",
        "noncomputable section",
        "theorem inside_the_section : True := trivial",
        "end",
        "theorem after_the_section : True := trivial",
        "end AlgebraicGeometry")}
    check("a `noncomputable section` opens a scope, so its `end` does not revert the"
          " namespace's raise",
          run("The same heartbeats raise as `after_the_section` needs, same reason.",
              nc_namespace),
          ([], ["after_the_section"], []))
    check("and the declaration inside the section inherits it too",
          run("The same heartbeats raise as `inside_the_section` needs, same reason.",
              nc_namespace),
          ([], ["inside_the_section"], []))

    nc_reverts = {"FormalSchemes/Carrier.lean": _src(
        "noncomputable section",
        "set_option maxHeartbeats 400000",
        "end",
        "namespace AlgebraicGeometry",
        "theorem after_the_section : True := trivial",
        "end AlgebraicGeometry")}
    check("a raise written inside a `noncomputable section` reverts at its `end`",
          run("The same heartbeats raise as `after_the_section` needs, same reason.",
              nc_reverts),
          (["after_the_section"], ["after_the_section"], []))

    # The stack's *other* consumer, which predates the option scope by the whole life of the
    # scanner: qualifying a name by its enclosing `namespace`.  A missed `section` push makes
    # the matching `end` pop the namespace early, so the declaration after it is qualified with
    # the wrong prefix -- and on a tree that declares one stem in two namespaces that is how a
    # sentence gets checked against the wrong declaration.  Asserted against the table, since
    # `run` reports anchors rather than names.
    # The trailing declaration is not decoration: without it nothing watches `end` popping the
    # *namespace* stack at all -- a loosening that stops popping it leaves both qualified names
    # unchanged and fails no case.  That guard has been unwatched since the scanner was built,
    # and it is the same 0-FAIL shape issue 2126's author hit on their own precedence rule.
    qualified, _, _ = option_table({"FormalSchemes/Carrier.lean": _src(
        "namespace AlgebraicGeometry",
        "noncomputable section",
        "theorem inside_the_section : True := trivial",
        "end",
        "theorem after_the_section : True := trivial",
        "end AlgebraicGeometry",
        "theorem outside_every_namespace : True := trivial")})
    check("a name after a `noncomputable section` closes keeps its namespace qualifier, and one"
          " after the namespace closes loses it",
          sorted(qualified),
          ["AlgebraicGeometry.after_the_section", "AlgebraicGeometry.inside_the_section",
           "outside_every_namespace"])

    # The underflow census: the walk's own account of whether it understood the file.  Both
    # halves are asserted, because a diagnostic that can only ever report zero is the same dead
    # rule this row is about -- it is what the two `if` guards in `option_table` were doing
    # before, and 239 of the 582 files were underflowing while `--tree` printed nothing.
    _, _, balanced = option_table({"FormalSchemes/Carrier.lean": _src(
        "namespace AlgebraicGeometry",
        "noncomputable section",
        "theorem anchor_with_nothing : True := trivial",
        "end",
        "end AlgebraicGeometry")})
    check("a file whose scopes balance reports no underflow", balanced, {})
    _, _, stray = option_table({"FormalSchemes/Carrier.lean": _src(
        "namespace AlgebraicGeometry",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry",
        "end")})
    check("an `end` that closes a scope the walk never opened is counted and named",
          stray, {"FormalSchemes/Carrier.lean": 1})

    # File-scoped `linter.*` is the one form that is boilerplate, and excluding it is what keeps
    # the fallback family `any` from becoming vacuously true: every module of this tree carries
    # `linter.style.header false`, so admitting it turns both of the tree's standing
    # `MISMATCH`es into passes.  Measured, not asserted -- see the loosening in the pull request.
    boilerplate = {"FormalSchemes/Carrier.lean": _src(
        "set_option linter.style.header false",
        "namespace AlgebraicGeometry",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry")}
    check("a file-scoped `linter.*` option is boilerplate and is not attributed",
          run("The same accommodation as `anchor_with_nothing` makes, same reason.", boilerplate),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # `set_option ... in` before an `example` is consumed by the `example`.  Population 0 on this
    # tree, so this pins a hole rather than closing a live one.
    exemplar = {"FormalSchemes/Carrier.lean": _src(
        "namespace AlgebraicGeometry",
        "set_option backward.isDefEq.respectTransparency false in",
        "example : True := trivial",
        "theorem anchor_with_nothing : True := trivial",
        "end AlgebraicGeometry")}
    check("a scoped option consumed by an `example` does not fall through to the next theorem",
          run("Same transparency requirement as `anchor_with_nothing`, same reason.", exemplar),
          (["anchor_with_nothing"], ["anchor_with_nothing"], []))

    # The two scopes are kept apart in the record, which is what lets `report` say which
    # answered.  Asserted against the table directly: `run` only reports anchors.
    own_and_inherited = _src(
        "set_option maxHeartbeats 400000",
        "namespace AlgebraicGeometry",
        "set_option maxHeartbeats 800000 in",
        "theorem its_own : True := trivial",
        "theorem inherits : True := trivial",
        "end AlgebraicGeometry")
    table, _, _ = option_table({"FormalSchemes/Carrier.lean": own_and_inherited})
    check("a declaration's own option outranks the file-scoped one of the same name",
          table["AlgebraicGeometry.its_own"], {"maxHeartbeats": OWN})
    check("a declaration that only sits below the raise is recorded as inheriting it",
          table["AlgebraicGeometry.inherits"], {"maxHeartbeats": INHERITED})
    check("`answered_by` names the scope the verdict rests on",
          (answered_by(table["AlgebraicGeometry.its_own"], "heartbeats"),
           answered_by(table["AlgebraicGeometry.inherits"], "heartbeats"),
           answered_by(table["AlgebraicGeometry.inherits"], "transparency")),
          (OWN, INHERITED, ""))

    # Namesakes are the only place the two scopes are merged rather than built together, and a
    # plain `update` there silently downgrades the stronger record to the weaker one depending
    # on which file sorts first.  Without this case that precedence rule fails no loosening at
    # all, which is the defect it exists to prevent one level up.
    twins, _, _ = option_table({
        "FormalSchemes/TwinA.lean": _src(
            "namespace AlgebraicGeometry",
            "set_option maxHeartbeats 400000 in",
            "theorem twin : True := trivial",
            "end AlgebraicGeometry"),
        "FormalSchemes/TwinB.lean": _src(
            "set_option maxHeartbeats 800000",
            "namespace AlgebraicGeometry",
            "theorem twin : True := trivial",
            "end AlgebraicGeometry")})
    check("merging namesakes keeps the stronger record: own is not downgraded by a later file",
          twins["AlgebraicGeometry.twin"], {"maxHeartbeats": OWN})

    # `report` is the only thing that prints `by family` and the only thing that prints which
    # scope answered, so neither was reachable from a case at all until here -- and the tree's
    # own `by family` is `any 17, transparency 10`, with no `heartbeats` member to watch.  This
    # runs the whole report over the file-scoped shape, which is the one that makes that family
    # reachable, and reads the two lines back.
    reported = io.StringIO()
    with contextlib.redirect_stdout(reported):
        report({"FormalSchemes/Budget.lean": _src(
                    "set_option maxHeartbeats 400000",
                    "namespace AlgebraicGeometry",
                    "set_option synthInstance.maxHeartbeats 1000000 in",
                    "theorem carries_its_own : True := trivial",
                    "theorem only_inherits : True := trivial",
                    "end AlgebraicGeometry"),
                "FormalSchemes/Site.lean": _src(
                    "-- The same heartbeats raise as `carries_its_own` needs, same reason.",
                    "",
                    "-- The same heartbeats raise as `only_inherits` needs, same reason.")})
    lines = reported.getvalue().split("\n")
    check("`by family` reaches the `heartbeats` family through the file-scoped shape",
          [l.split(":")[1].strip() for l in lines if "by family" in l], ["heartbeats 2"])
    check("the report says which scope answered, and only when it is the weaker one",
          [l.split("(")[-1].rstrip(")") for l in lines if l.startswith("  checked")],
          ["heartbeats", "heartbeats, file-scoped"])

    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--tree", action="store_true",
                   help="check every option cross-reference in the tree's comments")
    g.add_argument("--selftest", action="store_true",
                   help="check the attribution, family and declining rules on canned sources")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    return report(read_tree())


if __name__ == "__main__":
    sys.exit(main())
