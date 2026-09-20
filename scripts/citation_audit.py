#!/usr/bin/env python3
"""Check that every backticked declaration name in this tree's comments resolves.

`lake build` cannot catch a docstring that cites a declaration which does not exist, so this
script is the only thing that does.  See `CONTRIBUTING.md` for the convention it implements; in
short, a backticked identifier-shaped token is a *citation* and must resolve as a declaration, a
project module, or a repository path.  Five of the non-citation categories are decided here, in
`is_excluded`: notation, one- and two-character prose variables, name fragments, Lean vocabulary,
and the enumerated construction shorthands.  The remaining three -- longer prose variables,
dot-notation on a local, and a field of a structure named in the same sentence -- are not
mechanically separable from a declaration name, so this script reports them and the author names
them in the pull request body.

Usage, from the repository root, after a full `lake build`:

    python3 scripts/citation_audit.py --diff upstream/master...HEAD
    python3 scripts/citation_audit.py --tree

A backticked `<project file>.lean:NN` pointer is not a citation either, and it is the only
non-citation shape this script treats as a *defect* rather than as a category: it is not
identifier-shaped, so the resolution machinery never sees it, while the line it names moves the
first time anyone inserts a declaration above it.  `project_line_pointer` reports them.  Mathlib
pointers are left alone -- they are pinned by the toolchain, not by this repository's edits.
(There is deliberately no count here.  The two lists above hold five categories and three, and an
ordinal that has to be kept in step with both of them is one more thing that can go quietly wrong
-- which is the defect this paragraph is about.)

The pointer check, and only the pointer check, also runs over this repository's Markdown:
`markdown_line_pointers`.  See `CONTRIBUTING.md` for why that is the one part of the audit that
crosses over, and for the use/mention rule it reads off the document.

`--selftest` checks the tokenizer against the cases it used to get wrong, both of the
malformed-span checks below, the line-pointer predicate and the Markdown scan, and needs no build.

Resolution of the declaration case is done by elaborating one `#check @Token` per distinct token
in a single throwaway Lean file, which costs one `import FormalSchemes` and a few seconds.  That
probe is the one part of this script that needs a built tree, and a probe that does not elaborate
used to answer "nothing is unresolved" rather than failing -- an `import` that fails puts the only
error on line 1, where no token lives, so every token came back resolved.  It now exits **2** and
says so; see `probe_unresolved` for the two fatal shapes and `CONTRIBUTING.md` for how to
recognise the old failure in a report someone else ran.  Exit 1 still means the audit measured the
tree and found something.

A *built* tree is not the same thing as a build **of this tree**, and that is the second way the
probe can be wrong (issue 2109).  `lake env lean` sets `LEAN_PATH` and hands the probe whatever
oleans are on disk; on a checkout whose `.lake` was built from another branch it answers fluently
about those sources while the population counts beside it are read off these ones.  The probe is
therefore gated on `lake build --no-build FormalSchemes`, which compares Lake's own traces, builds
nothing, costs about two seconds and names the modules that are out of date.  That refusal exits
**2** as well: for a caller it is the same question -- can this report be believed -- and it has
the same remedy.  See `tree_is_current`, which also records why the mtime comparison proposed for
this job is wrong.
"""

from __future__ import annotations

import argparse
import glob
import os
import re
import subprocess
import sys
import tempfile

OPEN_SET = (
    "open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace CategoryTheory\n"
    "  CategoryTheory.Limits FormalSpectrum TopologicalSpace\n"
)

# A citation span may be broken by the 100-column wrap, so this crosses newlines.  That has two
# consequences, and both are handled below rather than left to bite.  A span that wraps is joined
# by `tokens_of`, so a wrapped *name* still resolves and a wrapped *expression* is still notation.
# And a fragment with an odd number of backticks no longer merely loses one span: every backtick
# after the stray one re-pairs, so the rest of the fragment is read as the wrong text.  A
# line-bounded regex confined that damage to one line and hid it; `unbalanced_fragments` reports it
# instead.
BACKTICKED = re.compile(r"`([^`]+)`")

# A fenced block is code, not prose, so its contents are not citations -- and with a newline-
# crossing `BACKTICKED` the three backticks of a fence would otherwise pair with whatever comes
# next and swallow the block.
FENCE = re.compile(r"^\s*```")

# The layout of a wrapped span: the newline, the next line's indentation, and its `--` marker when
# the span wraps inside a line comment.  None of it is part of the name.
_CONTINUATION = re.compile(r"^\s*(?:--\s*)?")

# A span nested inside another is *balanced*, so a parity check cannot see it, but the crossing
# `BACKTICKED` closes the outer span at the inner one's opener and the rest of the comment reads as
# the wrong text.  The shape that produces it is a run of two or more backticks once fences are
# stripped: Lean comments have no double-backtick convention, so such a run is the defect or a typo.
ADJACENT = re.compile(r"``+")

# A `File.lean:NN` pointer at a *project* file.  `is_excluded` files it under notation, because a
# colon is not an identifier character, so nothing ever checks it -- and unlike every other
# non-citation category it makes a claim that can go wrong silently: issue 1479 removed the three
# `set_option` blocks of `Gluing.lean` and `Gluing.lean:48`, cited from two other files as the
# precedent for one, went on pointing at a blank line.  A declaration name is checked on every pull
# request; a line number is checked by nobody.
#
# Mathlib pointers are deliberately *not* matched.  They are pinned by the toolchain rather than by
# this repository's edits, and the comparison below is exactly what separates them: the project's
# `Gluing.lean` is a path this repository globs, `Mathlib/AlgebraicGeometry/Gluing.lean` is not.
LINE_POINTER = re.compile(r"^(\S+\.lean):\d+(?:-\d+)?$")

# The same shape in Markdown, where the Lean tokenizer above does not apply and must not be run:
# a ``...`` run is ordinary markup in a document and a *defect* in a Lean comment (`nested_spans`),
# and a document that deliberately cites deleted names and misspellings would drown the resolution
# machinery.  Only the pointer predicate crosses over, because it is a shape test on a token and
# the shape means the same thing in both languages.
#
# `MENTION` is what stops this reporting the document that defines the rule.  `CONTRIBUTING.md`
# already separates *using* a token from *naming* one, in its own markup and without having been
# asked to: a pointer that cites a location is written with single backticks, while the one place
# the document displays the defective token itself is written with double backticks -- which is
# how Markdown shows a backtick.  Measured on `c80eb53` (issue 1530): six single, one double, no
# exceptions either way.  The rule is read off the document, not imposed on it.
#
# A pointer never wraps -- the shape has no space in it -- so scanning line by line is exact here,
# and the newline-crossing `BACKTICKED` is deliberately not reused.
MENTION = re.compile(r"``.+?``")
MD_SPAN = re.compile(r"`([^`]+)`")


def project_line_pointer(token: str, paths: set[str]) -> bool:
    """True if `token` is a `<project file>.lean:NN` pointer -- a citation nothing can check."""
    m = LINE_POINTER.match(token)
    return bool(m) and m.group(1) in paths


def line_pointers_in_markdown(text: str, paths: set[str]):
    """Yield `(line, token)` for each single-backticked project line pointer in `text`."""
    for n, line in enumerate(strip_fences(text).split("\n"), 1):
        for m in MD_SPAN.finditer(MENTION.sub(" ", line)):
            if project_line_pointer(m.group(1), paths):
                yield n, m.group(1)


def tracked_markdown() -> list[str]:
    """The Markdown this repository versions.  `git ls-files` rather than a glob: the sandbox keeps
    an unversioned Lean toolchain under `.elan-home/`, with README files of its own."""
    out = subprocess.run(["git", "ls-files", "*.md"], capture_output=True, text=True, check=True)
    return out.stdout.split()


def markdown_line_pointers(paths: set[str]) -> list[tuple[str, int, str]]:
    """Report every project line pointer in the tracked Markdown, as `(path, line, token)`.

    Whole documents in both modes, not the diff.  A citation is falsified by the pull request that
    changes it, so the diff is the right population for one; a line pointer is falsified by an edit
    to the file it *names*, which is nowhere near the document carrying it, so a diff-restricted
    scan would be blind to the only way one ever goes wrong.
    """
    return [(path, n, tok) for path in sorted(tracked_markdown())
            for n, tok in line_pointers_in_markdown(open(path, encoding="utf-8").read(), paths)]

# Lean identifier syntax.  Subscripts (U+2080-U+209C) are identifier characters; superscripts are
# not, which is why `Iⁿ` is notation and `U₂` is a name.  Getting this wrong makes the generated
# file fail to parse rather than fail to resolve, so the two are kept apart deliberately.
_ATOM = r"[A-Za-z_Α-ω][A-Za-z0-9_'!?Α-ω₀-₉ₐ-ₜ]*"
IDENTIFIER = re.compile(r"^%s(\.%s)*$" % (_ATOM, _ATOM))

# Tokens that are Lean syntax rather than names: `#check @private` is a parse error, not an
# unresolved citation, and a parse error derails every command after it.
SYNTAX_TOKENS = set(
    """by fun let have show from do if then else match with at in theorem lemma def abbrev
    instance example variable variables universe open namespace end section import set_option
    attribute deriving where this sorry admit calc local omit private protected partial unsafe
    noncomputable mutual macro notation infix infixl infixr prefix postfix syntax elab structure
    class inductive extends return try catch finally for while unless assert use exists forall
    obtain rintro rcases refine intro apply exact simp rw rfl decide haveI letI inferInstanceAs
    and or not is the a it as on no all be so one two that than only of to""".split()
)

# The **construction shorthand** allow-list: the standard mathematical name of a construction,
# used as prose for the whole family of declarations that realise it rather than for any one of
# them.  `CONTRIBUTING.md` states the admission rule and the measurement behind each entry, and
# the list is closed -- a token joins it only by that measurement.
#
# This check runs *before* the declaration case, deliberately.  Bare `Spec` does resolve, to
# `AlgebraicGeometry.Spec : CommRingCat -> Scheme`, which is what 2 of a 43-occurrence sample
# mean by it; letting it through the declaration case is how a wrong referent got blessed.
CONSTRUCTION_SHORTHAND = {
    "Spf": "FormalScheme.Spf, FormalSpectrum.locallyRingedSpaceObj, "
           "FormalSpectrum.locallyRingedSpaceMap, AdicRingCat.spfFunctor",
    "Spec": "Spec, Spec.locallyRingedSpaceObj, Spec.locallyRingedSpaceMap, PrimeSpectrum",
}

# Tactics, attributes, elaborator entry points and configuration fields.  Some of these do resolve
# to a real constant (`subst` to `HEq.subst`, `whnf` to `Lean.Meta.whnf`), which is precisely why
# they have to be listed: resolving is not evidence that the citation meant that constant.
VOCABULARY = set(
    """reassoc subst whnf isDefEq instances dsimp erw omega aesop norm_num unfold delta conv
    gcongr positivity ring linarith nlinarith push_cast field_simp abel module bound fun_prop
    congr convert ext filter_upwards induction cases constructor specialize symm trans
    change convert! rcases' peel measurability continuity""".split()
)


def comment_regions(src: str):
    """Yield `(line_number, text)` for each `/-- -/`, `/-! -/` and `--` comment.

    Block comments nest in Lean, so the depth has to be tracked: a `-/` inside a nested comment
    does not close the outer one.  String literals are skipped so that a `--` inside one is not
    mistaken for a comment.
    """
    out, i, n, line, depth, start, startline = [], 0, len(src), 1, 0, None, None
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
        elif depth:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
                if depth == 0:
                    out.append((startline, src[start:i]))
            else:
                i += 1
        elif src.startswith("/-", i):
            depth, start, startline, i = 1, i, line, i + 2
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append((line, src[i:j]))
            i = j
        elif c == '"':
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\":
                    i += 1
                if i < n and src[i] == "\n":
                    line += 1
                i += 1
            i += 1
        else:
            i += 1
    return out


def strip_fences(text: str) -> str:
    """Blank the contents of ``` fenced blocks, keeping the line count so attribution survives.

    A fragment with an odd number of fence lines is left alone: that happens when a `--diff` hunk
    adds one side of a fence, and there is then no way to tell which lines are inside it.  Blanking
    from the lone fence to the end of the hunk would silently drop real citations, which is the
    failure this script is for.
    """
    if sum(bool(FENCE.match(l)) for l in text.split("\n")) % 2:
        return text
    out, inside = [], False
    for line in text.split("\n"):
        if FENCE.match(line):
            inside = not inside
            out.append("")
            continue
        out.append("" if inside else line)
    return "\n".join(out)


def join_wrapped(raw: str) -> str:
    """Collapse a span broken by the line wrap back into one line."""
    head, *rest = raw.split("\n")
    parts = [head.rstrip()] + [_CONTINUATION.sub("", p).rstrip() for p in rest]
    return " ".join(p for p in parts if p)


def tokens_of(text: str, base_line: int):
    text = strip_fences(text)
    for m in BACKTICKED.finditer(text):
        raw = m.group(1)
        yield (join_wrapped(raw) if "\n" in raw else raw,
               base_line + text[: m.start()].count("\n"))


def is_excluded(token: str) -> str | None:
    """Return the exclusion category, or `None` if the token has to resolve."""
    if not IDENTIFIER.match(token):
        return "notation"
    if token in CONSTRUCTION_SHORTHAND:
        return "construction shorthand"
    if token in SYNTAX_TOKENS or token in VOCABULARY:
        return "Lean vocabulary"
    if len(token) <= 2:
        return "prose variable"
    if token.startswith("_"):
        return "name fragment"
    return None


def project_modules() -> set[str]:
    return {"FormalSchemes"} | {
        "FormalSchemes." + os.path.basename(f)[:-5] for f in glob.glob("FormalSchemes/*.lean")
    }


# The root module list.  It is a project file and the tree has occasion to cite it by name --
# `CONTRIBUTING.md`'s account of what adding a module costs is about this file -- but it sits at
# the repository root rather than under `FormalSchemes/`, so neither spelling in `project_paths`
# reaches it, and it is not excludable by shape either: `IDENTIFIER` matches it, so without this
# entry it is sent to `#check @FormalSchemes.lean` and reported UNRESOLVED.  It belongs here and
# not in `project_modules` because it is a *path*.  The module of the same file is `FormalSchemes`,
# which that set already carries; adding `FormalSchemes.lean` there would assert a module nothing
# imports, and the two sets print under one heading but do not mean the same thing.
ROOT_MODULE_LIST = "FormalSchemes.lean"

# The library the probe imports, and therefore the one the staleness gate asks `lake` about.  It is
# a constant rather than two string literals so that the gate and the `import` it guards cannot
# drift apart: a gate that certifies a different target from the one the probe reads would be worse
# than no gate, because it would certify it confidently.
LIBRARY = "FormalSchemes"


def project_paths() -> set[str]:
    """Both spellings the tree uses: the path, and the bare file name after a locative.

    For every file but one those are two different strings; for the root module list they are the
    same string, which is why it reads as a single `add` rather than as a pair.
    """
    paths = set(glob.glob("FormalSchemes/*.lean"))
    paths |= {os.path.basename(f) for f in paths}
    paths.add(ROOT_MODULE_LIST)
    return paths


class ProbeDidNotElaborate(RuntimeError):
    """The `#check` probe failed before it reached a `#check`, so its silence means nothing.

    Raised rather than returned, and never converted into "everything is unresolved": a false
    alarm on every mid-build tree would be as useless as the false clean this replaces, and an
    author who has been told the probe did not run knows exactly what to do about it.
    """


class ProbeTreeIsStale(RuntimeError):
    """`.lake` is not established to be a build of this checkout, so the probe must not answer.

    Raised on both branches of `probe_stale`: the one where `lake` listed out-of-date targets, so
    that `.lake` holding a build of *other* sources is a fact, and the one where `lake` failed for
    a reason of its own, so that it is merely unestablished and the tree may be perfectly current.
    The class does not tell them apart because a caller cannot act on the difference -- the
    question is "can I believe this report" either way -- while the *message* names which happened
    in its lead sentence, which it did not before issue 2113.  The name is kept for the commoner
    case rather than widened to cover both, since it is what four sites already state.

    A sibling of `ProbeDidNotElaborate`, raised for the same reason and carrying the same exit
    code: this run measured nothing.  They are worth telling apart in the *message* and not in the
    exit status, because a caller branches on "can I believe this report", which is one question,
    while an author branches on the sentence, which names which of the two happened.  The remedy is
    also the same one -- run a full `lake build` -- so a third numeral would buy a distinction
    nobody acts on, against four sites that state this convention (this class, the module
    docstring, and `CONTRIBUTING.md` in two places) and would all have to be kept in step with it.

    This failure is strictly nastier than the one issue 2099 closed.  A probe that did not
    elaborate leaves a *recognisable* artefact: population right, `UNRESOLVED` exactly `0`.  A
    probe run against a stale `.lake` leaves a plausible non-zero number that no signature
    distinguishes from a true one -- the report is about the built tree while the population counts
    beside it are read off the checkout's sources.
    """


# The block `lake` ends an unsuccessful run with.  The `✖ [n/m] Building X` lines above it carry
# the same names, but only this block is a list and only it is what `lake` calls the answer.  Its
# absence is not fatal on its own: the message falls back to quoting `lake`'s own lines, so a
# change to this format costs the report its module names and not its verdict.
_LAKE_FAILURES = re.compile(r"^Some required targets logged failures:\n((?:[ \t]*-[ \t]+\S+\n?)+)",
                            re.M)
_LAKE_TARGET = re.compile(r"^[ \t]*-[ \t]+(\S+)[ \t]*$", re.M)


def probe_stale(transcript: str, returncode: int, target: str) -> list[str]:
    """Read one `lake build --no-build` result, or refuse to let the probe run at all.

    Returns the empty list when the build is current.  Split out of `tree_is_current` so that
    `--selftest` can reach it without a `lake`, exactly as `probe_unresolved` is split out of
    `resolve_declarations`, and for the same reason: a guard nobody has watched fire is not a guard
    (issue 2072).

    The predicate is one rule -- **`lake` exits 0, or this run measured nothing** -- and it is
    deliberately the whole of it.  `--no-build` compares Lake's own traces and content hashes, so
    a zero exit is the strongest statement available that the oleans the probe will import were
    built from the sources this script just read.  Anything else, including a `lake` that failed
    for a reason of its own, leaves that unestablished, and an instrument that cannot establish it
    must not answer.  There is no false-alarm surface above a zero exit, which is what lets the
    rule be this blunt.

    The other rules are about the *message* and not the verdict, and the message must claim only
    what its branch establishes.  When `lake` listed out-of-date targets, staleness is a fact and
    the refusal says so and names them -- naming the module is this instrument's whole advantage
    over the one refuted below.  When `lake` failed for a reason of its own, or failed silently,
    all that is established is that `lake` did not answer, so the refusal says *that* and quotes
    `lake`'s own first lines; the tree may be perfectly current.  The two leads are deliberately
    disjoint strings and `--selftest` asserts each branch does not carry the other's, because a
    single shared lead is what this said before issue 2113 and nothing could see it.
    """
    if returncode == 0:
        return []
    m = _LAKE_FAILURES.search(transcript)
    named = _LAKE_TARGET.findall(m.group(1)) if m else []
    if named:
        lead = ("`.lake` is not a build of this checkout, so the probe would resolve against\n"
                "    sources nobody asked it about.\n")
        detail = "    out of date:\n" + "".join("      %s\n" % t for t in named[:5]) + (
            "      ... and %d more\n" % (len(named) - 5) if len(named) > 5 else "")
    else:
        lead = ("`lake` did not answer, so whether `.lake` is a build of this checkout is\n"
                "    unknown -- and an audit that cannot establish it will not answer either.\n")
        lines = [l.strip() for l in transcript.splitlines() if l.strip()]
        detail = ("".join("    %s\n" % l for l in lines[:5]) if lines else
                  "    `lake build --no-build %s` exited %d and printed nothing.\n"
                  % (target, returncode))
    raise ProbeTreeIsStale(
        lead
        + detail
        + "    `lake env lean` sets `LEAN_PATH` and hands the probe whatever oleans are on\n"
          "    disk; it does not check them against the working tree.  Run a full\n"
          "    `lake build` and re-run this audit.")


def tree_is_current(target: str = LIBRARY) -> None:
    """Refuse to run the probe against a `.lake` built from sources other than the checkout's.

    Costs one `lake build --no-build <target>`, which **builds nothing**: it exits immediately
    when a target is out of date rather than starting the rebuild, so the stale case is as cheap
    as the healthy one -- measured on this tree at 2.0s and 1.9s respectively, against a probe
    that already costs several.  That is the property which makes the gate affordable: a check
    that started a two-hour rebuild to find out would not be run.

    *An mtime comparison is not a weaker version of this check; it is a different and false one,
    and it was implemented and refuted before this was written (issue 2109).*  The proposal was to
    stamp the report with the root `.olean`'s mtime against the newest tracked `.lean`, on the
    argument that a comparison cannot false-alarm.  It false-alarms on a healthy tree: `git
    checkout` rewrites the mtime of every file it touches and `lake exe cache get` unpacks oleans
    with times of its own, so a fully built, genuinely up-to-date tree routinely carries a root
    olean *older* than its newest source -- by 8567s when the row was filed, and reproducibly by
    any `touch` of a source whose content does not change.  Lake does not care, because Lake
    compares traces and content hashes (`.lake/build/lib/lean/*.trace`; `lake --help`: `--rehash`
    "hash all files for traces (do not trust .hash files)").  Asking Lake is therefore both exact
    and the only thing that cannot disagree with what the probe will actually import.
    """
    proc = subprocess.run(["lake", "build", "--no-build", target],
                          capture_output=True, text=True)
    probe_stale(proc.stdout + proc.stderr, proc.returncode, target)


def probe_unresolved(transcript: str, path: str, header: int, tokens: list[str],
                     returncode: int) -> set[str]:
    """Read one probe transcript into the unresolved set, or refuse to read it at all.

    Split out of `resolve_declarations` so that `--selftest` can reach it without a build.  That
    split is the whole point of the guard: the failure being guarded against is a *missing*
    `unknownIdentifier` line, and nothing that cannot be handed a transcript can tell an empty
    answer apart from a clean one.

    Two things are fatal, and neither subsumes the other (issue 2099).

    * An `error` at or above `header`.  That is the `import`-and-`open` region, where nothing this
      audit is about lives.  An `import` that fails puts the *only* error there and no `#check` is
      ever elaborated; this script answered `0 UNRESOLVED` through that failure three times in
      thirty hours, once into a shipped pull-request body.  An `open` that has stopped naming a
      namespace errors there too while the `#check`s below carry on resolving against the wrong
      set, which the exit-code rule cannot see.
    * A non-zero exit with **no error attributed to a `#check` line at all**.  That is `lake`
      failing before `lean` ran, or `lean` dying without a diagnosis this reader can place.

    Deliberately *not* "non-zero exit with an empty unresolved set": a tree whose only complaint is
    one ambiguous name exits non-zero, resolves everything, and has measured the whole population.
    Failing that run would trade this row's false clean for a false alarm.
    """
    unresolved, stray, region, attributed = set(), [], False, 0
    for line in transcript.splitlines():
        m = re.match(re.escape(path) + r":(\d+):\d+: error(.*)", line)
        if not m:
            if line.lstrip().startswith("error"):
                # Attributed to no line of the probe: `lake`'s own complaint, before `lean`.
                stray.append(line.strip())
            continue
        idx = int(m.group(1)) - header - 1
        if idx < 0:
            region = True
            stray.append(line.strip())
            continue
        if idx < len(tokens):
            # Counted before the class is looked at: it is evidence that the probe reached this
            # `#check`, which is all the exit-code rule needs.
            attributed += 1
        if "unknownIdentifier" not in m.group(2):
            # An ambiguous or overloaded name resolves — to more than one constant.  That is a
            # different complaint, and not this script's.
            continue
        if idx < len(tokens):
            unresolved.add(tokens[idx])
    if region or (returncode != 0 and tokens and not attributed):
        raise ProbeDidNotElaborate(
            "the resolution probe did not elaborate, so this run measured nothing.\n"
            + ("".join("    %s\n" % f for f in stray[:5]) if stray else
               "    `lake env lean` exited %d and printed nothing this reader could place.\n"
               % returncode)
            + "    Run a full `lake build` first: a probe whose `import FormalSchemes` fails\n"
              "    reports every token as resolving.")
    return unresolved


def resolve_declarations(tokens: list[str]) -> set[str]:
    """Return the subset of `tokens` that `#check @token` fails to resolve.

    Raises `ProbeDidNotElaborate` if the probe cannot be believed; see `probe_unresolved`.  Raises
    `ProbeTreeIsStale` if the tree it would be believed *about* is not this checkout.

    The staleness gate sits here, below the empty-token early return, so that it guards the probe
    and not the script: `--diff` on a range with no `*.lean` in it never imports anything, and
    charging such a run two seconds and a possible refusal would be a cost with nothing on the
    other side of it.  `--tree` always has tokens, so it is always gated.
    """
    if not tokens:
        return set()
    tree_is_current()
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as h:
        h.write("import %s\n" % LIBRARY + OPEN_SET)
        for t in tokens:
            h.write("#check @%s\n" % t)
        path = h.name
    header = 1 + OPEN_SET.count("\n")
    proc = subprocess.run(
        ["lake", "env", "lean", "-DmaxErrors=200000", path],
        capture_output=True,
        text=True,
    )
    os.unlink(path)
    return probe_unresolved(proc.stdout + proc.stderr, path, header, tokens, proc.returncode)


def merge_line_comments(regions):
    """Merge a run of consecutive `--` lines into one fragment.

    `comment_regions` yields one region per `--` line, which is the right granularity for
    everything except a citation span that wraps *between* two of them -- five such spans exist in
    this tree, and with one region per line no regex can see them.  Merging is confined to lines
    that are literally adjacent, so a `--` comment separated from the next by code stays separate.
    """
    def is_line_comment(text: str) -> bool:
        return "\n" not in text and text.lstrip().startswith("--")

    out: list = []
    for line, text in regions:
        prev = out[-1] if out else None
        if (prev and is_line_comment(text) and is_line_comment(prev[1].rsplit("\n", 1)[-1])
                and prev[0] + prev[1].count("\n") + 1 == line):
            out[-1] = (out[-1][0], out[-1][1] + "\n" + text)
        else:
            out.append((line, text))
    return out


def _loc(path, line) -> str:
    """`file:line`, or the file alone when the line is not meaningful -- a `--diff` hunk."""
    return path if line is None else "%s:%d" % (path, line)


def _first_odd_line(text: str) -> int:
    """Offset of the first line from which the running backtick parity is odd and stays odd.

    The stray backtick is what a reader has to find, and it is not the fragment's first line.  In
    `IndSchemeLimitComponents.lean` -- the defect this check was written for -- the comment starts
    at line 6 and the unclosed span opens at line 35, 29 lines and 119 backticks later.  Falls back
    to the fragment start when the parity is already odd on the first line.
    """
    parity, last_even = 0, -1
    for i, line in enumerate(text.split("\n")):
        parity ^= line.count("`") & 1
        if not parity:
            last_even = i
    return last_even + 1


def unbalanced_fragments(fragments):
    """Yield `(file, line)` for each comment fragment with an odd number of backticks.

    Before the newline-crossing `BACKTICKED`, a stray backtick cost one span on one line.  Now it
    re-pairs every backtick after it, so the whole fragment is read as the wrong text -- which is
    exactly the failure this script exists to catch, turned on the script itself.

    **Parity catches a missing closer and nothing else.**  A *balanced* mis-pairing -- a span
    nested inside another -- has an even count and passes this check silently; `nested_spans` is
    the instrument for that class, and the two together are what the tree is held to.  Exactly one
    fragment was unbalanced when issue 1482 made the regex cross lines: a missing closer in
    `IndSchemeLimitComponents.lean`, worth five citations.  The nested pair in
    `TateGraphCodiagonalXLift.lean` fixed in the same commit was found by diffing the old and new
    token maps, not by this check.  Both are fixed in the tree.
    """
    for path, line, text in fragments:
        stripped = strip_fences(text)
        if stripped.count("`") % 2:
            yield path, None if line is None else line + _first_odd_line(stripped)


def nested_spans(fragments):
    """Yield `(file, line)` for each run of adjacent backticks in a comment fragment.

    The class parity cannot see.  `` `a `b` `` is balanced and still mis-pairs: the outer span
    closes at the inner one's opener, and everything after it reads as the wrong text.  It cost
    `graphCodiagX_inr` in `TateGraphCodiagonalXLift.lean` for two weeks with no signal at all.

    The tree-wide baseline is **0** (`1b1d684`), and it is zero for a reason rather than by luck,
    so the check is exact rather than merely quiet.  Unlike parity it also survives slicing, which
    is why it fails a `--diff` run: a hunk can hide a run of backticks but not invent one.  The one
    way it could is a hunk that adds a single fence line, since `strip_fences` then leaves the
    block's text in place -- that did not occur once in the 712 added hunks measured in `collect`.
    """
    for path, line, text in fragments:
        stripped = strip_fences(text)
        for m in ADJACENT.finditer(stripped):
            yield path, None if line is None else line + stripped[: m.start()].count("\n")


def added_lines(diff_range: str):
    """Yield `(file, text)` for each added *hunk* of a diff, restricted to Lean sources.

    One entry per contiguous run of added lines rather than per line: a citation span that wraps
    is one token, and joining the run is what lets `tokens_of` see it.  Lines from different hunks
    are not contiguous in the new file and are never joined.
    """
    out = subprocess.run(
        ["git", "diff", "--unified=0", diff_range, "--", "*.lean"],
        capture_output=True, text=True, check=True,
    ).stdout
    current, block = None, []
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            if block:
                yield current, "\n".join(block)
            current, block = line[6:], []
        elif line.startswith("+") and not line.startswith("+++"):
            block.append(line[1:])
        elif block:
            yield current, "\n".join(block)
            block = []
    if block:
        yield current, "\n".join(block)


def collect(args):
    """Return `(sites, unbalanced, nested)`: `{token: [(file, line), ...]}` and the defect lists.

    Both checks run in both modes; they are not worth the same in each.  A `--tree` fragment is a
    whole comment, so both are exact and both fail the run.  A `--diff` hunk is an arbitrary slice
    of a file, so a span opened on an *unchanged* line leaves the added text with an odd count and
    nothing wrong -- over the 712 added hunks of the last 60 commits on `master` that happened
    once, and that once was benign, so `--diff` prints unbalanced as advisory and does not fail on
    it.  Adjacent backticks cannot be manufactured by slicing, so `nested_spans` fails either mode.

    Nothing in `.github/workflows/` invokes this script; the convention in `CONTRIBUTING.md` is
    what binds it, and an author runs it by hand.  The printed lines are the signal, not the exit
    status -- `--tree` returns 1 on the standing backlog alone.
    """
    sites: dict[str, list] = {}
    fragments = []
    if args.tree:
        for f in sorted(glob.glob("FormalSchemes/*.lean")):
            src = open(f, encoding="utf-8").read()
            for ln, frag in merge_line_comments(comment_regions(src)):
                fragments.append((f, ln, frag))
                for tok, at in tokens_of(frag, ln):
                    sites.setdefault(tok, []).append((f, at))
    else:
        # An added hunk is judged on its own: a comment marker is not needed, since a backticked
        # identifier in added Lean code is either a citation or inside a string.  A hunk's line
        # numbers are not the file's, so its fragment carries `None` and reports as the file alone.
        for f, text in added_lines(args.diff):
            fragments.append((f, None, text))
            for tok, _ in tokens_of(text, 0):
                sites.setdefault(tok, []).append((f, 0))
    return sites, list(unbalanced_fragments(fragments)), list(nested_spans(fragments))


# Every case here is one this script got wrong before issue 1482, stated as the smallest input
# that shows it.  The second is the one that cost real citations: a span wrapped at the 100-column
# limit is always an *expression*, because the wrap happens at a space and a Lean name has none --
# so the loss is never the wrapped span itself, it is the next citation, whose opening backtick the
# unmatched span used to consume.
SELFTEST = [
    ("a citation on one line is unchanged",
     "-- see `FormalSpectrum.awayCompletionHom_eq_algebraMap`\n", 1,
     ["FormalSpectrum.awayCompletionHom_eq_algebraMap"]),
    ("a wrapped span is one notation token, and the citation after it still pairs",
     "/-- `a ≫\nb` then `Iso.symm` -/", 1, ["a ≫ b", "Iso.symm"]),
    ("a `--` marker on the continuation line is layout, not part of the span",
     "-- `a ≫\n-- b` then `Iso.symm`\n", 1, ["a ≫ b", "Iso.symm"]),
    ("a fenced block is code: its contents are not citations",
     "/-!\n```\nlet `x` := 1\n```\n`Iso.symm`\n-/", 1, ["Iso.symm"]),
]


def selftest() -> int:
    bad = 0
    for name, src, line, want in SELFTEST:
        got = [t for t, _ in tokens_of(src, line)]
        ok = got == want
        bad += not ok
        print("%s  %s" % ("ok  " if ok else "FAIL", name))
        if not ok:
            print("        want %r\n        got  %r" % (want, got))
    src = "/-- `a` and `b -/"
    got = list(unbalanced_fragments([("<selftest>", 1, src)]))
    ok = got == [("<selftest>", 1)]
    bad += not ok
    print("%s  an odd backtick is reported, not silently re-paired" % ("ok  " if ok else "FAIL"))

    src = "/-- `a` and `b`\nno backticks on this line\nstray ` opens\nand nothing closes it -/"
    got = list(unbalanced_fragments([("<selftest>", 1, src)]))
    ok = got == [("<selftest>", 3)]
    bad += not ok
    print("%s  the report points at the stray backtick, not the fragment's first line"
          % ("ok  " if ok else "FAIL"))
    if not ok:
        print("        want %r\n        got  %r" % ([("<selftest>", 3)], got))

    # The assertion is about the *report*, not the token list: the token list for a nested pair is
    # wrong by construction, which is the whole reason the class needs a check of its own.
    src = "/-- `a \u21a6 f of `g x`` -/"
    got = list(nested_spans([("<selftest>", 1, src)]))
    ok = got == [("<selftest>", 1)] and not list(unbalanced_fragments([("<selftest>", 1, src)]))
    bad += not ok
    print("%s  a nested pair is reported, though its backtick count is even"
          % ("ok  " if ok else "FAIL"))
    if not ok:
        print("        want %r and no parity report\n        got  %r" % ([("<selftest>", 1)], got))

    # The scope of the line-pointer check (issue 1517): a project pointer in either spelling and at
    # either a line or a range, a Mathlib pointer that shares the project file's *basename*, and
    # the two shapes it must not swallow -- a module name and a bare path.
    fake = {"FormalSchemes/Gluing.lean", "Gluing.lean"}
    want = [("Gluing.lean:48", True), ("FormalSchemes/Gluing.lean:48", True),
            ("Gluing.lean:48-52", True),
            ("Mathlib/AlgebraicGeometry/Gluing.lean:262-423", False),
            ("FormalSchemes.Gluing", False), ("Gluing.lean", False)]
    got = [(t, project_line_pointer(t, fake)) for t, _ in want]
    ok = got == want
    bad += not ok
    print("%s  a project line pointer is reported and a Mathlib one is not"
          % ("ok  " if ok else "FAIL"))
    if not ok:
        print("        want %r\n        got  %r" % (want, got))

    # The Markdown scan (issue 1530), on the four inputs that define it: a pointer that cites a
    # location, the same token *displayed* inside a mention span, a pointer inside a fenced block,
    # and the Mathlib pointer.  Only the first is a defect, and the second is what `CONTRIBUTING.md`
    # needs in order to be able to state the rule at all.
    doc = ("cited: `Gluing.lean:48`\n"
           "displayed: `` `Gluing.lean:48` ``\n"
           "```\n`Gluing.lean:52`\n```\n"
           "`Mathlib/AlgebraicGeometry/Gluing.lean:262-423`\n")
    want = [(1, "Gluing.lean:48")]
    got = list(line_pointers_in_markdown(doc, fake))
    ok = got == want
    bad += not ok
    print("%s  in Markdown a cited pointer is reported and a displayed one is not"
          % ("ok  " if ok else "FAIL"))
    if not ok:
        print("        want %r\n        got  %r" % (want, got))

    # The root module list (issue 2022).  It is not excludable by shape and it is not a module, so
    # `project_paths` is the only thing that can classify it; before that entry existed all three
    # of these read the other way and a docstring could not name the file at all.  The three are
    # asserted together because the fix is as much about *where* the entry goes as about its being
    # there.  Independent of the working directory: the two globs may come back empty, and neither
    # answer below depends on them.
    want = [("excluded by shape", None), ("a project path", True), ("a project module", False)]
    got = [("excluded by shape", is_excluded(ROOT_MODULE_LIST)),
           ("a project path", ROOT_MODULE_LIST in project_paths()),
           ("a project module", ROOT_MODULE_LIST in project_modules())]
    ok = got == want
    bad += not ok
    print("%s  the root module list is a project path, and is not a module"
          % ("ok  " if ok else "FAIL"))
    if not ok:
        print("        want %r\n        got  %r" % (want, got))

    # The probe guard (issue 2099).  Every transcript below is a real one, shortened: the script
    # answered `0 UNRESOLVED` on the first of them three times in thirty hours, once into a
    # shipped pull-request body, because the only error sat on the `import` line where no token
    # lives.  These six cases are the reason `probe_unresolved` is a function and not a loop
    # inside `resolve_declarations` -- `--selftest` invokes no `lake`, so a transcript is the only
    # way to reach the failure at all.  `header` is 3 here as in the real probe, so the first
    # `#check` is line 4.
    probe = "/probe.lean"
    def guard(name, transcript, tokens, rc, want):
        nonlocal bad
        try:
            got = probe_unresolved(transcript, probe, 3, tokens, rc)
        except ProbeDidNotElaborate:
            got = "FATAL"
        ok = got == want
        bad += not ok
        print("%s  %s" % ("ok  " if ok else "FAIL", name))
        if not ok:
            print("        want %r\n        got  %r" % (want, got))

    guard("a probe whose `import` failed is fatal, and is not an empty unresolved set",
          probe + ":1:0: error: unknown module prefix 'FormalSchemes'\n",
          ["Foo.bar", "Foo.baz"], 1, "FATAL")
    guard("a healthy transcript still names exactly the token that did not resolve",
          probe + ":5:8: error(lean.unknownIdentifier): Unknown identifier `Foo.baz`\n",
          ["Foo.bar", "Foo.baz", "Foo.qux"], 1, {"Foo.baz"})
    guard("a `lake` failure before `lean` ran is fatal, though it names no line of the probe",
          "error: no such file or directory (error code: 2)\n", ["Foo.bar"], 1, "FATAL")
    guard("a probe that failed and said nothing at all is fatal on its exit code alone",
          "", ["Foo.bar"], 1, "FATAL")
    guard("an `open` that stopped naming a namespace is fatal even while the `#check`s answer",
          probe + ":2:5: error: unknown namespace 'FormalSpectrum'\n"
          + probe + ":5:8: error(lean.unknownIdentifier): Unknown identifier `Foo.baz`\n",
          ["Foo.bar", "Foo.baz"], 1, "FATAL")
    guard("an error at a `#check` line that is not an unknown identifier is neither",
          probe + ":4:8: error(lean.ambiguous): ambiguous, possible interpretations …\n",
          ["Foo.bar", "Foo.baz"], 1, set())

    # The staleness gate (issue 2109).  `--selftest` invokes no `lake`, so again a transcript is
    # the only way to reach the refusal.  All four below are real and shortened: the first from a
    # healthy tree, the second from a checkout whose `.lake` had been built from another branch --
    # this row's own slot, unaltered, which is how the gap was measured rather than supposed --
    # and the last two from a `lake` that failed for a reason of its own.  The third and fourth
    # exist because the *message* has rules too: without them a loosening that stopped naming the
    # out-of-date module, or stopped quoting `lake` when it listed none, would pass.
    # The two lead sentences, pinned as literals rather than imported from `probe_stale`, so that
    # rewording one is a deliberate act with a failing test attached (issue 2113).  Each branch
    # asserts its own lead *and* the absence of the other's: before 2113 the refusal opened with
    # the staleness sentence on all three branches, and cases 3 and 4 asserted only on the detail
    # line, which is why three sessions on this file never saw it.  A collapse back to one shared
    # lead now fails two cases in whichever direction it collapses.
    _STALE_LEAD = "`.lake` is not a build of this checkout"
    _UNKNOWN_LEAD = "`lake` did not answer, so whether `.lake` is a build of this checkout is"

    def build(name, transcript, rc, want, wants=(), nots=()):
        nonlocal bad
        msg = ""
        try:
            got = probe_stale(transcript, rc, LIBRARY)
        except ProbeTreeIsStale as exc:
            got, msg = "FATAL", str(exc)
        ok = got == want and all(w in msg for w in wants) and not any(w in msg for w in nots)
        bad += not ok
        print("%s  %s" % ("ok  " if ok else "FAIL", name))
        if not ok:
            print("        want %r containing %r and not %r\n        got  %r containing %r"
                  % (want, list(wants), list(nots), got, msg))

    build("an up-to-date tree passes the gate and is not an empty list of complaints",
          "All targets up-to-date (3506 jobs).\n", 0, [])
    # Verbatim, not shortened, and that matters: `lake` interleaves a `✖`/`error` pair per module
    # above the list, so the *fifth* non-empty line is still the third module.  A loosening that
    # stopped reading the list and fell back to quoting `lake`'s first five lines would name
    # `TateShift` either way and pass a shortened transcript.  `CompletionBasicOpenGlue` is
    # reachable only through the list, so asserting it is what makes that rule visible.
    build("an out-of-date tree is fatal, and the report names every module `lake` listed",
          "✖ [2741/2931] Building FormalSchemes.TateShift\n"
          "error: target is out-of-date and needs to be rebuilt\n"
          "✖ [2951/3506] Building FormalSchemes.TwoPatchFibreProductProjectionLeft\n"
          "error: target is out-of-date and needs to be rebuilt\n"
          "✖ [3053/3506] Building FormalSchemes.GeneralFibreProductBaseChange\n"
          "error: target is out-of-date and needs to be rebuilt\n"
          "✖ [3222/3506] Building FormalSchemes.CompletionGlueTwoPatchCondition\n"
          "error: target is out-of-date and needs to be rebuilt\n"
          "✖ [3284/3506] Building FormalSchemes.CompletionBasicOpenGlue\n"
          "error: target is out-of-date and needs to be rebuilt\n"
          "Some required targets logged failures:\n"
          "- FormalSchemes.TateShift\n"
          "- FormalSchemes.TwoPatchFibreProductProjectionLeft\n"
          "- FormalSchemes.GeneralFibreProductBaseChange\n"
          "- FormalSchemes.CompletionGlueTwoPatchCondition\n"
          "- FormalSchemes.CompletionBasicOpenGlue\n", 3, "FATAL",
          ("out of date:", "FormalSchemes.TateShift", "FormalSchemes.CompletionBasicOpenGlue",
           _STALE_LEAD), (_UNKNOWN_LEAD,))
    build("a `lake` that failed for a reason of its own says only that `lake` did not answer",
          "error: unknown target 'FormalSchemez'\n", 1, "FATAL",
          ("unknown target 'FormalSchemez'", _UNKNOWN_LEAD), (_STALE_LEAD,))
    build("a `lake` that failed and said nothing at all is fatal on its exit code alone",
          "", 2, "FATAL", ("exited 2 and printed nothing", _UNKNOWN_LEAD), (_STALE_LEAD,))
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--diff", metavar="RANGE", help="audit the added lines of a git diff range")
    g.add_argument("--tree", action="store_true", help="audit every comment in FormalSchemes/")
    g.add_argument("--selftest", action="store_true", help="check the tokenizer, no build needed")
    ap.add_argument("--verbose", action="store_true", help="also list the excluded tokens")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    sites, unbalanced, nested = collect(args)
    modules = project_modules()
    paths = project_paths()

    excluded, candidates = {}, []
    for tok in sorted(sites):
        why = is_excluded(tok)
        if why:
            excluded.setdefault(why, []).append(tok)
        elif tok not in modules and tok not in paths:
            candidates.append(tok)

    pointers = [t for t in sorted(sites) if project_line_pointer(t, paths)]
    md_pointers = markdown_line_pointers(paths)
    try:
        unresolved = resolve_declarations(candidates)
    except (ProbeDidNotElaborate, ProbeTreeIsStale) as exc:
        # Nothing is printed before this.  The population counts below are read off the sources
        # and would have been right either way, which is exactly what makes a report carrying
        # them and a zero UNRESOLVED line indistinguishable from a clean run -- and, for the
        # stale case, what makes a report carrying them and a *plausible* UNRESOLVED line
        # indistinguishable from a true one.  Both exit 2: see `ProbeTreeIsStale`.
        print("PROBE FAILED: %s" % exc, file=sys.stderr)
        return 2
    resolved = [t for t in candidates if t not in unresolved]

    n = lambda ts: sum(len(sites[t]) for t in ts)
    print("backticked tokens        : %5d distinct, %5d occurrences"
          % (len(sites), n(sites)))
    for why in sorted(excluded):
        print("  excluded (%-14s): %5d distinct, %5d occurrences"
              % (why, len(excluded[why]), n(excluded[why])))
        if args.verbose:
            print("      " + ", ".join(excluded[why]))
    inrepo = [t for t in sites if t in modules or t in paths]
    print("  module name or path     : %5d distinct, %5d occurrences"
          % (len(inrepo), n(inrepo)))
    print("  resolves as declaration : %5d distinct, %5d occurrences"
          % (len(resolved), n(resolved)))
    print("  UNRESOLVED              : %5d distinct, %5d occurrences"
          % (len(unresolved), n(unresolved)))

    print("  unbalanced fragments    : %5d%s"
          % (len(unbalanced), "" if args.tree else "   (advisory: a hunk is a slice)"))
    print("  nested spans            : %5d" % len(nested))
    print("  project line pointers   : %5d distinct, %5d occurrences"
          % (len(pointers), n(pointers)))
    print("  ... in Markdown         : %5d   (whole documents, not the diff)"
          % len(md_pointers))

    for tok in sorted(unresolved, key=lambda t: (-len(sites[t]), t)):
        where = sites[tok][0]
        loc = where[0] if where[1] == 0 else "%s:%d" % where
        print("  %4d  %-50s %s" % (len(sites[tok]), tok, loc))
    for path, line in unbalanced:
        print("  %-10s  %s -- an odd backtick re-pairs the rest of this comment"
              % ("UNBALANCED" if args.tree else "unbalanced", _loc(path, line)))
    for path, line in nested:
        print("  %-10s  %s -- adjacent backticks re-pair the span they sit in"
              % ("NESTED", _loc(path, line)))
    for tok in sorted(pointers, key=lambda t: (-len(sites[t]), t)):
        where = sites[tok][0]
        loc = where[0] if where[1] == 0 else "%s:%d" % where
        print("  %-10s  %s -- `%s` names a line, which nothing checks; name the declaration"
              % ("POINTER", loc, tok))
    for path, line, tok in md_pointers:
        print("  %-10s  %s:%d -- `%s` names a line; name the declaration, or display the token"
              " in a ``...`` mention span if you mean to quote it"
              % ("POINTER", path, line, tok))
    # Parity is exact on a whole comment and advisory on a hunk; adjacent backticks are exact on
    # both, and so is a line pointer -- slicing a hunk can neither manufacture nor destroy one.
    # See `collect` for the measurement that settled the asymmetry.  The Markdown scan reads whole
    # documents in either mode, so it is exact in both for the reason `markdown_line_pointers`
    # gives.
    return 1 if unresolved or nested or pointers or md_pointers or (
        unbalanced and args.tree) else 0


if __name__ == "__main__":
    sys.exit(main())
