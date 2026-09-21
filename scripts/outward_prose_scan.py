#!/usr/bin/env python3
"""Flag prose *anywhere* on the tree that describes how a just-changed declaration is proved.

The other four instruments in `scripts/` are tree walks: each asks *"is this tree internally
consistent right now?"* and answers it from the tree alone.  A refactor raises a different
question -- *"who, anywhere, describes how **this proof** works?"* -- and that question is anchored
on a **declaration name**, not on a file position, which is why no tree walk can be made to answer
it and why this is the only instrument here that takes a diff as input.

Three sessions wrote a version of this by hand and each found a real defect:

* issue 2048 / PR #720 -- a falsified sentence in the **file header**, about a thousand characters
  above the declaration it describes;
* issue 2065 / PR #752 -- **three** falsified sentences in three *other* files, which became issue
  2144;
* issue 2144 / PR #753 -- the same scan re-run over all ten of #752's names with a wider cue list,
  confirming that 2144 was the whole class rather than a sample.

Each was written from scratch, in a different dialect, and thrown away.  **Widening the window is
not the fix** -- #720's miss was in the same file and out of reach of any sane window, #752's was
in another file entirely.  Widen the *anchor*: scan every comment on the tree for the name.

Usage, from the repository root.  No `lake`, no build, no environment.

    python3 scripts/outward_prose_scan.py --diff upstream/master...HEAD
    python3 scripts/outward_prose_scan.py \
        --names tateChainInv_glueMorphisms_compat,glueChartMorphisms
    python3 scripts/outward_prose_scan.py --diff badd407...987e195 --cues 'four-case|unfold'
    python3 scripts/outward_prose_scan.py --selftest

## There is no `--tree` mode and no MISMATCH verdict, on purpose

Without a diff there is no set of changed names, so there is no tree-wide invariant to enforce: a
`--tree` run would either pass always or fail always.  Every hit here is a **question for a
human**, exactly as in `docstring_signature_scan.py`, and the output is modelled on that scanner
rather than on `closure_audit.py`.  For the same reason this is **not** wired into
`.orchestra/validation.sh`.

## The five things that are easy to get wrong

* **Comment spans are found directly, by a lexer, not by diffing a stripped copy against the
  original.**  A stripper that blanks code and a stripper that blanks comments are both fine for
  *reading* one side; recovering *positions* by comparing the two is where sessions have lost time,
  because the two disagree by two characters at every `-/`.  `comment_spans` below returns offsets
  into the file on disk and nothing is aligned against anything.
* **String literals are code.**  `"-- not a comment"` must not open one, and a `\"` inside a string
  must not close it.  `--selftest` pins both.  *Char* literals are deliberately **not** tracked:
  `'` is an identifier character on this tree (`ofGlueData'`, `cgcNe'`), so a lexer that opened a
  char literal at every `'` would swallow the rest of the file.  The population that would need it
  is `'"'` and `'\\'` in code, measured 0 under `FormalSchemes/` when this was written -- and even
  a miss there only mis-classifies code as comment, which costs a spurious question, never a
  missed one.
* **The unit of context is the prose block, not the line and not the file.**  Consecutive `--`
  lines are one paragraph and a window clipped to a single line cannot see the sentence the cue is
  in; a window taken from the raw file would let *code* supply the cue.  Adjacent comment spans
  separated by nothing but whitespace are merged, and the window is clipped to the merged block.
* **The diff's own files are scanned by default, and that is a correction to issue 2147's
  design.**  That row proposed excluding them, *"since those are covered by the in-file sweep a
  refactor already owes"*.  Measured: issue 2048's finding -- the first of the three this scan
  exists to reproduce -- is in `ChartedDatumGlueOpenImmersion.lean:28-29`, a file the diff touches,
  about seventy lines above the nearest declaration and describing a `glueChartMorphisms` that is
  declared in another file entirely.  **Excluding touched files loses it**, and the in-file sweep
  that was supposed to cover it is exactly the windowed scan that missed it.  `--exclude-touched`
  is available and is not the default.
* **A `git diff` names two paths, not one, and either may be `/dev/null`.**  `changed_lines` keeps
  the `-` side and the `+` side in separate variables and keys each at its own path.  One variable
  attributes a deleted file's hunks to whatever file preceded it in the diff: on `ba2e4ce` (issue
  805 / PR #290, which deletes two modules and modifies eight) that is **8 names lost and 9
  invented**, and the lost ones are the names the commit is about.  The same root cause drops a
  rename's `-` side, because it looks the old lines up at the *new* path and `git show` then exits
  non-zero; `befe0fd` renames ten `.lean` files -- twenty paths -- in one commit, and fixing this
  recovers **13** of the 37 names in its range.  And the headers cannot be recognised by shape:
  under `--unified=0` a deleted `-- comment` renders in the diff **body** as `--- comment`, **171**
  times across this tree's last two hundred commits (in 70 of them) when this was written, so a
  header is read only while one is pending after a `diff --git` line.

## What this scan cannot reach, and it is not a window width

This scan is anchored on a **name**.  Three consequences, all of them established by measurement on
this tree rather than by argument, and none of them fixed by widening `WINDOW`:

* A claim whose subject is a **population** -- *"only the `₀`-orientations meet the bookkeeping"*,
  *"no proof in this file unfolds the `dite`"*, *"each statement below is given at both index
  pairs"* -- is outside its reach whenever the declarations that falsify it are not named in the
  sentence, because there is then no name for the anchor to key on.  Issue 2158 is exactly that
  shape, and forcing the four lemma names in by hand still does not reach it.
* A sentence that was **false when it was written** is outside its reach too: no diff ever changes
  a name in it, so `--diff` never supplies the key.
* **A hit's line number is not its excerpt.**  The ±230-character window is anchored on the
  occurrence, so it can land a pointer *inside* a defective paragraph while clipping the defective
  clause out of what is printed.  That is what happened to issue 2158: the LIVE run of PR #761
  emitted `CompletionGlueTwoPatchCondition.lean:54  completionTwoPatchDesc`, four lines below the
  false clause, and the printed context began after it.  **The `file:line` is the finding; the
  excerpt is a hint.**

Issue 2156 item 1 was catchable only because that sentence happens to *name* a declaration the diff
changed.  Read a green run as "no sentence naming a changed declaration sits beside a cue", which
is what it says, and not as coverage of the population class.

## The cue list, and why it is a flag rather than a constant

A bare name census is unusable: `tateSelfProductDiagonal` had 13 comment occurrences at #753's head
and every one of them was about the morphism Δ, not about a case split.  The cues are what make
the output readable.  They are also the part most likely to be wrong, so they are a flag --
`--cues <regex>` replaces the default, `--extra-cues <regex>` adds to it.  Issue 2144 widened the
previous run's list and got the **same** real-hit set, which is the only evidence available that
the default is not over-fitted to the run that produced it; re-widen it when you use this, and say
whether the set moved.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys


# `-/` closes; `/-` nests.  `--` runs to end of line.  Both are handled by `comment_spans` below
# rather than by a regex, because neither is a regular language once `/-` nests.
DEFAULT_CUES = (r"diagonal|t_id|four-case|four case|unfold|ofGlueData'|by_cases|dif_neg|"
                r"eqToHom|case split|heartbeat|transparency")

# The declaration openers this scan resolves.  `example` is absent because it has no name, and an
# anonymous `instance` is skipped for the same reason: the token after the keyword is then `:` or
# `(`, and `NAME` does not match it.
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*"
                  r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|"
                  r"scoped\s+|local\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+"
                  r"([^\s:({\[]+)")

# The scope stack, as `option_reference_audit.py` walks it -- including the `noncomputable section`
# spelling, which that scanner did not know until issue 2130 and which is the majority of this
# tree's section openers.  `end` is matched unindented only: an indented `end` closes a `do` or a
# `match`, not a scope.
NAMESPACE = re.compile(r"^namespace\s+(\S+)")
SECTION = re.compile(r"^(?:noncomputable\s+)?section\b\s*(\S*)")
END = re.compile(r"^end\b\s*(\S*)")

# A `+`/`-` line of a `git diff` body, and a hunk header.  `--unified=0` is what makes the line
# numbers usable: with context lines the ranges include code nobody changed.
HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")

WINDOW = 230


def comment_spans(text: str) -> list[tuple[int, int]]:
    """Every comment's `(start, end)` half-open offsets into `text`, outermost spans only.

    A four-state lexer: code, string, line comment, block comment at depth n.  Offsets are into
    the string that was passed in, so a caller can slice `text` with them and can turn one into a
    line number by counting newlines -- nothing is recovered by alignment.
    """
    spans: list[tuple[int, int]] = []
    i, n = 0, len(text)
    depth, start = 0, 0
    while i < n:
        if depth:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                if depth == 0:
                    spans.append((start, i))
                continue
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            i += 1
            continue
        if text.startswith("/-", i):
            depth, start = 1, i
            i += 2
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            spans.append((i, end))
            i = end
            continue
        if text[i] == '"':
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        i += 1
    if depth:
        # An unterminated `/-` is a syntax error the compiler will report; treat the rest of the
        # file as comment rather than as code, so this scan errs towards asking a question.
        spans.append((start, n))
    return spans


def prose_blocks(text: str) -> list[tuple[int, int]]:
    """`comment_spans`, with spans merged across nothing-but-whitespace gaps.

    Consecutive `--` lines are one paragraph and the cue for an occurrence on one of them is
    routinely on another.  A gap containing any code stops the merge, so a trailing `--` comment
    after a statement is never merged with the next one.
    """
    merged: list[list[int]] = []
    for start, end in comment_spans(text):
        if merged and not text[merged[-1][1]:start].strip():
            merged[-1][1] = end
        else:
            merged.append([start, end])
    return [(a, b) for a, b in merged]


def mask_comments(text: str) -> str:
    """`text` with every comment character replaced by a space, positions preserved.

    Used only by the scope walk: a `namespace` written inside a docstring must not push a scope.
    Newlines are kept so that line numbers survive.
    """
    out = list(text)
    for start, end in comment_spans(text):
        for i in range(start, end):
            if out[i] != "\n":
                out[i] = " "
    return "".join(out)


def declarations(text: str) -> list[tuple[int, str]]:
    """Every named declaration of `text` as `(1-based line, fully qualified name)`.

    The name is the `namespace` stack joined with the declaration's own stem, and a stem that
    already carries dots is left alone -- this tree writes both
    `theorem AlgebraicGeometry.foo` and a bare `foo` inside `namespace AlgebraicGeometry`.
    """
    found: list[tuple[int, str]] = []
    stack: list[str | None] = []          # a `namespace` pushes its name; a `section` pushes None
    for number, line in enumerate(mask_comments(text).split("\n"), 1):
        bare = line.rstrip()
        if NAMESPACE.match(bare):
            stack.append(NAMESPACE.match(bare).group(1))
            continue
        if SECTION.match(bare):
            stack.append(None)
            continue
        if END.match(bare):
            if stack:
                stack.pop()
            continue
        hit = DECL.match(line)
        if not hit:
            continue
        stem = hit.group(2)
        prefix = ".".join(part for part in stack if part)
        found.append((number, "%s.%s" % (prefix, stem) if prefix else stem))
    return found


def header_path(line: str) -> str | None:
    """The path a `--- `/`+++ ` header names, or `None` when that side is `/dev/null`.

    The `a/` / `b/` prefixes are stripped when present and tolerated when they are not, so a diff
    taken with `diff.noprefix` still resolves.
    """
    value = line[4:].split("\t")[0]
    if value == "/dev/null":
        return None
    for prefix in ("a/", "b/"):
        if value.startswith(prefix):
            return value[len(prefix):]
    return value


def changed_lines(diff: str) -> dict[str, tuple[set[int], set[int]]]:
    """`{path: (lines changed on the `-` side, lines changed on the `+` side)}` from a `git diff`.

    Needs `--unified=0`: with context lines the ranges cover code nobody touched, and a scan keyed
    on *changed declarations* would then take the whole file.

    **The two sides are tracked separately and keyed at their own paths**, because they are not
    always the same path and either of them may be absent.  A deletion is `+++ /dev/null`, an
    addition is `--- /dev/null`, and a rename names the old path on one side and the new on the
    other; a parser with one `path` variable attributes a deleted file's hunks to whatever file
    preceded it in the diff, which is 8 names lost and 9 invented on this repository's own
    `ba2e4ce`.  A rename resolves its `-` side at the **old** path, which is where `git show
    <base>:<path>` can find it.

    **The file headers are recognised only while one is pending**, i.e. between a `diff --git` line
    and the `+++ ` that closes the pair.  Shape alone is not enough: under `--unified=0` a deleted
    `-- comment` renders in the diff *body* as `--- comment`, and this tree's last two hundred
    commits contain 171 such lines, in 70 of them.
    """
    out: dict[str, tuple[set[int], set[int]]] = {}
    old_path = new_path = None
    pending = False
    for line in diff.split("\n"):
        if line.startswith("diff --git "):
            old_path = new_path = None
            pending = True
            continue
        if pending and line.startswith("--- "):
            old_path = header_path(line)
            continue
        if pending and line.startswith("+++ "):
            new_path = header_path(line)
            pending = False
            continue
        hit = HUNK.match(line)
        if not hit:
            continue
        old, old_n, new, new_n = (int(hit.group(1)), int(hit.group(2) or 1),
                                  int(hit.group(3)), int(hit.group(4) or 1))
        if old_path is not None and old_n:
            out.setdefault(old_path, (set(), set()))[0].update(range(old, old + old_n))
        if new_path is not None and new_n:
            out.setdefault(new_path, (set(), set()))[1].update(range(new, new + new_n))
    return out


def touched_declarations(text: str, lines: set[int]) -> set[str]:
    """The declarations of `text` whose *extent* meets `lines`.

    A declaration's extent runs from its opening line to the line before the next declaration or
    the next unindented `end`, which is what makes a change to a proof *body* count.  Exact
    extents would need the elaborator; this over-approximates at the tail of a declaration and
    never under-approximates, which is the safe direction for a scan whose output is a question.
    """
    if not lines:
        return set()
    masked = text.split("\n")
    stops = {number for number, line in enumerate(mask_comments(text).split("\n"), 1)
             if END.match(line.rstrip())}
    decls = declarations(text)
    names: set[str] = set()
    for index, (number, name) in enumerate(decls):
        following = decls[index + 1][0] if index + 1 < len(decls) else len(masked) + 1
        for stop in sorted(stops):
            if number < stop < following:
                following = stop
                break
        if any(number <= line < following for line in lines):
            names.add(name)
    return names


def names_from_diff(diff_range: str, root: str = ".") -> tuple[set[str], set[str]]:
    """`(declaration names changed in the range, `.lean` files the range touches)`.

    Both ends are walked, so a *deleted* declaration is still a name to scan for -- prose that
    describes how a deleted proof worked is exactly the class this instrument is about.  That is
    why `changed_lines` keys each side at its own path: a deleted module's names live at
    `<base>:<old path>` and nowhere else, and a renamed one's `-` side does too.
    """
    base, _, head = diff_range.partition("...")
    if not head:
        base, _, head = diff_range.partition("..")
    diff = subprocess.run(["git", "-C", root, "diff", "--unified=0", diff_range, "--", "*.lean"],
                          capture_output=True, text=True, check=True).stdout
    names: set[str] = set()
    files = set()
    for path, (old_lines, new_lines) in changed_lines(diff).items():
        files.add(path)
        for rev, lines in ((base, old_lines), (head, new_lines)):
            if not rev or not lines:
                continue
            shown = subprocess.run(["git", "-C", root, "show", "%s:%s" % (rev, path)],
                                   capture_output=True, text=True)
            if shown.returncode == 0:
                names |= touched_declarations(shown.stdout, lines)
    return names, files


def lean_files(root: str = ".") -> list[str]:
    """Every module under `FormalSchemes/`, by a filesystem walk.

    A walk and not `git ls-files`: a `git archive` extraction is not a repository, and this scan is
    routinely pointed at one.
    """
    out = []
    for base, _, entries in os.walk(os.path.join(root, "FormalSchemes")):
        for entry in entries:
            if entry.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(base, entry), root))
    return sorted(out)


def flatten(text: str) -> str:
    return " ".join(text.split())


def scan_file(text: str, names: list[str], cues: re.Pattern, window: int = WINDOW):
    """Every comment occurrence of a name in `text` whose prose block window matches `cues`."""
    hits = []
    blocks = prose_blocks(text)
    if not blocks:
        return hits
    for name in names:
        stem = name.rsplit(".", 1)[-1]
        for match in re.finditer(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(stem), text):
            at = match.start()
            block = next(((a, b) for a, b in blocks if a <= at < b), None)
            if block is None:
                continue
            low = max(block[0], at - window)
            high = min(block[1], at + len(stem) + window)
            context = flatten(text[low:high])
            if cues.search(context):
                hits.append({"name": stem, "line": text.count("\n", 0, at) + 1,
                             "context": context})
    return hits


def scan(root: str, names: set[str], exclude: set[str], cues: re.Pattern):
    ordered = sorted(names)
    results = []
    for path in lean_files(root):
        if path in exclude:
            continue
        with open(os.path.join(root, path), encoding="utf-8") as handle:
            text = handle.read()
        for hit in scan_file(text, ordered, cues):
            hit["path"] = path
            results.append(hit)
    return sorted(results, key=lambda h: (h["path"], h["line"], h["name"]))


def report(root: str, names: set[str], exclude: set[str], cues: re.Pattern, pattern: str,
           touched: set[str]) -> int:
    hits = scan(root, names, exclude, cues)
    print("declaration names scanned for    : %4d" % len(names))
    print("modules under FormalSchemes/     : %4d   (%d excluded, listed below)"
          % (len(lean_files(root)), len(exclude)))
    if touched:
        inside = sorted(touched & set(lean_files(root)))
        print("the diff's own files             : %4d   (%d of them scanned, not excluded)"
              % (len(touched), len(set(inside) - exclude)))
    print("cue pattern                      : %s" % pattern)
    print("FLAGGED: prose naming a changed declaration beside a proof-method cue : %4d"
          % len(hits))
    for hit in hits:
        print("  %s:%d  %s" % (hit["path"], hit["line"], hit["name"]))
        print("      %s" % hit["context"][:400])
    if exclude:
        print()
        print("excluded, and therefore not a claim about them:")
        for path in sorted(exclude):
            print("    %s" % path)
    if names:
        print()
        print("names scanned: %s" % ", ".join(sorted(names)))
    print()
    print("A flag is a question, not a finding: repair the sentence, repair the proof, or decline")
    print("it by name with a reason.  A flag left unmentioned is a defect.  This scan has no")
    print("verdict and no exit code of its own -- there is no tree-wide invariant here to break.")
    return 0


def selftest() -> int:
    """Pin the shapes this lexer and this window exist to get right.  No build, no tree."""
    ok, fail = 0, 0

    def check(label: str, got, want) -> None:
        nonlocal ok, fail
        if got == want:
            ok += 1
            print("ok    %s" % label)
        else:
            fail += 1
            print("FAIL  %s: got %r, wanted %r" % (label, got, want))

    cues = re.compile(DEFAULT_CUES)

    def names_of(text, names=("foo",), cue=cues):
        return [(h["name"], h["line"]) for h in scan_file(text, list(names), cue)]

    # --- the two classes drawn from real misses -------------------------------------------------
    # Issue 2065 / PR #752: the falsified sentence was in another *file*.  `scan` walks every
    # module, so the case here is that a file with no declaration of its own still reports.
    other_file = "/-!\n# Notes\n\n`foo`'s proof is four-case and unfolds the `dite`.\n-/\n"
    check("a hit in a file that declares nothing is found (issue 2065's class)",
          names_of(other_file), [("foo", 4)])

    # Issue 2048 / PR #720: the falsified sentence was in the file *header*, about a thousand
    # characters above the declaration.  A window anchored on the declaration cannot reach it; a
    # scan anchored on the name does not care how far away it is.
    far = ("/-!\n# Header\n\n`foo` is proved by a four-case split.\n-/\n\n"
           + "-- filler\n" * 120
           + "theorem foo : True := trivial\n")
    check("a hit a thousand characters from the declaration is found (issue 2048's class)",
          names_of(far), [("foo", 4)])
    check("that hit really is far from the declaration",
          far.index("theorem foo") - far.index("`foo`") > 1000, True)

    # --- the lexer ------------------------------------------------------------------------------
    check("a name in code, not in a comment, is not reported",
          names_of("theorem foo : True := by\n  unfold bar\n  trivial\n"), [])
    check("a nested `/- /- -/ -/` does not end the span early",
          names_of("/- outer /- inner -/ `foo` unfolds it -/\n"), [("foo", 1)])
    check("a `--` inside a string literal does not open a comment",
          names_of('def s : String := "-- foo unfolds it"\n'), [])
    check("a `/-` inside a string literal does not open a comment",
          names_of('def s : String := "/- foo unfolds it -/"\n'), [])
    check("an escaped quote does not end the string early",
          names_of('def s : String := "a \\" -- foo unfolds it"\n'), [])
    check("a `\"` inside a comment does not open a string that swallows the next comment",
          names_of('-- a quote " here\n-- `foo` unfolds it\n'), [("foo", 2)])
    check("an unterminated `/-` is read as comment to end of file rather than as code",
          names_of("/- open\n`foo` unfolds it\n"), [("foo", 2)])
    # The offsets are into the file on disk and are not recovered by aligning a stripped copy
    # against the original -- the trap this scan was told twice not to walk into.
    positioned = "code\n-- `foo` unfolds\n"
    check("comment_spans offsets slice the original text, not a stripped copy",
          [positioned[a:b] for a, b in comment_spans(positioned)], ["-- `foo` unfolds"])
    blocked = "-- one\n-- two\ncode\n-- three\n"
    check("a prose block merges adjacent `--` lines and stops at code",
          [blocked[a:b] for a, b in prose_blocks(blocked)], ["-- one\n-- two", "-- three"])

    # --- the cue filter, which is what makes the output readable --------------------------------
    check("a cue-free hit is not reported (the 13 `tateSelfProductDiagonal` occurrences)",
          names_of("-- `foo` is the object this file is about.\n"), [])
    check("the cue may sit on a neighbouring `--` line of the same paragraph",
          names_of("-- `foo` is restated here,\n-- and its proof is four-case.\n"), [("foo", 1)])
    check("a cue in code after a trailing comment does not count: the block stops at the code",
          names_of("-- `foo` is restated here.\ntheorem t : True := by unfold bar\n"), [])
    check("a custom cue pattern replaces the default",
          names_of("-- `foo` is proved by strong induction.\n", cue=re.compile("induction")),
          [("foo", 1)])

    # --- names: suffix matching and word boundaries ---------------------------------------------
    check("a qualified name is matched by its last component, as prose writes it",
          names_of("-- `A.B.foo` unfolds the `dite`.\n", names=("Ns.foo",)), [("foo", 1)])
    check("a longer identifier containing the name is not a hit",
          names_of("-- `foo_bar` unfolds the `dite`.\n"), [])
    check("a primed sibling is not a hit, because `'` is an identifier character here",
          names_of("-- `foo'` unfolds the `dite`.\n"), [])

    # --- the scope walk and the diff plumbing ---------------------------------------------------
    src = ("namespace AlgebraicGeometry\n"
           "noncomputable section\n"
           "theorem foo : True := by\n"
           "  trivial\n"
           "end\n"
           "theorem bar : True := trivial\n"
           "end AlgebraicGeometry\n"
           "theorem baz : True := trivial\n")
    check("the scope stack qualifies a declaration, and `noncomputable section` opens a scope",
          declarations(src),
          [(3, "AlgebraicGeometry.foo"), (6, "AlgebraicGeometry.bar"), (8, "baz")])
    check("a `namespace` inside a docstring does not push a scope",
          declarations("/-- see `namespace Other` -/\ntheorem foo : True := trivial\n"),
          [(2, "foo")])
    check("an anonymous `instance` has no name to scan for and is skipped",
          declarations("instance : Inhabited Nat := ⟨0⟩\ninstance i : Inhabited Bool := ⟨true⟩\n"),
          [(2, "i")])
    check("a modifier before the keyword does not hide the declaration",
          declarations("private theorem foo : True := trivial\n"
                       "@[simp] protected noncomputable def bar : Nat := 0\n"),
          [(1, "foo"), (2, "bar")])
    check("a change inside a proof body attributes to the declaration it is in, not the next one",
          touched_declarations(src, {4}), {"AlgebraicGeometry.foo"})
    check("a change on a declaration's own line attributes to it",
          touched_declarations(src, {6}), {"AlgebraicGeometry.bar"})
    check("a change on a scope-closing `end` attributes to no declaration",
          touched_declarations(src, {5}), set())
    check("an empty change set names nothing", touched_declarations(src, set()), set())
    modify = ("diff --git a/A.lean b/A.lean\n--- a/A.lean\n+++ b/A.lean\n")
    check("hunk headers with no explicit length mean one line",
          changed_lines(modify + "@@ -3 +3 @@\n-x\n+y\n"), {"A.lean": ({3}, {3})})
    check("hunk headers with a zero-length side are read as empty on that side",
          changed_lines(modify + "@@ -3,0 +4,2 @@\n+y\n+z\n"),
          {"A.lean": (set(), {4, 5})})
    deletion = ("diff --git a/B.lean b/B.lean\ndeleted file mode 100644\n"
                "--- a/B.lean\n+++ /dev/null\n@@ -1,2 +0,0 @@\n-x\n-y\n")
    check("a deleted file's hunks attribute to its own old side, not to the file before it",
          changed_lines(modify + "@@ -3 +3 @@\n-x\n+y\n" + deletion),
          {"A.lean": ({3}, {3}), "B.lean": ({1, 2}, set())})
    check("a deleted file alone in the diff yields its own old-side lines",
          changed_lines(deletion), {"B.lean": ({1, 2}, set())})
    check("a removed `-- comment` in the body is not read as a file header",
          changed_lines(modify + "@@ -3,2 +3 @@\n--- not a header\n-x\n+y\n"),
          {"A.lean": ({3, 4}, {3})})
    check("an added `++ ...` line in the body is not read as a file header",
          changed_lines(modify + "@@ -3 +3,2 @@\n-x\n+++ not a header\n+y\n"),
          {"A.lean": ({3}, {3, 4})})
    check("a rename resolves the old side at the old path",
          changed_lines("diff --git a/Old.lean b/New.lean\nsimilarity index 90%\n"
                        "rename from Old.lean\nrename to New.lean\n"
                        "--- a/Old.lean\n+++ b/New.lean\n@@ -7 +9 @@\n-x\n+y\n"),
          {"Old.lean": ({7}, set()), "New.lean": (set(), {9})})
    check("an added file's hunks attribute to its new side only",
          changed_lines("diff --git a/C.lean b/C.lean\nnew file mode 100644\n"
                        "--- /dev/null\n+++ b/C.lean\n@@ -0,0 +1,2 @@\n+x\n+y\n"),
          {"C.lean": (set(), {1, 2})})

    print("\n%d ok / %d FAIL" % (ok, fail))
    return 1 if fail else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--diff", metavar="RANGE",
                        help="a `git diff` range; changed declarations become the names")
    parser.add_argument("--names", help="comma-separated declaration names, added to `--diff`'s")
    parser.add_argument("--exclude", help="comma-separated paths to skip; nothing by default")
    parser.add_argument("--exclude-touched", action="store_true",
                        help="skip the `.lean` files `--diff` touches.  NOT the default: issue "
                             "2048's finding is in one of them, seventy lines from the nearest "
                             "declaration -- see the module docstring.")
    parser.add_argument("--cues", default=DEFAULT_CUES, help="replace the cue pattern")
    parser.add_argument("--extra-cues", help="add alternatives to the cue pattern")
    parser.add_argument("--root", default=".", help="tree to scan; may be an extraction")
    parser.add_argument("--diff-root", help="repository to read `--diff` from, when it is not "
                                            "the tree being scanned -- a `git archive` "
                                            "extraction is not a repository and `git diff` "
                                            "dies in one.  Defaults to --root.")
    parser.add_argument("--selftest", action="store_true", help="needs no build and no tree")
    args = parser.parse_args()

    if args.selftest:
        return selftest()
    if not args.diff and not args.names:
        parser.error("one of --diff or --names is required")

    names: set[str] = set()
    touched: set[str] = set()
    if args.diff:
        names, touched = names_from_diff(args.diff, args.diff_root or args.root)
    if args.names:
        names |= {n.strip() for n in args.names.split(",") if n.strip()}
    exclude = {p.strip() for p in (args.exclude or "").split(",") if p.strip()}
    if args.exclude_touched:
        exclude |= touched
    pattern = args.cues if not args.extra_cues else "%s|%s" % (args.cues, args.extra_cues)
    return report(args.root, names, exclude, re.compile(pattern), pattern, touched)


if __name__ == "__main__":
    sys.exit(main())
