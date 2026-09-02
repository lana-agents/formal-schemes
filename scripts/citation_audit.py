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

`--selftest` checks the tokenizer against the cases it used to get wrong and needs no build.

Resolution of the declaration case is done by elaborating one `#check @Token` per distinct token
in a single throwaway Lean file, which costs one `import FormalSchemes` and a few seconds.
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


def resolve_declarations(tokens: list[str]) -> set[str]:
    """Return the subset of `tokens` that `#check @token` fails to resolve."""
    if not tokens:
        return set()
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as h:
        h.write("import FormalSchemes\n" + OPEN_SET)
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
    unresolved = set()
    for line in (proc.stdout + proc.stderr).splitlines():
        m = re.match(re.escape(path) + r":(\d+):\d+: error(.*)", line)
        if not m:
            continue
        idx = int(m.group(1)) - header - 1
        if "unknownIdentifier" not in m.group(2):
            # An ambiguous or overloaded name resolves — to more than one constant.  That is a
            # different complaint, and not this script's.
            continue
        if 0 <= idx < len(tokens):
            unresolved.add(tokens[idx])
    return unresolved


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


def unbalanced_fragments(fragments):
    """Yield `(file, line)` for each comment fragment with an odd number of backticks.

    Before the newline-crossing `BACKTICKED`, a stray backtick cost one span on one line.  Now it
    re-pairs every backtick after it, so the whole fragment is read as the wrong text -- which is
    exactly the failure this script exists to catch, turned on the script itself.  Two such
    fragments existed when issue 1482 made the regex cross lines, both genuine prose defects
    (a missing closer and a nested pair); both are fixed in the tree.
    """
    for path, line, text in fragments:
        if strip_fences(text).count("`") % 2:
            yield path, line


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
    """Return `({token: [(file, line), ...]}, [(file, line) unbalanced])` over the sources."""
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
        # identifier in added Lean code is either a citation or inside a string.
        for f, text in added_lines(args.diff):
            for tok, _ in tokens_of(text, 0):
                sites.setdefault(tok, []).append((f, 0))
    return sites, list(unbalanced_fragments(fragments))


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

    sites, unbalanced = collect(args)
    modules = project_modules()
    # Both spellings the tree uses: the path, and the bare file name after a locative.
    paths = set(glob.glob("FormalSchemes/*.lean"))
    paths |= {os.path.basename(f) for f in paths}

    excluded, candidates = {}, []
    for tok in sorted(sites):
        why = is_excluded(tok)
        if why:
            excluded.setdefault(why, []).append(tok)
        elif tok not in modules and tok not in paths:
            candidates.append(tok)

    unresolved = resolve_declarations(candidates)
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

    print("  unbalanced fragments    : %5d" % len(unbalanced))

    for tok in sorted(unresolved, key=lambda t: (-len(sites[t]), t)):
        where = sites[tok][0]
        loc = where[0] if where[1] == 0 else "%s:%d" % where
        print("  %4d  %-50s %s" % (len(sites[tok]), tok, loc))
    for path, line in unbalanced:
        print("  UNBALANCED  %s:%d -- an odd backtick re-pairs the rest of this comment"
              % (path, line))
    return 1 if unresolved or unbalanced else 0


if __name__ == "__main__":
    sys.exit(main())
