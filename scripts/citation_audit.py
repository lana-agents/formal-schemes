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

BACKTICKED = re.compile(r"`([^`\n]+)`")

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


def tokens_of(text: str, base_line: int):
    for m in BACKTICKED.finditer(text):
        yield m.group(1), base_line + text[: m.start()].count("\n")


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


def added_lines(diff_range: str):
    """Yield `(file, text)` for each added line of a diff, restricted to Lean sources."""
    out = subprocess.run(
        ["git", "diff", "--unified=0", diff_range, "--", "*.lean"],
        capture_output=True, text=True, check=True,
    ).stdout
    current = None
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            current = line[6:]
        elif line.startswith("+") and not line.startswith("+++"):
            yield current, line[1:]


def collect(args):
    """Return `{token: [(file, line), ...]}` over the selected sources."""
    sites: dict[str, list] = {}
    if args.tree:
        for f in sorted(glob.glob("FormalSchemes/*.lean")):
            src = open(f, encoding="utf-8").read()
            for ln, frag in comment_regions(src):
                for tok, at in tokens_of(frag, ln):
                    sites.setdefault(tok, []).append((f, at))
    else:
        # An added line is judged on its own: a comment marker is not needed, since a backticked
        # identifier in added Lean code is either a citation or inside a string.
        for f, text in added_lines(args.diff):
            for tok, _ in tokens_of(text, 0):
                sites.setdefault(tok, []).append((f, 0))
    return sites


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--diff", metavar="RANGE", help="audit the added lines of a git diff range")
    g.add_argument("--tree", action="store_true", help="audit every comment in FormalSchemes/")
    ap.add_argument("--verbose", action="store_true", help="also list the excluded tokens")
    args = ap.parse_args()

    sites = collect(args)
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

    for tok in sorted(unresolved, key=lambda t: (-len(sites[t]), t)):
        where = sites[tok][0]
        loc = where[0] if where[1] == 0 else "%s:%d" % where
        print("  %4d  %-50s %s" % (len(sites[tok]), tok, loc))
    return 1 if unresolved else 0


if __name__ == "__main__":
    sys.exit(main())
