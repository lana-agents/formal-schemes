#!/usr/bin/env python3
"""Check that a comment saying another declaration needs the same `set_option` is still true.

Every `set_option` in this tree is justified in an adjacent comment, and a good number of those
comments are *cross-references*: they say the option is the same one some **other** declaration
needs, and point at it by name.  That sentence is a claim about the declaration it names, not
about the file it sits in, so a refactor which removes the option from the named declaration
falsifies a sentence that may be anywhere on the tree -- and **removing an option cannot fail a
build**, so the whole class is invisible to CI by construction.  It is invisible to this tree's
other four instruments too: `closure_audit.py` only sees sentences carrying an anchor and a
figure, `citation_audit.py` resolves the *name* and does not model a property attributed to it,
`docstring_signature_scan.py` reads docstrings against signatures and these are `--` comments,
and `lake build` cannot read English.  Three such sentences were left false by one pull request
and were found by a reviewer reading the diff by hand (issue 2106, from issue 2064's review).

Usage, from the repository root.  It reads sources, so it needs no build and invokes no `lake`:

    python3 scripts/option_reference_audit.py --tree
    python3 scripts/option_reference_audit.py --selftest

The three populations follow `closure_audit.py`'s house shape, and **`declined` is an honest
answer rather than a failure**: it is the scanner saying it could not read the sentence, which
here is the commonest outcome, because a large minority of these cross-references point at a
*module* or at a Mathlib declaration rather than at a declaration on this tree.

What is checked is exactly one thing: *does the declaration this sentence names still carry an
option of the family the sentence claims?*  Whether the stated **reason** is the true reason is
not mechanically decidable and is deliberately out of scope.
"""

from __future__ import annotations

import argparse
import glob
import os
import re
import sys

LIBRARY = "FormalSchemes"

# The option families, keyed by the English word a sentence uses, because the sentence is what is
# being checked and *"the same transparency requirement"* said of a declaration carrying only a
# `maxHeartbeats` raise is exactly the near-miss worth catching.  Matching on the option name
# instead would collapse the two families into "carries some option" and lose that.  `linter.*` is
# in no family and is not attributed at all: `set_option linter.style.setOption false in` is the
# bookkeeping that accompanies every other option here, never the thing a sentence refers to.
FAMILIES = {
    "transparency": ("backward.isDefEq.respectTransparency", "backward.defeqAttrib.useBackward"),
    "budget": ("maxHeartbeats", "synthInstance.maxHeartbeats", "maxRecDepth"),
}
# The words that name a family.  A sentence naming none of them, but still making a same-as claim
# inside an option justification, is checked against ANY option -- `"Same requirement as `X`"` is
# a real and common phrasing on this tree and it does claim something checkable.
FAMILY_WORDS = {
    "transparency": "transparency",
    "transparencies": "transparency",
    "heartbeat": "budget",
    "heartbeats": "budget",
    "budget": "budget",
    "raise": "budget",
}
# Words that make a comment sentence an option cross-reference rather than a remark about the
# mathematics.  Without one of these, `same` in a justification comment is prose ("for the same
# reason", "the same argument"), and treating it as a claim is a false-alarm surface.
CLAIM_NOUNS = ("requirement", "requirements", "option", "options", "accommodation", "transparency",
               "heartbeat", "heartbeats", "budget", "raise", "mixture", "limit")
# A sentence in the past tense is recording *history* -- "`X` needed the same option until issue
# 2064 rerouted it" -- and is true precisely when `X` carries nothing now.  Checking it would
# invert the verdict, so it is counted separately and reported rather than silently dropped: this
# is the one phrasing that silences the scanner, and it has to stay visible for that reason.
HISTORICAL = re.compile(r"\bneeded\b|\bused to\b|\bno longer\b|\buntil\b|\bwas rerouted\b", re.I)

_DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|"
                   r"unsafe\s+|scoped\s+|local\s+)*"
                   r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
                   r"([^\s({\[:]+)")
_DECL_ANON = re.compile(r"^(?:@\[[^\]]*\]\s*)?"
                        r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*"
                        r"(?:instance|example)\b")
_SETOPT = re.compile(r"^\s*set_option\s+(\S+)\s+\S+\s+in\s*$")
_SETOPT_FILE = re.compile(r"^set_option\s+(\S+)\s+\S+\s*$")
_NAMESPACE = re.compile(r"^namespace\s+(\S+)")
_END = re.compile(r"^end\b(?:\s+(\S+))?")
_SECTION = re.compile(r"^section\b(?:\s+(\S+))?")
_ATTRIBUTE = re.compile(r"^@\[[^\]]*\]\s*$")
_LINE_COMMENT = re.compile(r"^\s*--(?!\s*$)(.*)$")
# A backticked span, taken whole.  Only identifier-shaped ones are looked up; the rest (`rfl`,
# `def`, `Spec (CommRingCat.of _)`) fall out when nothing on the tree answers to them.
_TICKED = re.compile(r"`([^`\n]+)`")
# Tokens that are Lean vocabulary rather than a name being cited.  They are listed because some
# of them *resolve*: bare `rfl` matches `Ideal.IsCofinal.rfl` on this tree and hijacked the anchor
# of five sentences in this script's first draft, in every case a sentence whose real anchor was a
# module.  Resolving is not evidence that the sentence meant that constant, which is the same
# argument `citation_audit.VOCABULARY` is written down for; this is the subset of it that turns
# up inside an option justification, kept separate rather than imported so that the two
# instruments stay independent of each other's tokenizers.
_VOCAB = set("""rfl rw simp dsimp erw decide omega trivial subst whnf isDefEq instances unfold
    delta conv congr convert ext cases induction constructor symm trans change def abbrev
    theorem instance structure Spec Spf""".split())
_IDENT = re.compile(r"^[^\W\d]['\w?!ₐ-ₜ₀-₉ᵢ-ᵥ]*(?:\.[^\W\d]['\w?!ₐ-ₜ₀-₉ᵢ-ᵥ]*)*$", re.U)


def project_paths() -> set[str]:
    """Every tracked path, spelled as a comment would spell it, plus every module name.

    An anchor that names one of these is a *module* and not a declaration, which is the commonest
    reason a sentence is declined.  Telling that case apart from "no such thing on this tree" is
    worth the few lines: the first is a sentence this scanner cannot check, the second may be a
    Mathlib declaration, and the declined block has to be walked by hand either way.
    """
    out = set()
    for p in (glob.glob("**/*.lean", recursive=True) + glob.glob("*.md")
              + glob.glob("**/*.md", recursive=True)):
        if p.startswith(".lake" + os.sep):
            continue
        out.add(p)
        out.add(os.path.basename(p))
        if p.endswith(".lean"):
            out.add(p[:-len(".lean")].replace(os.sep, "."))
    return out


def option_table(paths: list[str]) -> dict[tuple[str, str], dict]:
    """Walk each file's `set_option … in` blocks and attribute them to the declaration they prefix.

    `set_option o v in` scopes over the *next command*, which is Lean's rule and not a guess about
    layout, so the walk simply accumulates option names and hands them to the next declaration it
    meets.  Comments, `omit … in`, `attribute`, `variable` and `open … in` sit between the two in
    this tree and do not interrupt the scope; a `namespace`, `section` or `end` does, and clears
    the pending list rather than attributing it to something further down.

    The `--` comment lines of that same prefix block are carried along with it: they are the
    justification, and they are the only text this scanner reads.  A `/-- … -/` docstring in the
    block is about the mathematics and is deliberately **not** read -- it is where "at **the
    same** `w`" lives, and admitting it would turn a false-alarm-free check into a noisy one.

    A `set_option` **without** `in` is file-scoped and is attributed to every declaration in the
    file.  That case is not a detail: 258 of this tree's 405 non-`linter` options are a
    `maxHeartbeats` / `synthInstance.maxHeartbeats` pair at the top of a file, so a scanner that
    only read `… in` blocks would answer "carries nothing" for most of the tree and fire on every
    true sentence about a budget.  The two scopes are kept apart in the record so a report can
    say which one answered.  Every one of the 258 sits in the first 22 lines of its file, so
    treating them as file-scoped rather than section-scoped is a measurement and not a guess;
    re-check that before trusting this on a tree that has grown a `section`-local one.

    Keyed by `(qualified name, path)` and **not** by the name alone: 18 qualified names on
    this tree answer in more than one file -- `AlgebraicGeometry.mapSpf_congr` in five, and
    most of the rest `private` helpers repeated between sibling files -- so a name-keyed
    table silently merges their option sets, which is a false clean in one direction and a
    false alarm in the other.

    Returns `{(qualified name, path): {"options": [...], "path": …, "line": …,
    "comment": [(line, text)], "file_options": [...]}}`.
    """
    decls: dict[str, dict] = {}
    for path in paths:
        lines = open(path, encoding="utf-8").read().splitlines()
        stack: list[str] = []
        pending: list[str] = []
        comment: list[tuple[int, str]] = []
        file_opts: list[str] = []
        here: list[str] = []
        i = 0
        while i < len(lines):
            raw = lines[i]
            line = raw.rstrip()
            m = _SETOPT.match(line)
            if m:
                if not m.group(1).startswith("linter."):
                    pending.append(m.group(1))
                i += 1
                continue
            m = _SETOPT_FILE.match(line)
            if m:
                if not m.group(1).startswith("linter."):
                    file_opts.append(m.group(1))
                i += 1
                continue
            m = _LINE_COMMENT.match(line)
            if m:
                comment.append((i + 1, m.group(1).strip()))
                i += 1
                continue
            if line.strip() == "":
                i += 1
                continue
            if line.lstrip().startswith("/-"):          # docstring or section header: skip whole
                if line.lstrip().startswith("/-!"):     # a section header ends the prefix block
                    comment = []
                while i < len(lines) and "-/" not in lines[i]:
                    i += 1
                i += 1
                continue
            m = _NAMESPACE.match(line)
            if m:
                stack.append(m.group(1))
                pending, comment = [], []
                i += 1
                continue
            if _END.match(line) or _SECTION.match(line):
                if _END.match(line) and stack and _END.match(line).group(1) in (stack[-1], None):
                    stack.pop()
                pending, comment = [], []
                i += 1
                continue
            m = _DECL.match(line)
            if m or _DECL_ANON.match(line):
                name = m.group(1) if m else "_instance_%s_%d" % (os.path.basename(path), i + 1)
                full = ".".join(stack + [name]) if stack else name
                key = (full, path)
                decls.setdefault(key, {"options": [], "path": path, "line": i + 1,
                                       "comment": [], "file_options": []})
                decls[key]["options"] = sorted(set(decls[key]["options"] + pending))
                decls[key]["comment"] = comment
                here.append(key)
                pending, comment = [], []
                i += 1
                continue
            # `omit … in`, `variable`, `attribute`, `open … in` and a `@[…]` on its own line all
            # sit *inside* the prefix block in this tree and do not end the `set_option … in`
            # scope.  The standalone attribute line is the one that matters: dropping it lost
            # `chartStepLRS_comp_chartInclusion`'s own `respectTransparency`, and the scanner then
            # reported a true sentence about it as a MISMATCH.  A false clean would have been
            # worse, but a false alarm on a declaration whose option is three lines above the
            # `theorem` is the shape that gets an instrument switched off.
            if line.startswith(("omit", "include", "variable", "attribute", "open", "universe",
                                "local")) or _ATTRIBUTE.match(line):
                i += 1
                continue
            pending, comment = [], []
            i += 1
        for key in here:
            decls[key]["file_options"] = sorted(set(file_opts))
    return decls


def resolve(anchor: str, same_file: str,
            decls: dict[tuple[str, str], dict]) -> tuple[tuple[str, str] | None, str]:
    """Resolve a backticked anchor to one declaration, preferring the file the sentence is in.

    An anchor is written the way a reader would write it -- bare (`specGD_f`) or partly qualified
    (`SheafedSpace.mono_coequalizer_π_c_app`) -- so a match is *suffix on dot boundaries*.  When
    several declarations answer, the one in the sentence's own file wins, because these sentences
    say "above" and "below" and mean their own file; when several answer **in that file**, or
    when several answer and none is in it, the anchor is **declined as ambiguous** rather than
    guessed at.  That is the pinned answer to "the option is on a different declaration of the
    same name in another file": the scanner declines, and says which candidates it saw.
    """
    hits = [k for k in decls if k[0] == anchor or k[0].endswith("." + anchor)]
    if not hits:
        return None, "no declaration of that name on this tree"
    local = [k for k in hits if k[1] == same_file]
    pool = local or hits
    if len(pool) > 1:
        return None, "ambiguous: %s" % ", ".join("%s (%s)" % k for k in sorted(pool)[:4])
    return pool[0], ""


def sentences(text: str) -> list[str]:
    """Split a flattened comment into sentences at `. ` only.

    Not at `;` or `:`, deliberately: *"the two are `rfl` but not at `instances` transparency, as
    `X` records for the same field"* puts the family word and the claim on opposite sides of a
    comma and a semicolon, and splitting there would hide the claim from the word that types it.
    A `.` inside a qualified name is not followed by a space, so it does not split.
    """
    return [s for s in re.split(r"(?<=\.)\s+", text) if s.strip()]


def anchor_candidates(sentence: str) -> list[str]:
    """Order the backticked names of a sentence by how likely each is the thing being compared to.

    The claim reads *"same <something> as `X`"*, so the anchor is normally the first name **after**
    the word `same`.  Two phrasings on this tree put it before instead -- *"…, as `X` records for
    the same field"* -- and for those the anchor is the name **nearest before** it, which is why
    the fallback is reversed rather than left-to-right: taking the sentence's first name there
    picks up whatever the comment was explaining, not the declaration it is pointing at.
    """
    m = re.search(r"\bsame\b", sentence, re.I)
    if not m:
        return _TICKED.findall(sentence)
    after = _TICKED.findall(sentence[m.end():])
    return after or list(reversed(_TICKED.findall(sentence[:m.start()])))


def family_of(sentence: str, block: str) -> str:
    """Name the option family the sentence claims, from the English word it uses.

    Read off the sentence first and the whole justification block second -- a two-sentence comment
    routinely says "transparency" once and then "the same requirement as `X`".  A sentence naming
    no family word is checked against **any** option: it claims the named declaration carries the
    same thing this one does, without saying which, and that is still falsifiable.
    """
    for scope in (sentence, block):
        for word, fam in FAMILY_WORDS.items():
            if re.search(r"\b%s\b" % word, scope, re.I):
                return fam
    return "any"


def carries(options: list[str], family: str) -> bool:
    """Does this declaration carry an option of the claimed family?"""
    if family == "any":
        return bool(options)
    return any(o in FAMILIES[family] for o in options)


def audit(decls: dict[tuple[str, str], dict], paths: set[str]) -> dict:
    """The second pass: every same-as claim in an option justification, resolved and checked."""
    attributed, mismatch, declined, historical = [], [], [], []
    for key in sorted(decls, key=lambda k: (decls[k]["path"], decls[k]["line"])):
        d = decls[key]
        if not d["options"] or not d["comment"]:
            continue
        block = " ".join(t for _, t in d["comment"])
        for sent in sentences(block):
            if not re.search(r"\bsame\b", sent, re.I):
                continue
            if not any(re.search(r"\b%s\b" % w, sent, re.I) for w in CLAIM_NOUNS):
                continue
            site = "%s:%d" % (d["path"], d["comment"][0][0])
            rec = {"site": site, "on": key[0], "sentence": sent.strip()}
            if HISTORICAL.search(sent):
                historical.append(rec)
                continue
            fam = family_of(sent, block)
            rec["family"] = fam
            ticked = anchor_candidates(sent)
            hit, why = None, "no backticked name in the sentence resolves to a declaration"
            for tok in ticked:
                if tok in paths:
                    why = "`%s` names a module or a file, not a declaration" % tok
                    break
                if not _IDENT.match(tok) or tok in _VOCAB:
                    continue
                hit, why = resolve(tok, d["path"], decls)
                if hit:
                    rec["anchor"] = tok
                    break
            if not hit:
                rec["why"] = why
                rec["tokens"] = ticked
                declined.append(rec)
                continue
            rec["resolved"] = hit[0]
            held = decls[hit]["options"] + ["%s (file scope)" % o
                                            for o in decls[hit]["file_options"]]
            rec["carries"] = held
            attributed.append(rec)
            if not carries(decls[hit]["options"] + decls[hit]["file_options"], fam):
                mismatch.append(rec)
    return {"attributed": attributed, "mismatch": mismatch, "declined": declined,
            "historical": historical}


def report(res: dict, verbose: bool) -> int:
    print("declarations with a non-`linter` `set_option … in`: %5d" % res["n_options"])
    print("  ... of them with a `--` justification comment    : %5d" % res["n_justified"])
    print("files with a non-`linter` file-scoped `set_option` : %5d" % res["n_file_scoped"])
    print("same-as claims in the justification comments")
    print("  attributed (anchor resolved, claim checked)      : %5d" % len(res["attributed"]))
    print("  MISMATCH   (anchor carries no such option)       : %5d" % len(res["mismatch"]))
    print("  declined   (anchor not a declaration on the tree): %5d" % len(res["declined"]))
    print("  historical (past tense: a claim about what was)  : %5d" % len(res["historical"]))
    for r in res["mismatch"]:
        print("\nMISMATCH %s" % r["site"])
        print("    on        : %s" % r["on"])
        print("    claims    : %s carries a `%s` option" % (r["anchor"], r["family"]))
        print("    but %s carries: %s" % (r["resolved"], ", ".join(r["carries"]) or "nothing"))
        print("    sentence  : %s" % r["sentence"])
    if verbose:
        for kind in ("declined", "historical", "attributed"):
            print("\n--- %s ---" % kind)
            for r in res[kind]:
                extra = r.get("why") or r.get("resolved", "")
                print("%s  %s\n    %s" % (r["site"], extra, r["sentence"]))
    return 1 if res["mismatch"] else 0


def run(root: str = ".", verbose: bool = False) -> int:
    paths = sorted(glob.glob(os.path.join(root, LIBRARY, "**", "*.lean"), recursive=True))
    cwd = os.getcwd()
    os.chdir(root)
    try:
        rel = [os.path.relpath(p, root) for p in paths]
        decls = option_table(rel)
        known = project_paths()
    finally:
        os.chdir(cwd)
    res = audit(decls, known)
    res["n_options"] = sum(1 for d in decls.values() if d["options"])
    res["n_justified"] = sum(1 for d in decls.values() if d["options"] and d["comment"])
    res["n_file_scoped"] = len({d["path"] for d in decls.values() if d["file_options"]})
    return report(res, verbose)


# --------------------------------------------------------------------------------------------
# `--selftest`: canned sources, pure Python, no `lake` and no tree.  Every rule below has been
# watched to fail -- see the loosening table in the pull request of issue 2106 -- which is this
# tree's standing requirement for a check (issue 2072): a rule no case can see is dead weight.


_CASES = [
    ("a sentence whose anchor still carries the option does not fire", {
        "A.lean": """
namespace N
set_option backward.isDefEq.respectTransparency false in
-- The glue datum is a `def`, so this is needed.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as `base` above.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 0, "declined": 0, "historical": 0}),
    ("a sentence whose anchor lost the option fires", {
        "A.lean": """
namespace N
-- No option here any more.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as `base` above.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 1, "declined": 0, "historical": 0}),
    ("an anchor naming a module declines and does not fire", {
        "A.lean": """
namespace N
set_option backward.isDefEq.respectTransparency false in
-- Same accommodation as `FormalSchemes/A.lean` makes.
theorem other : True := trivial
end N
"""}, {"attributed": 0, "mismatch": 0, "declined": 1, "historical": 0}),
    ("an anchor answered by two files and by neither of its own is declined, not guessed", {
        "A.lean": """
namespace N
set_option backward.isDefEq.respectTransparency false in
-- A transparency requirement.
theorem base : True := trivial
end N
""",
        "B.lean": """
namespace N
-- The other `base`, same namespace, another file, no option at all.
theorem base : True := trivial
end N
""",
        "C.lean": """
namespace P
set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as `base`.
theorem other : True := trivial
end P
"""}, {"attributed": 0, "mismatch": 0, "declined": 1, "historical": 0}),
    ("the same-file candidate wins over a same-named one in another file, and is checked", {
        "A.lean": """
namespace N
set_option maxHeartbeats 400000 in
-- A raised budget.
theorem base : True := trivial
end N
""",
        "B.lean": """
namespace N
-- The same qualified name in another file, with no option.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as `base` above.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 1, "declined": 0, "historical": 0}),
    ("a transparency claim about a declaration carrying only a budget raise fires", {
        "A.lean": """
namespace N
set_option maxHeartbeats 400000 in
-- A raised budget, and nothing about transparency.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as `base` above.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 1, "declined": 0, "historical": 0}),
    ("a family-less claim is checked against any option and does not fire on a budget raise", {
        "A.lean": """
namespace N
set_option maxHeartbeats 400000 in
-- A raised budget.
theorem base : True := trivial

set_option maxHeartbeats 400000 in
-- Same requirement as `base` in `FormalSchemes.A`.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 0, "declined": 0, "historical": 0}),
    ("a past-tense sentence is historical and is not checked as a present claim", {
        "A.lean": """
namespace N
-- No option here any more.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- `base` above needed the same option until issue 2064 rerouted it.
theorem other : True := trivial
end N
"""}, {"attributed": 0, "mismatch": 0, "declined": 0, "historical": 1}),
    ("`same reason` with no claim noun is prose, not a claim about an option", {
        "A.lean": """
namespace N
-- No option here any more.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- The rewrite below is ill-typed without this, for the same reason `base` is stated as it is.
theorem other : True := trivial
end N
"""}, {"attributed": 0, "mismatch": 0, "declined": 0, "historical": 0}),
    ("a docstring in the prefix block is about the mathematics and is not read", {
        "A.lean": """
namespace N
-- No option here any more.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
/-- The two sides agree at **the same** point, with the same transparency requirement as
`base`. -/
theorem other : True := trivial
end N
"""}, {"attributed": 0, "mismatch": 0, "declined": 0, "historical": 0}),
    ("a `linter` option is not an option: it justifies nothing and carries no claim", {
        "A.lean": """
namespace N
set_option linter.style.setOption false in
-- Same transparency requirement as `base` above.
theorem other : True := trivial

theorem base : True := trivial
end N
"""}, {"attributed": 0, "mismatch": 0, "declined": 0, "historical": 0}),
    ("a claim two sentences after the family word still reads the family off the block", {
        "A.lean": """
namespace N
set_option maxHeartbeats 400000 in
-- A raised budget.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- The rewrite is ill-typed at `instances` transparency without this. Same requirement as
-- `base` above.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 1, "declined": 0, "historical": 0}),
    ("an option behind an `@[…]`, an `omit … in` and an `include … in` is still attributed", {
        "A.lean": """
namespace N
variable (n : Nat)
set_option backward.isDefEq.respectTransparency false in
-- The two spellings are `rfl` but not at `instances` transparency.
omit n in
include n in
@[reassoc]
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as `base` above.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 0, "declined": 0, "historical": 0}),
    ("a file-scoped `set_option` is carried by every declaration in the file", {
        "A.lean": """
set_option maxHeartbeats 3200000
namespace N
theorem base : True := trivial
end N
""",
        "B.lean": """
namespace M
set_option maxHeartbeats 400000 in
-- Same budget raise as `base` needs.
theorem other : True := trivial
end M
"""}, {"attributed": 1, "mismatch": 0, "declined": 0, "historical": 0}),
    ("a Lean keyword that happens to resolve does not hijack the anchor", {
        "A.lean": """
namespace Ideal
theorem rfl : True := trivial
end Ideal

namespace N
set_option backward.isDefEq.respectTransparency false in
-- A transparency requirement.
theorem base : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- The same transparency requirement: both sides are `rfl` only past `instances`, as in `base`.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 0, "declined": 0, "historical": 0}),
    ("with no name after the claim the anchor is the one nearest before it, not the first", {
        "A.lean": """
namespace N
set_option backward.isDefEq.respectTransparency false in
-- A transparency requirement.
theorem early : True := trivial

theorem late : True := trivial

set_option backward.isDefEq.respectTransparency false in
-- The transparency `early` needs, as `late` records for the same field.
theorem other : True := trivial
end N
"""}, {"attributed": 1, "mismatch": 1, "declined": 0, "historical": 0}),
]


def selftest() -> int:
    import tempfile
    bad = 0
    for name, files, want in _CASES:
        with tempfile.TemporaryDirectory() as tmp:
            lib = os.path.join(tmp, LIBRARY)
            os.makedirs(lib)
            for fn, src in files.items():
                open(os.path.join(lib, fn), "w", encoding="utf-8").write(src.lstrip("\n"))
            cwd = os.getcwd()
            os.chdir(tmp)
            try:
                decls = option_table(sorted(glob.glob(os.path.join(LIBRARY, "*.lean"))))
                res = audit(decls, project_paths())
            finally:
                os.chdir(cwd)
        got = {k: len(res[k]) for k in ("attributed", "mismatch", "declined", "historical")}
        ok = got == want
        bad += not ok
        print("%s  %s" % ("ok  " if ok else "FAIL", name))
        if not ok:
            print("        want %r\n        got  %r" % (want, got))
            for k in ("mismatch", "declined", "historical", "attributed"):
                for r in res[k]:
                    print("        %-10s %s" % (k, r["sentence"]))
    print("%d ok / %d FAIL" % (len(_CASES) - bad, bad))
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--tree", action="store_true", help="audit every option justification")
    g.add_argument("--selftest", action="store_true", help="canned sources, no tree, no build")
    ap.add_argument("--root", default=".", help="repository root to audit (default: .)")
    ap.add_argument("--verbose", action="store_true", help="also list declined and historical")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    return run(args.root, args.verbose)


if __name__ == "__main__":
    sys.exit(main())
