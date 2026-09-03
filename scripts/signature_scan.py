#!/usr/bin/env python3
"""Group this project's declarations by the shape of their statements and report the collisions.

The dedup umbrella (issue 1395) scanned names and terms.  Two duplicates that mattered were
invisible to both, and issue 1534 filed the reason: they are **signature**-shaped.

* `FormalSpectrum.sectionsMk` and `FormalSpectrum.sectionsOpenHom` are the same ring map
  `R -> Gamma (U, O_Spf)`.  They share no morpheme, so a name scan is blind; one is an
  `IsLimit.lift` and the other a restriction of `globalSectionsEquiv.symm`, so they are not the
  same term and a term scan is blind.  Their *conclusions* print identically, and that is what
  found them.
* `FormalScheme.exists_openImmersion` and `LocallyRingedSpace.hasAffineChartAt_of_formalScheme`
  are one statement written unfolded and folded.  Nothing here merges them: their types differ
  syntactically and agree only after `whnf`.  The extractor marks the class in its `foldable`
  column; normalising it is a `MetaM` pass and belongs in a successor.

Usage, from the repository root, after a full `lake build`:

    lake env lean scripts/signature_scan.lean > /tmp/signatures.tsv
    python3 scripts/signature_scan.py /tmp/signatures.tsv

`--selftest` checks the filters against the shapes they exist to drop and needs no build.

## Which key, and what each one misses

`--key concl` (the default) buckets on the **pretty-printed conclusion**.  It is insensitive to
the binder list, which is what lets it see one map written twice under different instance
arguments; it is also blind to the binders' *types*, so fields of unrelated structures collide as
`Ideal self.K`.  `--key type` buckets on the hash of the whole type: exact, three times quieter,
and it does **not** find `sectionsMk`, because `sectionsOpenHom` carries two instance binders it
does not.  Run both.

## What a bucket means, and what it does not

**A bucket is a question, not a finding.** On `9dbf476`, under `--key type`, 55 of the 86 buckets
span more than one module and *none* survived being read:

* A **`def` bucket** usually holds one construction at several parameters -- `tateChain` and
  `tateChainInv`, `swapFirstSummandXY` and its `...Inv`, the five glue data.  Identical types
  because they are the same construction, which is the point of them.
* A **`thm` bucket** holds two proofs of one statement, and on this tree both were deliberate and
  said so: `IsTopologicallyFiniteType.self_of_two_charts` and `..._pow` are non-vacuity witnesses
  for two different criteria, and `tateSelfProductDiagonal_surjective_stalkMap_of_pr1` records a
  cheaper second route to a stalk fact.  Read the docstrings before filing anything.

So the number to act on is not the bucket count but the count that survives being read.
"""

from __future__ import annotations

import argparse
import collections
import sys

# Names Lean generates for us.  `Name.isInternalDetail` catches most of it in the extractor; these
# are the shapes that survive it, 512 of 6226 declarations on `9dbf476`.
AUTO = ("congr_simp", "eq_def", "injEq", "noConfusion", "sizeOf", "_proof_", ".eq_",
        ".match_", "brecOn", "below", "binductionOn", "toCtorIdx", "casesOn", "recOn")

# A conclusion that is a sort says nothing: `def A : Type u` would collide with every other
# type-valued definition in the library.  `?` is the extractor's marker for a conclusion it could
# not print, and it must not be allowed to collide with itself either.
def is_sortish(concl: str) -> bool:
    """True for a conclusion that carries no statement."""
    return concl in ("Prop", "?") or concl.startswith("Type ") or concl.startswith("Sort ")


def is_auto(name: str) -> bool:
    """True for a name Lean generated rather than an author."""
    return any(a in name for a in AUTO)


def read(path):
    rows, total = [], None
    with open(path, encoding="utf-8") as f:
        for line in f:
            field = line.rstrip("\n").split("\t")
            if field[0] == "DECL" and len(field) >= 8:
                rows.append(field)
            elif field[0] == "TOTAL":
                total = int(field[1])
    return rows, total


def report(path: str, key: str, cross_only: bool) -> int:
    rows, total = read(path)
    if not rows:
        print("no declarations read from %s -- did the extractor run?" % path)
        return 1
    auto = [r for r in rows if is_auto(r[1])]
    rest = [r for r in rows if not is_auto(r[1])]
    sortish = [r for r in rest if is_sortish(r[7])]
    kept = [r for r in rest if not is_sortish(r[7])]

    idx = {"type": 4, "concl": 7}[key]
    buckets = collections.defaultdict(list)
    for r in kept:
        buckets[r[idx]].append(r)
    multi = {k: v for k, v in buckets.items() if len(v) > 1}
    cross = {k: v for k, v in multi.items() if len({r[2] for r in v}) > 1}
    thm = sum(1 for v in cross.values() if any(r[3] == "thm" for r in v))

    print("key                          : %s" % key)
    print("declarations extracted       : %5d%s"
          % (len(rows), "" if total in (None, len(rows)) else "   (TOTAL says %d)" % total))
    print("  generated names dropped    : %5d" % len(auto))
    print("  sort-valued conclusions    : %5d" % len(sortish))
    print("  population bucketed        : %5d" % len(kept))
    print("    theorems                 : %5d" % sum(1 for r in kept if r[3] == "thm"))
    print("    definitions              : %5d" % sum(1 for r in kept if r[3] == "def"))
    print("    foldable conclusions     : %5d   (`whnf` would change them)"
          % sum(1 for r in kept if r[6] == "1"))
    print("distinct keys                : %5d" % len(buckets))
    print("buckets with two or more     : %5d" % len(multi))
    print("  spanning more than a module: %5d" % len(cross))
    print("  of those, theorem buckets  : %5d   (read every one)" % thm)

    shown = cross if cross_only else multi
    for k, v in sorted(shown.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        kinds = "/".join(sorted({r[3] for r in v}))
        label = k if key == "concl" else "#" + k
        print("\nBUCKET  n=%d  %s  %s" % (len(v), kinds, label[:96]))
        for r in sorted(v, key=lambda r: r[1]):
            print("    %-4s %-66s %s" % (r[3], r[1], r[2]))
    return 0


def selftest() -> int:
    bad = 0
    names = [("AlgebraicGeometry.foo.congr_simp", True), ("Foo.eq_def", True),
             ("Foo.mk.injEq", True), ("FormalSpectrum.sectionsMk", False),
             ("FormalSpectrum.sectionsOpenHom", False),
             ("IsTopologicallyFiniteType.self_of_two_charts", False)]
    got = [(n, is_auto(n)) for n, _ in names]
    ok = got == names
    bad += not ok
    print("%s  a generated name is dropped and an authored one is not" % ("ok  " if ok else "FAIL"))
    if not ok:
        print("        want %r\n        got  %r" % (names, got))

    concls = [("Type u_1", True), ("Prop", True), ("Sort u", True), ("?", True),
              ("R ->+* X", False), ("Ideal self.K", False)]
    got = [(c, is_sortish(c)) for c, _ in concls]
    ok = got == concls
    bad += not ok
    print("%s  a conclusion that carries no statement is dropped" % ("ok  " if ok else "FAIL"))
    if not ok:
        print("        want %r\n        got  %r" % (concls, got))
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("tsv", nargs="?", help="output of `lake env lean scripts/signature_scan.lean`")
    ap.add_argument("--key", default="concl", choices=["concl", "type"],
                    help="bucket on the printed conclusion (default) or the whole type's hash")
    ap.add_argument("--all", action="store_true", help="also show buckets confined to one module")
    ap.add_argument("--selftest", action="store_true", help="check the filters, no build needed")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if not args.tsv:
        ap.error("a TSV is required unless --selftest")
    return report(args.tsv, args.key, not args.all)


if __name__ == "__main__":
    sys.exit(main())
