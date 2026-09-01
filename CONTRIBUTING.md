# Conventions

Conventions that a build cannot check, written down once so that they are not re-derived — or
re-litigated — in every pull request.

## The docstring citation convention

**A backticked token that names a Lean declaration is a citation, and a citation must resolve.**
That includes a bare shorthand used as a second reference after a qualified first mention in the
same paragraph: it is a citation too, and it must resolve on its own. There is no
shorthand-after-a-qualified-mention exception; the measurement that killed it is below.

`lake build` never checks this. A docstring naming a declaration that does not exist compiles
exactly like one naming a declaration that does, so the audit is the only thing standing between
the tree and a docstring full of dead names.

### The audit

It runs on **the added lines of a diff**, after a full build:

```sh
python3 scripts/citation_audit.py --diff upstream/master...HEAD
```

A token counts as resolving if it resolves as **any one** of:

* a **declaration** — `#check @Token` succeeds under `import FormalSchemes` with the project open
  set (`AlgebraicGeometry`, `AlgebraicGeometry.LocallyRingedSpace`, `CategoryTheory`,
  `CategoryTheory.Limits`, `FormalSpectrum`, `TopologicalSpace`);
* a **project module** — `FormalSchemes.Foo`, with `FormalSchemes/Foo.lean` present;
* a **repository path** — `FormalSchemes/Foo.lean` or the bare `Foo.lean`, present.

Use the **shortest resolving spelling**, and check that it resolves **in the citing file's own
`open` context** as well as under the audit's, since the file is where a reader meets it.

For every token the audit still reports, the author does one of exactly two things, in the pull
request body: **qualify it until it resolves**, or **name the non-citation category it falls in**,
from the closed list below. Passing over it in silence is the defect this convention exists to
stop — two pull requests independently shipped the same broken citation in twelve hours by
inheriting it from a neighbouring docstring, and no build failed either time.

### What is not a citation

The first four the script decides mechanically. The last three it cannot, so they are what an
author names in the PR body; the list is closed, and a token outside it that does not resolve is a
defect.

* **Notation** — `𝒪_{Spf R}`, `V(I)`, `D(a)`, `Iⁿ`. Not identifier-shaped, so the audit never
  raises it. (Superscripts are not Lean identifier characters; subscripts are. `Iⁿ` is notation,
  `U₂` is a name.)
* **Prose variables of one or two characters** — `R`, `X`, `f`, `hθ`, `t'`. These name a binder of
  the surrounding statement.
* **Name fragments** — a token beginning with `_` (`_hom_snd`, `_comp_pr₂`), used to talk about the
  tail of a family of generated names.
* **Lean vocabulary** — `simp`, `subst`, `whnf`, `instances`: tactics and configuration fields, not
  declarations.
* **Longer prose variables** — `T_inv`, `U_n`, `hnode`, `hστ`, `R_f`. Same category as the
  two-character ones and just as legitimate, but not mechanically separable from a declaration
  name, so **say which binder it is**.
* **Dot-notation on a local** — `I.FG`, `e.symm`, `f.base`, `D.J`. A projection applied to a
  variable named in the same sentence; it can never resolve, and it should not be rewritten to.
* **A field of a structure named, qualified, in the same sentence** — `t_fac` and `f_open` after
  `CategoryTheory.GlueData'`. This is the one place a shorthand stands, and it is bounded: the
  structure must be named in the sentence, not merely somewhere in the file.

### Why a bare shorthand is a citation, and not prose

Settled by measurement on the token that produced the defect twice (issue 1423).

`ofGlueData'` — bare, resolving nowhere; `GlueData.ofGlueData'` and
`CategoryTheory.GlueData.ofGlueData'` both resolve — appeared bare **24 times in 13 files**. The
case for reading it as prose was that each occurrence is a second reference in a paragraph whose
first reference is already qualified. Measured, that is true of **6** of the 24. **Twelve** are
never qualified anywhere in their own file, so under any "after a qualified first mention"
exception they stay defects, and every occurrence has to be adjudicated one at a time — which is
the cost the exception was supposed to remove.

Tree-wide the same exception excuses **395 of 13,168** unresolved non-module occurrences: 3%. It
buys almost nothing and it is not free. So there is no exception, and all 24 are now qualified.

### The standing backlog

`python3 scripts/citation_audit.py --tree` runs the same check over every comment in the tree. It
is a **measurement, not a gate**: on 2026-09-01 it reported 1302 distinct unresolved tokens over
4604 occurrences, of which 843 (3428 occurrences) have a qualified spelling that would resolve and
459 (1176) have none in any spelling. Most of that residue is the last three categories above —
longer prose variables, dot-notation on locals, structure fields — and clearing it is not a
prerequisite for anything. The convention binds the diff; the tree-wide number is there so that
the backlog is a known quantity rather than a surprise.

### Two traps that have cost this tree real work

* **`glue_condition_apply` cannot be found by grep.** It is generated by `@[elementwise]` on
  `CategoryTheory.GlueData.glue_condition`, so no `theorem glue_condition_apply` line exists in
  Mathlib, and the namespace its call sites suggest (`TopCat.GlueData`) is not the one it resolves
  under. Resolve names by `#check`, never by grep.
* **`git grep -nw` returns zero hits, silently, for any name ending in `₀`/`₁`.** U+2080 and
  U+2081 are Unicode category `No` and form no word boundary. Use bare-string greps.

## Line width

Every line is at most **100 characters and 100 display columns** — two separate limits, since a
line of subscripts and arrows can satisfy one and fail the other. Measure with Python (`len` for
the first, `unicodedata.east_asian_width` with combining marks at zero for the second). `awk`'s
`length()` counts bytes and over-reports on any line with a non-ASCII character.

`lake env lean <file>` does **not** apply the lakefile's `leanOptions`, so it runs neither
`linter.style.longLine` nor the `show`-vs-`change` linter. Iterate with it if you like, but finish
on `lake build`, and re-measure after **every** rewrap.
