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

Use the **shortest resolving spelling**, and check it under the audit's open set, under **the
citing file's own `open` set** — the file is where a reader meets it — and against **the
declaration you actually mean**. The three checks are independent. Each has a counterexample on
this tree, so none of them can be skipped on the grounds that another passed.

* **The file's `open` *set*, not the lexical position of the citation.** A module docstring sits
  above the file's `open` line, so at its own position almost nothing is open. Reading the rule
  lexically would condemn **146 of the 231** declaration-shaped tokens in the module-docstring
  heads of the thirteen files this convention was settled on, including six of the twenty-four
  occurrences it rewrote — so the lexical reading is the one that puts the tree back in violation
  of its own convention. It is the file's open set that binds.
* **Shortest-under-the-audit is not shortest-in-the-file.** `GlueData.f_open` resolves under the
  audit's open set, to `AlgebraicGeometry.LocallyRingedSpace.GlueData.f_open`. In
  `TateSelfProductObject.lean` — inside `namespace AlgebraicGeometry`, with `CategoryTheory` open
  — the same spelling is an **unknown constant**: the head resolves to `CategoryTheory.GlueData`,
  which has no `f_open` field. There the shortest spelling is `LocallyRingedSpace.GlueData.f_open`.
* **Resolving is not resolving to the right thing.** `TopCat.GlueData.f_open` and
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.f_open` are different theorems about different
  structures, and `CategoryTheory.GlueData.f_open` does not exist at all — so that one token has
  three plausible spellings, one nonexistent and two meaning different things. A citation that
  resolves to the **wrong** declaration is worse than a bare one: unresolved is visible to the
  audit, wrong-referent is visible to nobody.

For every token the audit still reports, the author does one of exactly two things, in the pull
request body: **qualify it until it resolves**, or **name the non-citation category it falls in**,
from the closed list below. Passing over it in silence is the defect this convention exists to
stop — two pull requests independently shipped the same broken citation in twelve hours by
inheriting it from a neighbouring docstring, and no build failed either time.

### What is not a citation

The first five the script decides mechanically. The last three it cannot, so they are what an
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
* **A construction shorthand** — `Spf`, `Spec`, and nothing else. The standard mathematical name of
  a construction, standing for the whole family of declarations that realise it rather than for any
  one of them. The list is enumerated in `scripts/citation_audit.py` and the admission rule is
  below; both entries are excluded **before** the declaration case, because one of them resolves.
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

### What a construction shorthand is, and why the list is exactly two

Settled by measurement on the two tokens that broke the closed list (issue 1442), on `5823cac`.

`Spf` and `Spec` are the same kind of token, in the same sentences — "a morphism `Spf R ⟶ Spec C`",
"`Spec A` is `Spf` of its own ring taken discrete". Before this row one was condemned (317
occurrences in 129 files, unresolved) and the other waved through (172 in 63), decided entirely by
whether Mathlib happens to own the bare name. **Both verdicts were wrong**, and the one that passed
was the worse of the two.

Read a systematic 1-in-8 sample of the 317 bare `` `Spf` `` occurrences and ask, of each, which
declaration its sentence means:

| what the sentence means | of 40 | the declaration it means |
| :-- | --: | :-- |
| `Spf` of a *ring map* — a morphism | 18 | `FormalSpectrum.locallyRingedSpaceMap` |
| the functor, or the construction as a whole | 12 | `AdicRingCat.spfFunctor`, `spfEquivalence` |
| the object, at the formal-spectrum level | 8 | `FormalSpectrum.locallyRingedSpaceObj` |
| the object, as a formal scheme | 2 | `FormalScheme.Spf` |

`AlgebraicGeometry.FormalScheme.Spf` **exists**, so bare `Spf` is not a name with no referent — it
is worse than that. It is the only declaration whose bare name is `Spf`, and it is what **5%** of
the prose means. Qualifying the token to make the audit green would convert ~300 loud unresolved
citations into ~300 silent wrong-referent ones, which the third check above says is the worse
failure. That is what makes this a category and not a backlog.

A 1-in-4 sample of the 172 bare `` `Spec` `` occurrences splits the same way: 17 of 43 mean `Spec`
of a ring map, 12 the object, 9 are the adjectival "the `Spec` side" / "`Spec`-shaped" / "the
`Spec`-target theorem", and **2** mean `AlgebraicGeometry.Spec : CommRingCat ⥤ Scheme` — the one
declaration the bare token resolves to. About 95% of both tokens are wrong under (b); they differ
only in which way the audit fails to say so.

A token is a **construction shorthand**, and joins the list, when all three hold:

1. it is the standard mathematical name of a construction, in the literature and in Mathlib — not a
   name coined in this tree;
2. measured over its bare occurrences here, the prose uses it for **more than one declaration**, in
   more than one category, so that no single spelling is right for all of them;
3. the entry in `scripts/citation_audit.py` names every declaration it stands for, so that a reader
   who wants the constant can still find it.

Condition 2 is the bound, and it is what keeps the list at two. The only other tokens this tree
applies to a prose argument more than a dozen times are `algebraMap` (119 applied occurrences),
`ULift` (109), `AdicCompletion` (58), `formalCompletion` (50), `awayCompletionHom` (31) and
`eqToHom` (25), and every one of them has a single referent that its bare name already resolves to
correctly. `mapSpf`, at 108 bare occurrences the third-largest entry in the residue, means
`CompletedTensorProduct.mapSpf` and nothing else: backlog, not shorthand. `T_inv` (62) names one
object, not a family: a longer prose variable, as the list already says.

### The standing backlog

`python3 scripts/citation_audit.py --tree` runs the same check over every comment in the tree. It
is a **measurement, not a gate**. A figure here is a measurement with a commit attached; re-run it
rather than quoting it. On `5823cac` with this document's own change applied, and with `Spf` and
`Spec` excluded as construction shorthands, it reports **1301 distinct unresolved tokens over 4296
occurrences**. Partitioned by kind — which is what tells you whether a number is a defect or a
category (issue 1442):

| | distinct | occ |
| :-- | --: | --: |
| **no spelling resolves, in any namespace** | **459** | **1181** |
| — dot-notation on a local: `I.FG` 40, `D.J` 17, `f.c` 15, `e.symm` 10 | 82 | 251 |
| — a **namespace**, which is not one of the three resolution kinds | 12 | 26 |
| — longer prose variables: `T_inv` 62, `U_n` 28, `hστ` 26, `hnode` 18 | 365 | 904 |
| **some qualified spelling resolves** | **842** | **3115** |
| — a field of a structure: `t_fac` 115, `cocycle` 74, `f_open` 29 | 49 | 535 |
| — a bare cite of a real declaration — the actual backlog | 793 | 2580 |

Three things that partition shows and a frequency histogram does not.

* **The structure-field category is a rule almost nothing obeys.** It requires the structure be
  named, qualified, in the same sentence. Over the 531 field citations whose owning structure is
  cited anywhere in the tree, the structure appears in the same sentence — under *any* spelling,
  which is the generous reading — in **102 of them, 19%**. The category is right; the tree is not
  in it.
* **`inl`, `inr`, `fst`, `snd`, `lift` are not field citations at all** (201 occurrences). They are
  bare cites of `CompletedTensorProduct.inl`/`.inr`/`.lift` and friends. A field name that is also
  a declaration name elsewhere reads as a field to a mechanical check and as a declaration to a
  reader, so counting the bucket without reading it overstates it by a quarter.
* **The passing side is not clean either.** Ninety-five distinct tokens (820 occurrences) have
  their bare name owned by two or more constants; hand-reading every one with at least five
  occurrences found **five that resolve to a declaration the prose does not mean** — `inv` 31,
  `map` 14, `Hom.mk` 12, `IsClosedImmersion` 8, `IsSeparated` 8. These are invisible to the audit
  by construction. Issue 1444 has the list and the sites.

Clearing the backlog is not a prerequisite for anything. The convention binds the diff; the
tree-wide number is there so that the backlog is a known quantity rather than a surprise.

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
