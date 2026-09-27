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
* **"The file's `open` set" means everything the file makes visible, and that includes its
  `namespace` stack.** Of the nineteen files issue 1444 gave an `AlgebraicGeometry`-headed
  spelling, **six** never `open AlgebraicGeometry` at all —
  `AffineSeparatedTopFiniteType.lean`, `OpenFormalSubscheme.lean`,
  `RelativeTopFiniteTypeBasis.lean`, `TateXGluedIso.lean`, `TopFiniteTypeHom.lean`,
  `TopFiniteTypeHomTrans.lean`. Every one of those spellings is right, and it is the enclosing
  `namespace AlgebraicGeometry` that makes it so, not an `open` line. A module docstring sits
  above the `namespace` too, and the previous bullet's argument applies verbatim: it is what the
  file declares, not where the citation sits, that binds.
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
* **The audit's open set is not any file's `open` set.** `scripts/citation_audit.py` resolves
  every token under the single fixed set listed above; it is not any file's own set and it is
  deliberately not the union of them. So the audit flags tokens that are correct where they sit.
  Bare `IsEmbedding` resolves in `FormalSchemes.CompletionTwoPatchEmbedding`, to
  `Topology.IsEmbedding`, because that file carries `open CategoryTheory Topology TopologicalSpace`
  — while under the audit's set it is an unknown identifier. The reviewer's question is never
  "does the audit flag it" but "does it resolve, to the intended declaration, **in the citing
  file**". Qualifying a token the audit flags but the file resolves is always allowed, and is
  usually right when siblings need it: the same file's neighbours
  `CompletionTwoPatchClosed.lean` and `CompletionTwoPatchSupport.lean` open no `Topology`, so there
  the bare spelling genuinely did not resolve, and a half-qualified token across sibling files is
  worse than either state. That is **consistency, not repair** — a pull request doing it should say
  which of the two it is doing, because the diff looks the same.

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
* **Name fragments** — a token carrying an **elision marker**, used to talk about a family of names
  rather than one of them: a leading `_` (`_hom_snd`, `_comp_pr₂`), which is genuinely part of the
  generated names it is the tail of, or a `…` at whichever end is elided (`…_hom_fac`,
  `…InterchangeOpenImmersion`, `bothAlgData…`, `…GlueF_…`). The `…` form needs no rule of its own —
  it is not identifier-shaped, so it is already notation. On `c16a642` the tree uses it **49
  distinct tokens over 87 occurrences**, of which **36 / 71** put the `…` first and **24 / 55** put
  it first on a CamelCase name. **Quote the regex with the count**: the population here is every
  backticked span carrying a `…` and no space or comma, which is what "a fragment of one name"
  means, and `citation_audit.py`'s own tokenizer reproduces it token for token —

  ```sh
  git grep -oh '`[^` ,]*…[^` ,]*`' -- 'FormalSchemes/*.lean' | sort -u | wc -l   # 49
  git grep -oh '`[^`]*…[^`]*`'     -- 'FormalSchemes/*.lean' | sort -u | wc -l   # 215
  ```

  The second line is the same census under the loose reading, which admits a prose ellipsis such
  as `f i₁, …, f iₙ`: **215 distinct over 338 occurrences**, four times the figure, on the same
  commit and in the same document. A `…` count without its population is not reproducible.
  **The category is about the fragment, and the marker is how the fragment is visible.** A fragment
  written without one is not in this category: bare `` `Inv` `` — **27** occurrences over 7 files
  on `07cd325`, meaning the `…Inv` family — *resolves*, to Mathlib's `Inv` class, so the audit
  blessed a wrong referent rather than reporting it. Per file: `TateShiftInv.lean` 8,
  `TateChainStructMapInv.lean` 5, `TateOverlapInversionIso.lean` 4, `TateActionInv.lean` 4,
  `TateFreenessInv.lean` 3, `TateChainInvGlue.lean` 2, `TateShift.lean` 1. Issue 1476 rewrote all
  27 to `…Inv` with that breakdown unchanged, and bare `` `Inv` `` is now absent from the tree.
  Write `…Inv`.

  **This bullet is also the worked example of the audit's fixed blind spot.** On `07cd325` the
  audit reported **26** of those 27 — it could not see the one in the *Scope* paragraph of
  `FormalSchemes.TateOverlapInversionIso`'s module docstring, hidden behind the span
  `annulusOverlapChart ≫ s = …` that wrapped across a line — and the figure this bullet used to
  publish was that 26. Issue 1482 made `BACKTICKED` cross newlines; the same script on the same
  tree now reports 27, and grep and audit agree. There is no longer a reading of this document on
  which the two instruments disagree about `Inv`.
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
* **A namespace** — `AlgebraicGeometry`, `AlgebraicGeometry.Scheme.Pullback`, `Classical`. It is
  **not** a fourth resolution kind, and the reason is measured below; it is author-named, and
  bounded: the sentence must be about the namespace, not about something in it.
* **A historical citation** — the name of a module or declaration that has been **deleted**, cited
  on purpose to record what used to exist and why it does not. It cannot be made to resolve, and
  qualifying it would be a lie. Bounded the same way the structure-field category is: **the
  sentence must say the thing is gone.** Measured (issue 1476): the deleted module
  `FormalSchemes.GlueOpenCoverFactor` (3 occurrences) and **21 deleted declaration names over 33
  occurrences**, all of them in the four issue-812 deletion paragraphs of
  `FormalSchemes.GlueOpenCoverFactorBoth`, `FormalSchemes.GlueOpenCoverFactorBothAlg`,
  `FormalSchemes.GeneralFibreProductLiftAdic` and
  `FormalSchemes.GeneralFibreProductLiftUniqueAdic`. Every one of those paragraphs says it
  outright — *"Issue 812 deleted it"*, *"That layer is gone"*, *"None of those exist any more; the
  module is gone entirely"*, *"Every mention of those names in this library is history"* — which is
  what makes the bound checkable rather than a licence.

### A source location is named by declaration, never by line

**A backticked `` `File.lean:NN` `` pointing at a file of this repository is a defect, and
`scripts/citation_audit.py` reports it.** A colon is not a Lean identifier character, so the
pointer is filed under notation and the resolution machinery never sees it; and unlike every other
non-citation shape it makes a claim that can go wrong silently. Issue 1479 removed the three
`set_option backward.isDefEq.respectTransparency false` blocks of `FormalSchemes/Gluing.lean` after
showing they were unnecessary, and `` `Gluing.lean:48` `` — cited from two other files as the
precedent for keeping one — went on pointing at a blank line, through every pull request since.
Measured on `e64d0ab` (issue 1517): five project pointers, of which three were correct and two were
wrong, and not one of the five was checked by anything.

Name the declaration, and the module in parentheses when the file is worth naming:
`` `oneChart_schemeDiagonal'_eq` (`FormalSchemes.AffineSeparatedValue`) ``. Both halves resolve, so
both are checked on every pull request, and neither moves when a line is inserted above it. If what
you must point at is a *proof step* rather than a declaration, name the enclosing declaration too,
so the audit has something to bite on.

**Mathlib line pointers are a different case and are not banned.** `Mathlib/…` is pinned by
`lean-toolchain` and `lake-manifest.json` rather than by this repository's edits, so it does not rot
between our commits. The check compares the whole path against the files this repository globs,
which is what tells `FormalSchemes/Gluing.lean` apart from
`Mathlib/AlgebraicGeometry/Gluing.lean:262-423`.

**This document is checked too, and the check reads its own use/mention markup.** A pointer written
with single backticks *cites* a location and is reported; the same token displayed inside a
``…`` span — which is how Markdown shows a backtick — is the document *naming* the defective token
rather than making a claim with it, and is not. That distinction was not invented for the check.
Measured on `c80eb53` (issue 1530): of the seven pointers this file then carried, the six that
cited a location were single-backticked and the one that displayed the token itself was the only
double-backticked one, with no exceptions either way. So the rule is read off the document rather
than imposed on it, and the escape hatch a mention needs already existed.

Markdown is scanned **whole, in both modes**, rather than through the diff. A citation is falsified
by the pull request that changes it, which is why the diff is the right population for one; a line
pointer is falsified by an edit to the file it *names*, which is nowhere near the document carrying
it, so a diff-restricted scan would be blind to the only way one ever goes wrong. It costs a regex
over three files and no build. **Only the pointer predicate crosses over into Markdown**, not
resolution: this document deliberately cites deleted names, misspellings and tokens with three
plausible spellings, none of which could resolve, and running the whole audit here would report the
document that defines the convention.

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

### Why a namespace is not a fourth resolution kind

Settled by measurement (issue 1476), on `26aed15`. A namespace is cheap to detect — `open Token in`
succeeds or it does not — and adding it to the resolution kinds is about three lines of
`scripts/citation_audit.py`. It was implemented, measured, and **rejected**.

Tree-wide it moves **14 distinct tokens over 31 occurrences** out of `UNRESOLVED`: a 1.1% dent in a
1279-token backlog. Read one at a time, of those 14 — **eight are right and six are not**:

* **The namespace is what the sentence means** (8 tokens, 20 occurrences): `AlgebraicGeometry` 11,
  `NatIso` 2, `Classical`, `Limits`, `AlgebraicGeometry.Scheme.Pullback`,
  `CompletedTensorAwayInterchange`, `FormalSpectrum.ColimitTarget`, `ThreeChartCover`.
* **A bare cite of a real declaration**: `IsEmbedding` 4 — the predicate `Topology.IsEmbedding`.
* **A name fragment**: `Right` 3 and `Left` — the elided half of `actionQuotientLeft`/`…Right` and
  of `basicOpenChartOverlapIso_inv_comp_furtherLeft`/`_furtherRight`.
* **A `private` declaration of the citing file**: `cChart`, which no `#check` from outside can
  reach. Not a namespace, and not a category this list has.
* **Two dead citations** — a declaration that does not exist:
  `AlgebraicGeometry.IsTopologicallyFiniteType` (it is `IsTopologicallyFiniteType`, at the root)
  and `CategoryTheory.Limits.Multicoequalizer` (Mathlib renamed the object to `multicoequalizer`).
  Issue **1554** has since moved the twenty-nine lemmas that populated the first of those two
  namespaces to the root as well, so that prefix now names nothing at all and `open ... in` fails
  on it outright. The measurement below is the one taken when it still resolved.

So the pass rate is 20 of 31 occurrences right and **11 wrong**, and two of the eleven are dead
citations of exactly the kind this audit exists to catch: `open ... in` succeeds for both, because a
deleted or misspelled constant can still leave a populated namespace behind. Blessing them
mechanically converts two loud failures into two silent ones, which the third check above says is
the worse outcome — the same argument that made `Spf` and `Spec` a category rather than a pass.

**A namespace is therefore an author-named category, not a resolution kind.** The author says "this
is a namespace" in the pull request body and the reader can check it, which is what `IsEmbedding`
and the two dead citations would not have survived. **Five of the six defects are fixed on the
commit that records this**; `cChart` is not, because a `private` declaration has no spelling that
resolves from outside the file that owns it. That is a sixth category if it is anything, and it
needs its own measurement before it becomes one.

### The standing backlog

`python3 scripts/citation_audit.py --tree` runs the same check over every comment in the tree. It
is a **measurement, not a gate**. A figure here is a measurement with a commit attached; re-run it
rather than quoting it. On `5823cac` with this document's own change applied, and with `Spf` and
`Spec` excluded as construction shorthands, it reports **1301 distinct unresolved tokens over 4296
occurrences**. Partitioned by kind — which is what tells you whether a number is a defect or a
category (issue 1442):

*(The partition below is that `5823cac` hand-reading and is **not** restamped: issue 1482 fixed the
tokenizer and re-measured only the top line, on `6f2e3bd`, where the same run reports 1286/4240
before the fix and **1287/4247** after — one token and seven occurrences, all of them named in the
paragraph that follows the table. The proportions the partition reports are unaffected at that
size; the absolute levels below are still `5823cac`'s.)*

| | distinct | occ |
| :-- | --: | --: |
| **no spelling resolves, in any namespace** | **459** | **1181** |
| — dot-notation on a local: `I.FG` 40, `D.J` 17, `f.c` 15, `e.symm` 10 | 82 | 251 |
| — a **namespace**, an author-named category and not a resolution kind (above) | 12 | 26 |
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
  by construction. Issue 1444 fixed all five.

  **Two more escaped that pass, one at each end of its threshold** (issue 1476). `Hom.ext'` has
  **2** occurrences, so the ≥5 filter never reached it — and one of the two sat on a line issue
  1444 itself rewrote, three lines above a proof that spells it `FormalScheme.Hom.ext'`. `Inv` has
  **26**, comfortably above the threshold, and was passed over anyway because it reads as prose:
  it is the `…Inv` name fragment, and bare it resolves to Mathlib's `Inv` class. So the sweep needs
  **no occurrence threshold**, and it has to be re-run over the added lines of one's *own* diff:
  the audit's `UNRESOLVED` list cannot drive it, because a wrong referent is by definition
  something the audit passed.

**The blind spot these figures used to carry is fixed (issue 1482), and what it was worth is worth
recording.** `BACKTICKED` was `` `[^`\n]+` ``, which cannot match a span that wraps across a line;
**617 comment lines in 196 files, 1.4%,** carry an odd number of backticks for that reason. The
loss was never the wrapped span. A wrap happens at a space and a Lean name has none, so a wrapped
span is always an *expression* — all **116** of the tree's are — and the cost was that its
unclosed backtick consumed the *next* citation's opening one, and everything after it re-paired.
Making the regex cross lines recovered **four citations** that had been invisible since they were
written (`thickeningSheaf`, `specTwoPatchSchemeι₀`, `specTwoPatchSchemeι₁` — all three resolve, and
to the declaration the prose means — and `backwardHom_awayCompletionHom`, which does not and joined
the backlog above), and lost none.

Two things that fix carries, because a newline-crossing regex is not free. A fenced code block would
otherwise be swallowed whole — its three opening backticks would pair with whatever came next — so
fences are stripped; no loss, the 8 spans inside fences were all excluded anyway. And a stray
backtick now re-pairs a whole *comment* rather than one line, so the audit reports the malformed
comment itself. **A malformed span comes in two classes and it takes two checks** — issue 1482
fixed one prose defect of each class in the same commit, which is how they came to be recorded as
one, and issues 1501 and 1503 separated them:

* **unbalanced fragments** — an **odd** backtick count: a missing closer. There was exactly **one**
  on `6f2e3bd`, in `IndSchemeLimitComponents.lean`, worth five citations out of a 68-line
  docstring. The report names the line the stray backtick is on — the first line from which the
  running parity is odd and stays odd, `:35` there, not the comment's own first line `:6`.
* **nested spans** — a run of two or more **adjacent** backticks, which is what a citation nested
  inside another leaves behind. The count stays **even**, so parity never sees it, while the outer
  span closes at the inner one's opener and the rest of the comment reads as the wrong text:

  ```
  /-- The `R`-algebra map `A →ₐ[R] A[x⁻¹]^∧`, `a ↦ x⁻¹-inversion of `locX (flip a)``: the second leg
  of the `x`-side graph codiagonal (`graphCodiagX_inr`). -/
  ```

  Twelve backticks, and it cost `graphCodiagX_inr` and `x`. It was found by **diffing the old and
  new token maps**, not by any check, and lived in `TateGraphCodiagonalXLift.lean` for two weeks
  with no signal at all. Lean comments have no double-backtick convention, so the tree-wide
  baseline is **0** and a run of them is always this defect or a typo.

Against `6f2e3bd` each check reports exactly its own defect and nothing else; against `1b1d684`
both report **0**, and **that pair of zeros is the state to keep the tree in** — a single number
never was the invariant. Both run under `--diff` as well as `--tree`, and they are not worth the
same there. A hunk is an arbitrary slice, so a span opened on an *unchanged* line leaves the added
text odd with nothing wrong: over the **712** added hunks of the last **60** commits on `master`
that happened **once**, and that once was benign. So `--diff` prints unbalanced as advisory and
fails only on nested spans, which a slice can hide but not invent. Both of the known defects would
have been reported at the commit that introduced them — the missing closer by parity at `9813e4d`,
the nested pair by adjacency at `bbfc9da` — because both arrived in a new file, where the hunk is
the whole file. `--selftest` covers both checks and every case the tokenizer used to
get wrong, and needs no build.

Nothing in `.github/workflows/` runs `scripts/citation_audit.py`. It is an instrument an author
runs by hand under this convention, not a gate, so **the printed lines are the signal, not the exit
status**: `--tree` returns 1 on the standing backlog alone and will while the backlog is non-empty.

**Run it after a full build, and know what a report made before one looks like.** Almost every
line of the report is read off the sources and is right whether or not the tree is built; the only
ones the probe can touch are the `resolves as declaration` and `UNRESOLVED` counts, which sit in
the middle of the count block and trade off against each other, and the per-token list below them.
A probe whose `import FormalSchemes` fails puts its one error on line 1, where no token lives, so
every token used to be counted as resolving. **A report whose population and excluded categories
look right and whose `UNRESOLVED` is `0` is exactly what a broken probe produced** — three
sessions re-derived that independently and one shipped the zero in a pull-request body before the
script learned to refuse (issue 2099). It now exits **2** and names the cause instead of
answering; exit 1 still means it measured the tree and found something. When you quote a `0` here,
quote the positive control beside it — a token you know does not exist must come back UNRESOLVED.

**A stale `.lake` is not the same failure, and it is the nastier one** (issue 2109). `lake env
lean` hands the probe whatever oleans are on disk and does not check them against the working
tree, so on a checkout whose `.lake` was built from another branch the probe answers fluently
about *those* sources while the population beside it is read off *these* ones — producing a
plausible non-zero `UNRESOLVED` that no signature distinguishes from a true one, where an unbuilt
tree at least produced a recognisable `0`. The script now refuses that too, by name: it gates the
probe on `lake build --no-build FormalSchemes` — the library the probe imports — and, when a
target is out of date, prints the modules `lake` named and **exits 2 without printing a report**.
Two seconds, and it builds nothing. So exit **2** means *this run measured nothing*, in either of
its two ways and with the same remedy (run a full `lake build`); the sentence that follows the
message says which happened.

Clearing the backlog is not a prerequisite for anything. The convention binds the diff; the
tree-wide number is there so that the backlog is a known quantity rather than a surprise.

### Two traps that have cost this tree real work

* **`glue_condition_apply` cannot be found by grep.** It is generated by `@[elementwise]` on
  `CategoryTheory.GlueData.glue_condition`, so no `theorem glue_condition_apply` line exists in
  Mathlib, and the namespace its call sites suggest (`TopCat.GlueData`) is not the one it resolves
  under. Resolve names by `#check`, never by grep.
* **`git grep -nw` returns zero hits, silently, for any name ending in `₀`/`₁`.** U+2080 and
  U+2081 are Unicode category `No` and form no word boundary. Use bare-string greps.

## The closure-figure convention

**A closure figure quoted in a comment is a measurement, and it must be the measurement the
`import` lines give at the commit that carries it.** `## Placement` paragraphs all over this tree
argue for a home by comparing import costs, and the numbers in those arguments are checked by
nothing: the sentence compiles whatever they say, every name in it resolves, and
`scripts/citation_audit.py` looks at the names.

The figures rot in a way no diff can show. A **reverse** closure is invalidated by a leaf added
anywhere above the module, in a pull request that touches neither the file carrying the sentence
nor any file that sentence is about — so the number goes wrong with nothing in that pull request,
or any later one, able to see it. **Forward closures rot too**, more slowly: a module's forward
closure grows when a module it already imports gains an import, which is likewise not in its own
diff. Both had happened here before the checker existed: the reverse figures of sixteen files were
stale, and one file's forward figure was.

### The audit

From the repository root; no build needed, since it reads `import` lines:

```sh
python3 scripts/closure_audit.py --tree
python3 scripts/closure_audit.py --sweep
```

Run it beside `scripts/citation_audit.py`, at the same point and for the same reason. **Neither is
run by `.github/workflows/` or by `.orchestra/validation.sh`**, and this one is deliberately not
added to either: it is an author's instrument like the other, and a gate on a figure that a
*different* pull request can falsify would fail branches that changed nothing. Unlike the citation
audit it has no standing backlog, so `--tree` returning 0 is the state to keep the tree in, and a
non-zero exit is a defect rather than a level.

The conventions it implements are the ones the tree's own paragraphs state: the walk is over the
files under `FormalSchemes/`, `FormalSchemes.lean` at the repository root is outside it, a module
is not counted in its own closure, and `public import` is an import line. Where a paragraph counts
the other way it says so — *"(N counted with itself)"* — and that spelling is checked as well, at
one more.

**The script reads the tree at the current working directory, not the directory it is in.**
`python3 /tmp/base/scripts/closure_audit.py --tree`, run from the repository, audits *the
repository*, with only the script taken from the worktree, and prints nothing that says which tree
it walked. To measure a base, `cd` into the worktree first. A base measurement is only a base
measurement if you can say which tree produced it.

### What adding a module costs, and why the figures are repaired rather than anchored

**An absolute closure figure is a global invariant of the tree, so a pull request that adds a
module falsifies figures in files it does not touch.** The figures in this subsection are one
measurement at one commit — `db41d27`, where `--tree` is clean at 559 modules — and are not
maintained; re-run the experiment rather than quoting them. One new leaf, importing a single
existing module and touching no declaration, took `--tree` from 0 MISMATCH to **43**, across **27
sentences** in **23 files**, of exactly two shapes and no third:

| shape | count | why |
| --- | --: | --- |
| *"of the project's **N** modules"* | 16 | a new module falsifies every project total |
| *"the reverse closure of `X` is **N**"* | 27 | a leaf is downstream of most of the tree |

**A leaf leaves every forward closure alone** — a module added downstream changes nobody's imports
— and a pull request that adds only declarations changes nothing at all, measured at 0 MISMATCH.

**`closure_audit.py --edge A:B` prices a hypothetical import mechanically**, and is what to run
before writing any of the figures this subsection is about. It reports the modules the edge brings
in, which forward closures move and **which do not**, which reverse closures move, and the
`MISMATCH` population the edge would create, partitioned by the three species an import can
falsify. It reads a tree that does not exist, so it never fails and is not a gate. It does not read
the counterfactual sentence — comparing the report against what a paragraph says is yours to do,
exactly as with `--sweep`.

**`closure_audit.py --stub NAME:A,B` prices a hypothetical *module*, which is the experiment of the
paragraph above run rather than described.** It copies the tree, writes the stub into the copy as
its import lines and nothing else, audits both trees, and reports the difference — so the price
excludes whatever the tree was already red about, and nothing is written under the repository on any
exit path. It names the imports explicitly, because *a module over this one* and *a module repeating
this one's imports* are different questions with different answers, over file lists that can be
identical. Two species and no third, which is this subsection's own table: a project total or tree
census, and a reverse closure of a module the stub reaches. A stub is a leaf, so no forward closure
can move and no file's size changes; a claim landing outside those two is reported as
`unclassified`, which is never a level. **A tree census is in that first species and `--edge`'s
population deliberately has no census in it, and the asymmetry is about which species can name the
figure rather than about which hypothetical moves it.** Both move it — an import changes what
reaches what, which is what a census partitions by, and `--edge
FormalSchemes.AdicRing:FormalSchemes.AwayCompletionUniversal` moves nine census figures, a count
`edge_cost`'s own comment carries so the cap is not silent. What differs is where the figure would
go: `--edge`'s three species are exhaustive for *closures* and a bucket is not one, so pricing it
would print it as `unclassified`, which is false advice about a figure `--tree` already checks,
while `--stub`'s first species fits a census exactly — a stub grows `len(mods)` and a census's
universe is a count of modules, so it moves for the same reason the project total does. So a
module's price includes every census figure it falsifies, and since issue 2227 it does; an
import's names none. A hypothetical-module price you find quoted in a docstring and cannot
reproduce is worth checking against that date before assuming the walk moved.

**The rebuild beside that price has four readings, and the report prints all four rather than
picking one silently.** Whether a repaired file counts as re-elaborating *itself*, and whether the
stub — which is on the tree the repairs are made in, but which no repair edits — is inside the
answer, are independent choices; one sentence of this tree has been published with three different
union figures by three different sessions, none of whom had miswalked anything. The largest single
contributor is named with the union that drops it, which is the arithmetic the paragraph above does
by hand. The report also prints the count of **figures** beside the count of distinct **positions**,
which differ whenever one sentence carries two. **Quote the convention with the figure, or quote the
report.**

**An added *import* is the other case, and its cost is not the importing file's reverse closure.**
What an import `A → B` moves is the forward closure of `A` and of everything downstream of `A`, and
the reverse closure of every module that `B` newly brings into `A`'s closure — so what it costs is
the size of that new part, not the size of `A`'s consumer set. Both extremes were measured on one
file whose reverse closure is 0: importing a module whose own closure was already inside it moved
**one** figure, `A`'s forward closure, and cost **2** MISMATCHes because two files state that
figure; importing one that brought a fresh subtree cost **17**, across 12 files. *"Reverse closure
0, so an import is free"* is not the rule, and neither is *"one import, one figure"*.

**The repair is mechanical — `+1` on a numeral — and the cost is the rebuild, which is concentrated
in one file.** Editing a docstring re-elaborates that module's reverse closure; over the 23 files
above the union of those is **504** modules, of which **502** are
`FormalSchemes/StructureSheaf.lean` alone. Drop that one file and the same repair rebuilds **51**.

That is what decides the disposition, and it rules out the option that looks best:

* **Dropping the project totals** — one sentence here, and *"of the project's modules"* with no
  numeral in the docstrings — removes 16 of the 43 figures and 5 of the 23 files, and **0 of the
  504 rebuilt modules**. `FormalSchemes/StructureSheaf.lean` states a project total *and* its own
  reverse closure in one sentence, so it is edited either way. Halving the count is not halving
  the cost, and the cost is what the argument is about.
* **Anchoring the figures** — *"**559** modules at `db41d27`"*, the spelling `README.md` uses —
  would stop them rotting at the price of the checking that four rows were spent building, and no
  `.lean` docstring on this tree quotes a commit.
* **So the figures are repaired, and this is the obligation**: adding a module under
  `FormalSchemes/` includes running `--tree` and repairing what it reports, and that repair may cost
  a near-full rebuild on top of the build the module itself needs. Do the repairs **before** the
  final build, not after. It is deliberately not in `.orchestra/validation.sh`, for the reason the
  subsection above gives.

**What the measurement does point at is placement, not spelling.** A project total or an absolute
*reverse* closure written into a file with a large reverse closure is the expensive kind of figure:
it will be repaired by somebody who is not you, and their rebuild is your file's consumer set.
Where the argument allows it, put such a figure in a file that is cheap to re-elaborate, and prefer
a **forward** closure, which no added leaf can falsify.

### Which module a figure is about, and when the checker declines to guess

A figure in file `A` is often about `A`, but a `## Placement` paragraph also quotes the closures of
the modules it is choosing between, so neither "the file it is in" nor "the module named nearest"
is right on its own. The script's docstring states the rule it uses; what matters when writing
prose is that **a figure whose subject the rule cannot pin down is reported as declined and left
unchecked**, so an unattributable sentence silently loses its guarantee.

Two spellings are worth preferring for that reason alone, since both are checked:

* name the module — `` `FormalSchemes.Foo`'s reverse closure is **N** ``, or *"the reverse closure
  of `` `FormalSchemes.Foo` `` is **N** modules"* — rather than writing *"its reverse closure"*. A
  bare possessive pronoun is the anaphor the checker resolves least: it takes one shape only,
  a pronoun in a later coordinate of a conjunction whose *immediately preceding* coordinate names
  exactly one subject, as in *"this file's forward closure stays **93**, its reverse closure is
  **3**"*. Everywhere else it declines, because twice on this tree the antecedent was the
  paragraph's subject while the last module actually named was a different one mentioned in
  passing. A pronoun that opens its own sentence, or that reaches back past one coordinate, or
  that sits after a coordinate naming two modules, is still unchecked (row 2072);
* refer back by **name or by *that file***, never by a definite description. *That file*, *that
  module* and *whose* are resolved, to the nearest module named before them; *the first*, *the
  former* and *the latter* are not anchors at all, so the figure falls through to whatever module
  was last named, which is exactly the one the description was written to avoid repeating.
  *"…in the forward closure of the first, whose own forward closure is **267**"* was attributed to
  a module named three clauses earlier, and reported as a MISMATCH twice (row 1840);
* keep a companion figure in the same sentence as the claim it belongs to: *"against this file's
  M"*, *"K before this file"* and *"(J counted with itself)"* are all checked against the same walk,
  and all three have been wrong on this tree. A **project total** used to be read that way too and
  is not any more — it has no subject, so it needs no host claim and is checked wherever it stands
  (row 2209); what it needs instead is the spelling below.

A figure spelled in words is invisible to it. *"The reverse closure of `FormalSchemes.Foo` is the
two consumers and nothing else"* was **five** modules by then and no check could say so; write the
numeral.

**A closure phrase with no numeral is counted as `declined`, so prose refactoring moves the coverage
figure without touching a number.** Splitting one such sentence into three took the declined count
from 10 to 12; rewriting the paragraph so that each closure phrase sits beside its own figure took
it to 9 and moved those figures into *attributed* instead. So **re-run `--tree` after any prose edit
that touches a closure word, not only after one that touches a numeral** — and compare the declined
*lines*, not the counts. A set that changes while the count holds is the failure that comparison
catches, and a line number that moves because the file grew above it is not a change at all.

**And write the words `forward closure` or `reverse closure`, because that phrase is what the
checker looks for.** The same measurement has been spelled on this tree as *"the import closure of
this leaf is 82 project modules"*, *"whose import closure of 25 modules"*, *"this leaf's transitive
closure"*, *"adding it takes a closure of 35 to one of 45"* and — inverted — *"this file is in the
import closure of 445 of the library's 496 modules"*, which is a **reverse** closure written from
the far end. Such a sentence carries numerals and is not reported as declined either: it is
invisible, which is worse than unattributed, since a declined claim is at least counted. Two greps
— `import closure of` and `closure of N` — find **eight** such sentences in five files, of which
**two were wrong**: one by a module, and one that said *"this file is in the import closure of
**445** of the library's **496** modules"* where the walk gave both figures larger. Row 1825
rewrote the four that state a plain measurement into the checked spelling and left four deltas; the
repaired form of the second is in `FormalSchemes/StructureSheaf.lean`, where `--tree` now checks
both of its figures. Read the true pair there and not here: it is live, and this file is outside
the walk, as the paragraph below says. **Quote the two false figures, never the difference between
them.** *"Wrong by 56 in its figure and 62 in its total"* is itself a measurement, it names no
module and carries no closure phrase so no sweep can see it, and repairing the sentence it
describes silently falsifies it — as happened here, where it read 55 and 61 until a merge moved the
true figures.
**Those two greps are not the population**, and the section below is what a sweep finds instead.

**The noun beside the figure is a measurement too.** Call a module a **leaf** only where a walk you
ran gives it reverse closure 0; open a `## Placement` paragraph with *"Over `FormalSchemes.Foo` and
`FormalSchemes.Bar`:"*, which carries the only fact the opener needs and asserts nothing a later
module can falsify, and write *"this file's closure"* rather than *"this leaf's"*. **`Mathlib-only
leaf` is the opposite sense — *forward* closure 0 — and is unaffected**:
`FormalSchemes.LocallyRingedSpaceRange` is one, correctly, and its **reverse** closure is in the
hundreds. **This file is outside the audit's walk**, which covers `FormalSchemes/` only, so a live
figure quoted here is checked by nothing and rots unread: the figure that stood in this sentence
was stale by a module when row 1841 read it. Quote here only what cannot rot — a false figure, or
one anchored to a commit — and leave the live figure in the module, where `--tree` checks it.

**Half of that noun is checked and half is convention, and the halves are worth telling apart.**
Where a sentence carries a closure figure *and* calls the file it is in a leaf — a `## Placement`
opener, or *"against this leaf's 13"* — `closure_audit.py` reads the noun as the claim *reverse
closure 0* and checks it against the same walk, once per sentence; that costs no coverage, because
only sentences that already carry a figure are read and nothing new is declined. What it cannot
see is the positional noun about **another** module, as in *"`FormalSchemes.TateSeparated`, a Tate
leaf that nothing outside the Tate cluster can cite"*: there is no figure in that sentence to hang
the check on, and the file carrying it has no reason ever to re-measure the module it names, which
is why `TateSeparated` had picked up **67** consumers by the time anyone looked, and more since.
Say *"a Tate-cluster module"*, or name the figure and bring the sentence under the check.

### The spellings the checker cannot read, and `--sweep`

Those two greps are keyed on the preposition, and three further spellings do without it:
*"its import closure is 214 modules"*, with none at all; *"a 31-module transitive import closure"*,
with the numeral before the noun; and *"`FormalSchemes.Gluing` being upstream of 272 of this tree's
496 modules"*, a **reverse** closure written with neither the word `reverse` nor a preposition to
key on — and carrying the same stale project total that row 1825 had just repaired elsewhere.
Sweeping for every sentence that pairs a numeral with the word `closure`, with a project-module
total or with *upstream of N* reports all three. Row 1832 read that population and found **twelve**
wrong sentences in eleven files carrying **twenty** wrong numerals, against the two the greps
found: one project total stale by 62, one reverse closure stale by 32.

**A project total is the one figure here with no subject, and it has its own spelling rule: pin the
count to the tree, and let the noun phrase end there.** Write *"N of this tree's **T** modules"* —
`the project's` and `the library's` read the same — or *"N of the **T** modules under
`FormalSchemes/`"*, and `--tree` checks the **T** wherever in the file it stands. A phrase with
nothing pinning it to the whole tree is **not** checked and goes to `--sweep` instead — *"N of the
**T** modules"* on its own, *"over the **T** modules under it"*, *"the **T** modules under
`FormalSchemes/Tate`"* — because *"**2** of the **5** modules that import it"* is the same words
about a subset, and a checker that read its **5** as the project total would report a MISMATCH
against correct prose, which is worse than the gap.

**The second half of the rule is the one worth reading twice: a pin in front of the phrase is undone
by anything hung on the back of it.** *"the **T** modules under `FormalSchemes/` that import
`Foo`"*, *"…`FormalSchemes/` importing `Foo`"*, *"…`FormalSchemes/` repaired by row 2207"* and
*"…`FormalSchemes/` with a redundant import"* are all subsets in the same words as the total —
relative clause, present participle, past participle, preposition — and all four are refused and
swept instead. So **if what you mean is the total, let a finite verb or a full stop follow the
path**: *"…under `FormalSchemes/` **carry** an import"* is checked, and so is an anchor, *"…under
`FormalSchemes/` **at** that commit"*, because `at`, `of`, `by`, `for`, `to`, `on`, `as`, `from` and
`in` are deliberately outside the guard.

**And if `--tree` reports a MISMATCH on a total that you know is right, do not touch the numeral.**
This is the one species with no way to decline a figure by name, and that is deliberate — every
other decline here is the script refusing an ambiguous subject, and an author-written opt-out would
be the first place a stale figure could hide, in the species that exists because three of them hid.
What you have instead is the shape: post-modify the phrase (*"that"*, *"which"*, a participle,
*"with"*) and the sentence goes to the reading list with its numeral intact. Two shapes need that
edit rather than being refused already, because nothing separates them from a finite verb — an
adjective phrase, *"…under `FormalSchemes/` reachable from it"*, and a bare relative, *"…under
`FormalSchemes/` `Foo` imports"*. Inserting *that* or *that are* is the whole repair, and `--tree`
prints it under any total MISMATCH it reports.

**The pinned spelling is the fourth one this section owes to a real defect, and it was found the
expensive way**: it was invisible to `--tree` *and* to `--sweep` until row 2209, and
`FormalSchemes/RefinedOverlapTransition.lean` had three numerals go stale behind it inside one
paragraph while `--tree` reported MISMATCH 0 — one of them in a sentence with no closure phrase in
it at all, which is why the total cannot be read as a companion of a claim. The unpinned half of
that paragraph is still unpinned, deliberately: it is on the reading list, which is where a sentence
a checker cannot read belongs.

**A tree *census* is the fifth spelling this section owes to a defect, and it is the one that hides
best: the noun of the count phrase is elided, so there is nothing for any grammar to pin.** A census
is a partition of the module set written with no closure phrase in it — *"the best any of the other
**T−1** does is three: **A** reach none, **B** reach exactly one and **C** reach two"*, *"this
module is the only one of the **T** that reaches all three"*. The figures are written as letters
throughout this entry — **T** for the tree's module count, **A** to **D** for the buckets — because
this file is outside every instrument's walk, so a real numeral copied into it is a figure nothing
will ever re-check. Every numeral in one moves
when a module is added, and the *reach none* bucket and the two totals move while the others do
not, so **you cannot repair a census by adding one to every numeral in it**. Row 2207 falsified
seven of them in one paragraph with `--tree` reporting MISMATCH 0 and `--sweep` silent, which is
how this entry was paid for. Since row 2214 `--sweep` lists a census sentence that carries *the
other **N***, *the only one of the **N*** or an *N reach* bucket predicate that row 2224's species
does not read — a bare list of buckets (*"**A′** / **B′** / **C′** / **D** under the other
convention"*) still reaches the list only if something else in the sentence is a marker — and
`--tree` checks exactly one census spelling: *"the
only one of the **T** modules under `FormalSchemes/`"*, where naming the path says which set the
**T** counts. **Write that one if you want the figure checked.** *"the other **N**"* is
never checked as a **total**, because *the other* needs an antecedent for what is excluded and no
grammar has it — *"the other **T−6** modules under `FormalSchemes/`"* excluding a named six is the
same words as the whole tree less this file. **A census MISMATCH prints its own remedy and it is
not the total's**: post-modifying the noun phrase is what makes a *total* refuse and does nothing at
all to a census, so what sends a census total to `--sweep` is eliding the noun or naming the subset.

**Since row 2224 the *buckets* are checked, and what makes that possible is that a census spells its
own subject set's cardinality in words.** *"reaches all six of the above"* resolves to six module
tokens or the reading is refused, and no other figure in this tree states the answer to the question
its resolver is asking — which is why this is the one species here whose remedy is *change the
numeral*. So write a census like this and every numeral in it is checked:

- **name the set**, in the sentence itself or in the `## Placement` opener immediately before it and
  before that opener's colon, and **spell how many** — *"reaches all six of the above"*. The count
  and the modules named have to agree or the census declines;
- **name the set being partitioned**, as *"the other **N**"* (every module but this one) or *"the
  only one of the **N**"* (all of them), and not both. Here the **N** *is* checked, against the
  walk — the census reading is a different use of the same words from the total reading above, and
  it is available only because the subject set has already resolved;
- **word each bucket** as *"**A** reach none"*, *"**B** reach exactly one"*, *"**C** reach two"*.
  The predicate is read, so a bucket with a numeral and no readable index declines;
- **name every bucket you do not give a numeral to**, in words — *"and this file is the one that
  reaches three"*. The remainder is read off the walk rather than inferred from the shortfall, so a
  bucket the sentence names nowhere is a MISMATCH, which is the failure a sum rule cannot see;
- write *"this module is the only one of the **N**"* and the member of the top bucket is checked
  **by name**, not just its count — two figures, one saying this file is in that bucket and one
  saying nothing else is, and the second names what the walk found. *This module* has to be what
  the claim is **made of** and not merely present earlier in the sentence: *"this file is a leaf,
  and `FormalSchemes.X` is the only one of the **N**"* is a claim about `X`, and the species reads
  it as one, because whether a **named** module is the only one is a question no walk here answers.

**Which of the first bullet's two ways you name the set decides what happens when you repair an
identity, and one of them silently stops the census being checked.** A stale *"this module is the
only one of the **N**"* prints two remedies and the first is *say it of the module the walk gives* —
so you write the rival's name into the sentence, which adds a module token to it. If the set was
named **one sentence back**, before the opener's colon, the census's own sentence now names one
module against a spelled count of six, the hop still names six, the checksum still resolves and the
buckets, the universe and the remainder stay checked. If the set was named **in the census's own
sentence**, that sentence now names seven against a spelled six, nothing resolves, and the **whole
census declines** — green, with the reason printed, and no longer read. Both are safe and neither
can go red on correct prose; the difference is only whether you still have the check afterwards. So
prefer the opener for a census you also make an identity claim in, and if you take the decline,
re-spell the cardinality to match rather than leaving it. `--selftest` pins both halves on a tree
that is genuinely red before the repair.

A census stating the strict convention for its own buckets — not counting a module as reaching
itself — declines, because accepting both readings silently would give a stale figure two ways to
look right. The default is the self-counting one: a declaration placed in a file has that file's own
contents. Anything the four gates refuse is printed in `--tree`'s `census-declined` block with the
reason, which is where a census the buckets species cannot read is now read; `--sweep` no longer
carries it, so there is one reading list per figure and not two.

Extending `CLOSURE` to those spellings was considered and declined twice, and the reason is not
cost: *"the closure of `A` is N"* and *"`A` is in the closure of N"* are **opposite** claims in
nearly the same words, so a second grammar would have to carry the direction, and getting that
wrong turns a silent gap into confident mis-measurement. `--sweep` **counts** them instead. It
lists every sentence that carries a numeral together with the word `closure`, a project-module
total, a tree census or *upstream of N*, and that `--tree` neither attributes nor declines; `--tree`
prints the count in its header and never fails on it. Sentences naming Mathlib are left out — they
measure a graph this script does not walk.

**That exclusion is deliberately over-wide, and it has already cost a figure.** Nine sentences name
Mathlib; eight of them are genuinely about Mathlib's import graph, and the ninth,
`FormalSchemes/LocallyRingedSpaceRange.lean`'s *"the intersection is 27 modules"*, is an
intersection of **project** closures excluded only because the same sentence ends *"so the file
sits directly on Mathlib"*. It had gone stale by a module and was repaired on row 1841. The
exclusion stays — a filter narrow enough to keep the other eight out is more grammar than one
over-exclusion is worth — but the class it hides is *a project figure in a sentence that also
mentions Mathlib*, and nothing checks that class.

**Most of what `--sweep` reports is out of reach, and one class in it is not.** Deltas,
intersections of several import closures, peak-RSS figures and numerals that are issue numbers are
checked by no walk this script runs, and that is why the list does not fail a run. But **one
endpoint of every delta is a measurement of the tree as it stands** — *"importing it would take
this file's closure from 48 modules to 93"* says the closure is 48 **now** — and **six** of row
1832's twelve sentences were exactly that shape, wrong in the endpoint that is not counterfactual
while looking unfalsifiable because of the endpoint that is. (The counterfactual endpoint is not
beyond reach either: it is the closure of the union with the module being priced, and two of the
six were stale in that figure as well. `--sweep` does not compute it, and nor does `--tree`; it is
a ten-line walk, and row 1841 ran it over every delta the sweep still reports and found all of them
right, near endpoint and far.) If a figure `--sweep` reports is a plain measurement of this tree,
rewrite it in the checked spelling rather than leaving it for the next sweep.

**A counterfactual price — *"N figure repairs in M files"* — is on that list too, and it is the one
shape there whose remedy is not a rewrite.** Its subject is a tree that does not exist, so no
species can check it and none will; what it wants is a human re-running `--edge` or `--stub` and
dating what they write. It is swept by its own marker rather than by accident, which is the
difference this entry records: before that, such a sentence was listed only when something else in
it happened to carry a closure word or a project total, and one of them was hidden outright by the
closure claim standing beside it — the figure invisible because of the claim, which is the mechanism
the paragraph about row 2209 above is written over.

## The `set_option` cross-reference convention

Every `set_option` here is justified in an adjacent comment, and many of those comments are
cross-references — *"Same transparency requirement as `completion_glue_condition`, for the same
reason"*, *"the same accommodation `ThickeningCocone.lean` makes"*. **That sentence is a claim
about the declaration or module it names, not about the file it sits in**, so the edit that
falsifies it is a refactor somewhere else that removes the option, and nothing in a build can
notice: removing an option cannot fail an elaboration. `python3 scripts/option_reference_audit.py
--tree` checks each such sentence against the options its anchor still carries — by English word,
so *"transparency"* about a declaration that only raises `maxHeartbeats` is a `MISMATCH` — and
`--selftest` checks the reading rules against canned sources with no build. **A pull request that
removes a `set_option` must run it**; one that only adds declarations need not.

Like the other two it is **not** run by `.github/workflows/` or by `.orchestra/validation.sh`, and
for the same reason: it is an author's instrument, and a sentence a *different* pull request
falsified is not this branch's defect. It reads the tree at the current working directory, not the
directory the script is in. It had a standing backlog of **2** at `0c91a57`, both filed as issue
2123 and repaired by #747, so `--tree` returned 1 there; at `8acc6b7` the backlog is **0** and it
returns 0. Those are measurements with commits attached rather than a figure about the tree today
(issue 2128); the number moving is the signal, as with the citation audit.

## The two spaces `D(g) ⊆ D(f)` names

`D(g) ⊆ D(f)` is written on this tree for two containments that are **not** equivalent, and a
sentence that does not say which one it means is ambiguous however true it is.

* **In `Spec R`.** `D(g) ⊆ D(f)` ⟺ `g ∈ √(f)` ⟺ `IsUnit (algebraMap R (Localization.Away g) f)`.
  This is the hypothesis almost every declaration here actually takes; grep it as
  `IsUnit (algebraMap … (Localization.Away …) …)`.
* **In `Spf (R, I)`.** `FormalSpectrum.basicOpen I f` is the basic open of the residue `f mod I` in
  `Spec (R ⧸ I)`, so `FormalSpectrum.basicOpen I g ≤ FormalSpectrum.basicOpen I f` says only
  `ḡ ∈ √(f̄)` in `R ⧸ I`. It gives `g ^ n - f * a ∈ I`
  (`FormalSpectrum.exists_pow_sub_mul_mem_of_basicOpen_le`) and **no unit in `Localization.Away g`
  at all**. `FormalSchemes.AwayCompletionRestrict`'s opening paragraph is the exposition, and
  `FormalSpectrum.awayCompletionRestrict` is the map keyed on this weaker hypothesis — it exists
  because the unit is unavailable.

The second is strictly weaker, and the separation is witnessed rather than argued: at `R = ℤ`,
`I = (2)`, `f = 3`, `g = 5`, `Spf` is the single point `Spec 𝔽₂`, so `D(5) ≤ D(3)` holds there
while `3` is not a unit in `ℤ[1/5]` (map to `ZMod 3`). Both halves elaborate; issue 2188 carries
the two `example`s.

**The rule.** Whenever a sentence *identifies* the containment with the unit — *"encoded as"*,
*"encoded by"*, *"i.e."*, *"↔"*, *"is exactly"* — name the space in the same sentence. Write
`D(g) ⊆ D(f)` **in `Spec R`** for the unit and spell the other one out as
`FormalSpectrum.basicOpen I g ≤ FormalSpectrum.basicOpen I f`, or say *"the basic opens of
`Spf (R, I)`"*. A sentence that only asserts the implication — *"the unit makes `D(g)` a basic open
contained in `D(f)`"* — is sound without the gloss and needs no repair; it is the biconditional
that has to carry its space. `FormalSchemes.AdicCompletionAwayTrans`'s opening two paragraphs are
the model: they write both containments, both with their space, and say which is stronger.

**This is not a style preference.** PR #779 §4 handed its successor an unpriced step built on the
gloss — getting a unit out of a containment of basic opens of `Spf` — and PR #781 §1 spent a whole
pull request establishing that there is no such step, because the map keyed on the containment
alone already existed. Issue 2188 is the census and the site-by-site ruling; it found **135**
occurrences in **32** files and condemned **10** files, and it records that a line-oriented
`git grep "encoded as\|encoded by"` misses two of the seven `encoded` sites because the phrase
wraps.

**No instrument checks this.** `closure_audit.py` reads closure figures, `citation_audit.py` reads
backticked tokens, and neither reads a space. `scripts/` has no scanner for it and issue 2188
declined to add one: the ruling is per site and needs a reader.

## Line width

Every line of every tracked file is at most **100 characters and 100 display columns** — two
separate limits, since a line of subscripts and arrows can satisfy one and fail the other. Measure
with Python (`len` for the first, `unicodedata.east_asian_width` with combining marks at zero for
the second). `awk`'s `length()` counts bytes and over-reports on any line with a non-ASCII
character.

**Markdown is inside the rule**, and a wide table row is not a defence: keep the cells short, and
put a description that will not fit in a cell into a list instead. Every tracked `.md` file meets
both limits, tables included.

**Two tracked files are exempt and they are the whole of the exemption**, because neither can be
wrapped without changing what it means to whatever reads it:

* `.orchestra/config.json` — a JSON string value written on one line; JSON has no continuation
  inside a string literal.
* `.github/workflows/update.yml` — a commented-out `cron:` stanza whose trailing comment carries a
  documentation URL that is by itself longer than the limit.

Neither is prose this project writes, and both are named here so that a re-measurement finds them
already accounted for rather than as new defects.

**`linter.style.longLine` enforces the character half of this rule**, reached through the
lakefile's `weak.linter.mathlibStandardSet`: on the `.lean` sources the library elaborates, a line
of 101 characters is a warning, and `lake build --wfail` — the last step of
`.orchestra/validation.sh` — makes it a failure. It counts characters and not display columns, so
a line of 67 characters and 127 columns builds clean, and it exempts a line containing `http` and
an `import` line. Its scope is the library, so re-measure over `git ls-files` rather than trusting
this section — an unenforced rule rots, and this one did: it was written without a scope, against
a tree that already broke it. `scripts/reflow_widow_scan.py` does measure a width elsewhere, and
it is not this limit: a *fill* width of **99**, in `.lean` files through its two modes and in its
own `.py` module docstring through `--selftest`, which exits 1 when that docstring strands a word
or holds a short line in a paragraph's middle, which is issue 2236's stub species.

`lake env lean <file>` does **not** apply the lakefile's `leanOptions`, so it runs neither
`linter.style.longLine` nor the `show`-vs-`change` linter. Iterate with it if you like, but finish
on `lake build`, and re-measure after **every** rewrap.
