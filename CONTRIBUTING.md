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
  `CompletionTwoPatchEmbedding.lean:108` is `open CategoryTheory Topology TopologicalSpace`, so
  bare `IsEmbedding` resolves in that file, to `Topology.IsEmbedding`, while under the audit's set
  it is an unknown identifier. The reviewer's question is never "does the audit flag it" but "does
  it resolve, to the intended declaration, **in the citing file**". Qualifying a token the audit
  flags but the file resolves is always allowed, and is usually right when siblings need it: the
  same file's neighbours `CompletionTwoPatchClosed.lean` and `CompletionTwoPatchSupport.lean` open
  no `Topology`, so there the bare spelling genuinely did not resolve, and a half-qualified token
  across sibling files is worse than either state. That is **consistency, not repair** — a pull
  request doing it should say which of the two it is doing, because the diff looks the same.

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
  audit reported **26** of those 27 — it could not see the one at `TateOverlapInversionIso.lean:47`,
  whose backticked span wrapped across a line — and the figure this bullet used to publish was
  that 26. Issue 1482 made `BACKTICKED` cross newlines; the same script on the same tree now
  reports 27, and grep and audit agree. There is no longer a reading of this document on which
  the two instruments disagree about `Inv`.
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
  `GlueOpenCoverFactorBoth.lean:28-34`, `GlueOpenCoverFactorBothAlg.lean:26-34`,
  `GeneralFibreProductLiftAdic.lean:77-95` and `GeneralFibreProductLiftUniqueAdic.lean:31-34`.
  Every one of those paragraphs says it outright — *"Issue 812 deleted it"*, *"That layer is
  gone"*, *"None of those exist any more; the module is gone entirely"*, *"Every mention of those
  names in this library is history"* — which is what makes the bound checkable rather than a
  licence.

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
