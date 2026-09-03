# The `--key concl` half of the duplicate census

*Issue 1538, under the dedup umbrella 1395. Successor to issue 1534, which built
`scripts/signature_scan.lean` and `scripts/signature_scan.py` and read the other half.*

Row 1534's probe has two keys. `--key type` buckets on the hash of the whole type; `--key concl`
buckets on the pretty-printed conclusion. They are blind to different things, and 1534 read
`--key type` exhaustively — all 55 cross-module buckets, nothing surviving — while sampling
`--key concl`. The asymmetry ran the wrong way: `--key type` is precisely the key that **cannot**
see `FormalSpectrum.sectionsMk` and `FormalSpectrum.sectionsOpenHom`, the pair the probe was built
to find, because one carries two instance binders the other does not. So "nothing survived reading"
was established for the half that could not have found the defect.

This document reads the other half: **all 91 cross-module theorem buckets under `--key concl`**,
on `e0fd2e8`. Every claim of subsumption it makes is elaborated in
`scripts/census_concl_checks.lean`; none is asserted from reading alone.

The bucket numbering `B01`…`B91` below is **derived, not stable**: it is the tool's own ordering,
`sorted(thm.items(), key=lambda kv: (-len(kv[1]), kv[0]))`, so it renumbers whenever master adds a
declaration to a bucket. Regenerate it rather than trusting a `B`-number read from an older
revision of this file; the "how it drifted" section below is worked through once for exactly that
reason.

## Recipe

```
export XDG_CACHE_HOME="$PWD/.cache-home"
lake exe cache get && lake build --wfail
lake env lean scripts/signature_scan.lean > /tmp/signatures.tsv   # ~20 s warm
python3 scripts/signature_scan.py /tmp/signatures.tsv --key concl
lake env lean scripts/census_concl_checks.lean                    # silence is the result
```

## The population, and how it drifted

Measured on `e0fd2e8`, against `edc7a8e` and 1534's figures on `9dbf476`:

| | `9dbf476` | `edc7a8e` | `e0fd2e8` |
|---|---|---|---|
| declarations extracted | 6226 | 6248 | 6262 |
| generated names dropped | 490 | 490 | 490 |
| sort-valued conclusions | 94 | 94 | 94 |
| **population bucketed** | **5642** | **5664** | **5678** |
| `--key type`: >= 2 / cross / theorem | 86 / 55 / 2 | 86 / 55 / 2 | 86 / 55 / 2 |
| `--key concl`: >= 2 / cross / theorem | 273 / 199 / 87 | 274 / 200 / 88 | 276 / 203 / **91** |

**`9dbf476` -> `edc7a8e`, 22 declarations.** Entirely PR #517
(`FormalSchemes/AdicOpennessHalf.lean`, the openness half of adicity for issue 1218). Those 22
landed in buckets that already existed — the conservativity-affine-step bucket and the cofinality
bucket below — and added one new cross-module theorem bucket.

**`edc7a8e` -> `e0fd2e8`, 14 declarations.** Entirely PR #519
(`FormalSchemes/AffineThickeningsOpenImmersion.lean`, the *unconditional* form of the same, and
EGA I 10.12's affine case). This drift is the more instructive of the two, because it is the case
the census has to survive rather than the case it was measured on:

* two buckets **grew**: B09 (5 -> 6) and B13 (4 -> 5);
* three buckets are **new and cross-module only because of #519** — B17, B47 and B48. B17's
  other three members are all in `FormalSchemes.AdicOpennessHalf`, so it was a bucket the
  cross-module filter dropped; B47's and B48's other member is a single declaration in
  `FormalSchemes.AffineThickenings`, so they were not buckets at all. A file that states the
  general form of what a neighbour states specially is exactly the event that turns an
  intra-module family, or a lone declaration, into a cross-module collision;
* B13 changed **class**, F -> S, because the arriving member subsumes one that was there;
* the growth reordered the table: **80 of the 88 carried buckets have a different `B`-number**
  than they did on `edc7a8e` — only `B01`–`B08` are unmoved — purely from two buckets gaining one
  member each and three appearing. This is why the numbering is documented above as derived.

**Neither drift changed anything under `--key type`:** that key is sensitive to the binder list,
and both PRs' statements carry hypotheses their neighbours do not. Twice now, the two keys have
not been interchangeable.

The 91 theorem buckets hold **284 declarations**: 63 of size 2, 8 of size 3, 5 of size 4, 6 of
size 5, 2 of size 6, 2 of size 8, 2 of size 9, 2 of size 11, 1 of size 16.

The remaining 203 - 91 = **112 cross-module buckets have no theorem member**. They are `def`
families — one construction at several parameters — and the `--key type` pass already covered
that shape and found nothing. They are excluded here deliberately and not silently; re-reading
them is a separate row if anyone wants it.

### Drift since the reading

The reading is of `e0fd2e8` and is deliberately left there. The tally, the "Every bucket" table
and the per-bucket notes below are what the probe printed on that commit, and none of them is
rewritten to match a later one: a census is a dated measurement, and one that quietly tracks
master stops being evidence of anything. What has happened to that population since is recorded
instead — once, here, and in a sentence under each finding.

Six rows acted on the six findings — 1541 (PR #521), 1542 (#525), 1543 (#523), 1544 (#522),
1545 (#524) and 1547 (#520) — and row 1554 (#526) has since renamed an API two of them touch.
**Five of those seven only moved, renamed or annotated declarations.** A docstring is invisible to
both the key and the class — the key is a printed conclusion, the class is a reading of what the
members say — and so is a rename. A *rehome* is the one of the three that could move a figure, by
pulling a bucket's members into a single module and so out of the cross-module filter; none of
these did. Two rows deleted a declaration, and those two are the whole of the drift:

* row 1543 deleted the downward `IsPrecomplete` transfer — **B62 vanishes**;
* row 1542 deleted `CompletedTensorAwayInterchange.idealOfDefinition_fg` — **B31 vanishes**.

Each was a two-member bucket and a bucket needs two members, so neither shrinks; each stops being
a bucket. Re-run on `c5b5c48`, against the `e0fd2e8` column above:

| | `e0fd2e8` | `c5b5c48` |
|---|---|---|
| declarations extracted | 6262 | 6260 |
| generated names dropped | 490 | 490 |
| sort-valued conclusions | 94 | 94 |
| **population bucketed** | **5678** | **5676** |
| `--key concl`: >= 2 / cross / theorem | 276 / 203 / 91 | 274 / 201 / **89** |

Minus two on every line that can move, which is what two deleted declarations in two dissolved
buckets look like. The dissolution was checked directly rather than inferred from the totals:
neither `IsPrecomplete K M` nor `(CompletedTensorProduct.idealOfDefinition R I A B).FG` is a key
of the re-run. Every other bucket these findings name is unchanged in size — B06 still holds
eight, B09 six, B13 five, B17 four, B27 three, B47 and B63 two.

Every `B`-number after B31 moves, though. A label is a position in `sorted(...)`, so B31 leaving
shifts each of the labels after it up by one and B62 leaving shifts them again: from B32 on, the
label in this document is not the label a re-run prints. That is why each finding is keyed to its
**finding number** and to declaration names, and why the repair paragraphs cite no `B`-number.

## Classification

Five classes. Every bucket is in exactly one; where a bucket contains members of more than one
kind it is filed under the most actionable.

* **N — noise.** The printed key carries no statement: a bare equation (`f = g`), a one-symbol
  predicate applied to a variable, or a structure-field projection. The members are unrelated
  declarations that collide because their authors named variables the same way.
* **F — family or ladder.** One statement at several parameters; parallel statements at parallel
  data types; case leaves of one proof; a documented chain that discharges hypotheses one at a
  time; or several genuinely *independent* sufficient criteria for one predicate, no two of which
  subsume each other.
* **R — deliberate second route.** Two proofs of literally one statement, both kept on purpose,
  with a docstring saying why.
* **S — strictly-stronger pair.** One member's hypotheses imply another's, verified by
  elaboration. Not necessarily a duplicate; the weaker member is a corollary and should say so.
* **D — duplicate.** One statement written twice, the two differing only by binders that are not
  used.

### The tally

| class | buckets | declarations |
|---|---|---|
| N — noise | 19 | 62 |
| F — family or ladder | 50 | 145 |
| R — deliberate second route | 4 | 10 |
| S — strictly-stronger pair | 16 | 63 |
| D — duplicate | 2 | 4 |
| **total** | **91** | **284** |

## The result that matters

**Reading the `--key concl` half was not a formality: it produced six findings that nothing on
the tree recorded, and the class row 1538 nominated for dispatch as noise turns out to hold
five buckets that are not noise, four of them subsumptions.**

The past tense is a repair and not a hedge. **All six findings have since been acted on, one row
each**, and the paragraph under each finding below names the row, the pull request that landed it
and what that row actually did — which twice was not what the finding predicted. Two of the six
ended in a deletion, and those two deletions are the only movement in this document's population;
"Drift since the reading" above has the figures.

Row 1538 listed 19 buckets whose printed key is a bare equation or one-symbol predicate and
proposed handling them as a class. **Fourteen of the nineteen are indeed noise. Five are not:**

* **B27**, key `IsUnit a` — `isUnit_stalk_of_isUnit_zero` is `isUnit_of_isUnit_stalkProj` at
  `n = 0`. **S, undeclared when read**, declared by row 1541; Finding 1.
* **B63**, key `L.FG` — `IsTopologicallyFiniteType.fg` is `fg_of_presentation` at the witness.
  **S, undeclared when read**, declared by row 1544; Finding 3.
* **B20**, key `x = y` — `IsHausdorff.eq_of_mk_pow_eq` is `..._succ_eq` reindexed. **S, declared.**
* **B55**, key `IsAdic J` — `IsAdic.of_le_of_pow_le`'s two containments are an
  `Ideal.IsCofinal`, so it is `Ideal.IsCofinal.isAdic`. **S, declared.**
* **B74**, key `r₁ = r₂` — the general invariant-section lemma and its Tate-node
  instantiation. **F.**

Two of the five, B20 and B55, were themselves filed **N** in an earlier draft of this document and
corrected in review — which is the argument below happening to its own author, one turn further
in. Both are elaborated in `scripts/census_concl_checks.lean` like every other claim here.

**A key that says nothing does not imply that the declarations under it say nothing.** The
uninformative key is a statement about the *key*, not about the bucket; the five above are exactly
as substantive as any bucket with a long key, and a class dispatch would have dropped all of them.
The sieve to avoid is not "the key looks like noise" but "the members are about unrelated
subjects", and only reading decides that. This is the same lesson as row 1534's own — an unchecked
filter silently shrinks the population a census is a census of — one level up: applied to buckets
rather than to declarations. It also has a practical corollary for a reviewer: **read every member
of whatever class a census proposes to dispatch as a class**, because that is where the misfilings
are.

The N/F line, where it is fuzzy, is drawn at *is the collision worth a reader's second look* rather
than at relatedness. B73, B75, B76, B80 and B81 are parallel statements at parallel data types,
which is this document's own **F** wording, and are filed N because nothing actionable sits under
any of them.

## Findings

### Undeclared when the census read them, and declared by this census's own rows

Each was a separate row, and **all six have landed**. The italicised paragraph under each finding
names the row and its pull request and says what actually changed; where a row did something other
than what its finding proposed, that is what the paragraph records.

This is a third category and not the *Declared* section below: those relations were already
declared when the census read them, these are declared **because** it read them. The elaborated
witness for each is in `scripts/census_concl_checks.lean`, whose docstrings carry the same
annotations, and whose `example`s are unchanged — what they check is that one declaration's
statement is closed by another, which does not depend on whether a docstring names the pair.

1. **B27.** `FormalSpectrum.isUnit_stalk_of_isUnit_zero` (`FormalSchemes.Spf`) is
   `FormalSpectrum.isUnit_of_isUnit_stalkProj` (`FormalSchemes.Thickenings`) at `n = 0`. The
   general form is downstream of the special one, so the special one cannot cite it; the fix is a
   move or a note, not a deletion in place.

   *Resolved by row 1541* (PR #521), by the note. Nothing moved and nothing was deleted: each
   docstring now names the other declaration and says which way the implication runs. The relation
   is a **ladder rung** rather than a corollary — the general form is proved *from* the special
   one — so the citation the general form owes is upward, and the special form gains the pointer
   it could not have made into a proof. The bucket is unchanged in size, class and key; it is now
   *declared*.
2. **B62.** The downward `IsPrecomplete` transfer — when the census read it,
   `IsPrecomplete.of_cofinal` in `FormalSchemes.CofinalSheafComparisonGeneral` — takes
   `K <= I` and `I ^ c <= K`, which together *are* an `Ideal.IsCofinal`, so it is
   `IsPrecomplete.of_isCofinal` (`FormalSchemes.CofinalAdicRing`). The two modules are
   incomparable — neither imports the other — and the general form is additionally
   polymorphic in the module's universe where the special one is not.

   *Resolved by row 1543* (PR #523), and **not** by the note the incomparability seems to force.
   The row priced the incomparability instead of assuming it: making the general form visible from
   `FormalSchemes.CofinalSheafComparisonGeneral` costs **one import and two modules** of closure,
   which is not a wall, so the downward statement was **deleted**.
   `IsPrecomplete.of_cofinal` no longer exists — the name above is a historical citation and
   resolves to nothing — and its two call sites, `generalCofinalSpfIso` in that file and
   `FormalSpectrum.isAdicRing_mul` in `FormalSchemes.CofinalStructMap`, now
   read `IsPrecomplete.of_isCofinal (Ideal.IsCofinal.of_le_of_pow_le …)`. The import went in with
   the deletion, so the sentence above about the two modules being incomparable is true of the
   tree the census read and false of the tree today. **The bucket does not shrink; it vanishes**:
   a bucket needs two members, so `IsPrecomplete K M` is no longer a key of this census at all.
3. **B63.** `IsTopologicallyFiniteType.fg` (`FormalSchemes.TopFiniteTypeBasis`) is
   `RestrictedPowerSeries.fg_of_presentation` (`FormalSchemes.TopFiniteTypeTrans`) applied to the
   presentation inside the tf-type witness. The general form does not use surjectivity of the
   presentation, which is the whole of the difference. Incomparable modules again.

   *Resolved by row 1544* (PR #522). The incomparability was not the obstacle it looks like: the
   shared content of the two is `IsTopologicallyFiniteType.map_eq_of_presentation`
   (`FormalSchemes.TopFiniteType`), which is upstream of **both**, and each of the two was one
   `Ideal.FG.map` away from it. The general form now lives beside that lemma as
   `IsTopologicallyFiniteType.fg_of_presentation`, and the special form cites it. The bucket
   still has two members and is unchanged in size, class and key; it is now *declared*.

   Row **1554** (PR #526) has since moved the whole `IsTopologicallyFiniteType` API to the root,
   so the special form's spelling above is one namespace shorter than the census read it. Nothing
   else about this finding moves: a rename changes no conclusion, hence no bucket.
4. **B31 (duplicate).** `CompletedTensorProduct.idealOfDefinition_fg` — then in
   `FormalSchemes.AffineFibreProductLRS` — and `CompletedTensorAwayInterchange.idealOfDefinition_fg`
   (`FormalSchemes.CompletedTensorAwayInterchangeSpf`) are one statement about one ideal. The
   first carries **six** instance binders — two topologies and four `IsAdicRing`s — that its
   conclusion does not mention and its proof does not need. Incomparable modules, so the repair is
   to move one of them, not to make one cite the other.

   *Resolved by row 1542* (PR #525), by the move — and by a deletion the finding did not ask for.
   `CompletedTensorAwayInterchange.idealOfDefinition_fg` is **gone**: that name exists nowhere in
   the library, and the sentence above is a historical citation of it. The survivor is
   `CompletedTensorProduct.idealOfDefinition_fg`, rehomed to `FormalSchemes.CompletedTensor` —
   where `CompletedTensorProduct.idealOfDefinition` is defined, and which was already in both
   former homes' import closure, so their incomparability was never the obstacle — and it carries
   no instance binder its conclusion does not mention. **The bucket does not shrink; it vanishes**,
   for the same reason B62 does.

   A **third** declaration states the same thing with `A` pinned to the annulus:
   `AlgebraicGeometry.tensorIdealOfDefinition_fg` (`FormalSchemes.TateSelfProductAdicOverBase`),
   which is now an application of the survivor rather than a variant of it. `--key concl` could
   never have bucketed it here — a pinned argument changes the printed conclusion — and it is
   deliberately not retired; row **1563** carries that limit and the reason.
5. **B06, two lemmas.** `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_isSplitMono` and
   `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_retraction`
   (`FormalSchemes.ClosedImmersionSplitMono`) ask for a closed *embedding* of base maps where
   `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_isClosed_range_of_isSplitMono` and
   `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_isClosed_range_of_retraction`
   (`FormalSchemes.GeneralSeparatedRange`) ask only for a closed range. A closed embedding has
   closed range, so both are corollaries. One row, one file, one edit: the closed-range forms need
   nothing from `FormalSchemes.GeneralSeparatedRange` and could be stated upstream beside the
   forms they subsume.

   *Resolved by row 1545* (PR #524), by exactly that move. Both closed-range criteria now live in
   `FormalSchemes.ClosedImmersionSplitMono` beside the closed-embedding pair, and each
   closed-embedding form is the application of its closed-range form to
   `Topology.IsClosedEmbedding.isClosed_range`, verbatim. The module attribution above is
   therefore the census's reading and not the tree: `FormalSchemes.GeneralSeparatedRange` keeps
   neither of the two. No statement was added, deleted or renamed, so the bucket keeps its size,
   class and key; two of its eight members are now a *declared* pair.
6. **B09 / B13 / B17, one cluster, and a row was already open on it.** Three of PR #519's four
   unconditional results — `FormalSpectrum.le_radical_map_of_openImmersion`,
   `FormalSpectrum.isCofinal_map_of_openImmersion` and
   `IsTopologicallyFiniteType.of_openImmersion` (`FormalSchemes.AffineThickeningsOpenImmersion`) —
   strictly subsume **five** declarations that were already on the tree, listed under those three
   buckets. All five live *upstream* of the file that subsumes them, so none can cite it; the remedy
   is a note on each, not a deletion. Filed as row **1547** by #519's reviewer before this document
   was re-measured, so **no new row here** — it is counted in the tally and named in the findings
   because a census that silently omitted its largest S cluster would be wrong, not because it is
   unfiled. The five are `le_radical_map_of_range_eq_basicOpenChart`,
   `le_radical_map_of_range_eq_univ`, `isCofinal_map_of_range_eq_basicOpenChart`,
   `of_openImmersion_range_eq_univ` and `of_openImmersion_range_eq_basicOpen`.

   The fourth unconditional result, `FormalSpectrum.hasAffineThickenings_opensRange`, subsumes
   **nothing**, and B47 — where it meets
   `hasAffineThickenings_opensRange_of_range_eq_basicOpenChart` — is **F**, not S. See the
   per-bucket note on B47 below: the older member is `omit`-ted of all four of
   `[TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J]` and the newer one
   needs all four, so the two hypothesis sets are incomparable in both directions. An earlier
   revision of this document counted it as a sixth subsumption; that was wrong, and how the
   mistake survived an `example` is recorded in the header of
   `scripts/census_concl_checks.lean`.

   *Resolved by row 1547* (PR #520), by the note on each. All five now carry a **Now a special
   case** paragraph naming the general form and saying why the special form is kept — it is
   upstream of `FormalSchemes.AffineThickeningsOpenImmersion` and cannot cite it — and three
   headline claims that the general theorem had falsified were corrected rather than merely
   annotated. A **sixth** docstring changed, of the opposite shape:
   `FormalSpectrum.hasAffineThickenings_opensRange_of_range_eq_basicOpenChart` gained a *Not a
   special case, despite appearances* paragraph, which is B47's **F** verdict written where a
   reader meets the declaration instead of only here. No statement moved, so none of the three
   buckets moves.

### Declared: a docstring already names the relation

No row. Listed because a declared subsumption is still an asserted one, and each is checked in
`scripts/census_concl_checks.lean`.

* **B46 (duplicate).** `CompletedTensorProduct.codiagonal_le_comap` carries four instance binders
  that `CompletedTensorProduct.codiagonal_le_comap'` does not, and the primed docstring calls them
  "spurious" in as many words. Filed as **D** rather than **S** because it is one statement twice,
  not two statements one of which is stronger. The reason it has not been repaired is recorded on
  the primed form: the layer that needs it cannot see the topological section variables.
* **B20.** `IsHausdorff.eq_of_mk_pow_eq` is `IsHausdorff.eq_of_mk_pow_succ_eq` reindexed, and the
  succ form's docstring is titled "`eq_of_mk_pow_eq`, for a family that only starts at level `1`".
  Same module. The bucket also holds two unrelated `Hom.ext`s, and is filed **S** rather than
  **N** on this document's own rule that a mixed bucket goes under its most actionable member.
* **B55.** `IsAdic.of_le_of_pow_le`'s `I ≤ J` and `J ^ n ≤ I` together *are* an
  `Ideal.IsCofinal`, so it is `Ideal.IsCofinal.isAdic` — the identical shape to Finding 2, and
  here declared: `isAdic`'s docstring names `of_le_of_pow_le` explicitly, saying that the
  *converse* does not apply rather than that this direction fails.
* **B50.** `IsAdicRing` extends `IsAdicComplete`, so
  `RestrictedLaurentSeries.algebraMap_injective` is
  `RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete`. The stronger says so; the
  weaker instead says "Move it opportunistically", which is about a different problem.
* **B08 / B34.** Conservativity's `AlgebraicGeometry.FormalScheme.IsAdicOpenImmersionProperty`
  hypothesis is redundant. Both docstrings say so, on both members, in both buckets. This is the
  model of a ladder that needs no reader.
* **B09.** The cofinality form of conservativity's affine step is the containment form, because
  cofinal ideals have equal radicals.
* **B02, three pairs.** `isSeparated_of_openCover`, `..._base` and `..._isClosed_range` are the
  `_of_diagonal_cover` trio with `affineCover` replaced by an arbitrary cover. The relation is
  declared in the *stronger* member of each pair and not in the weaker; the weaker three are the
  older statements and are silent.
* **B39.** Large-period freeness of the shift is the `n != 0` statement restricted.
* **B29 / B30.** The primed node-chart lemmas are the unprimed ones with their hypothesis
  discharged.

### What this census structurally cannot see

Unchanged from 1534, and worth not rediscovering:

* The **proof-shaped** class — one construction appearing once as a declaration and once as an
  inline `refine`, row 1510's instance B. A signature scan sees declarations; it has no access to
  proof terms. Nobody has costed comparing them on this tree.
* The **folded/unfolded** class. 305 declarations have a conclusion whose head is a `def` of this
  project, so `whnf` would change it; the extractor marks them in its `foldable` column and
  normalising them is a `MetaM` pass and a different row.
* Anything the **binder list** distinguishes. B05 is the clean illustration: nine statements of
  EGA I 10.6.10 share a conclusion and differ entirely in the datum they take about the target.
  `--key concl` groups them; reading them apart is a person's job, and that is why the bucket count
  is not the number to act on.

## Every bucket

Class letters as above. `n` is the number of declarations in the bucket.

| # | n | class | printed key (truncated at 68) |
|---|---|---|---|
| B01 | 16 | F | `CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.bothAlgData...` |
| B02 | 11 | S | `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated DX σX hστX ...` |
| B03 | 11 | N | `f = g` |
| B04 | 9 | N | `g₁ = g₂` |
| B05 | 9 | F | `∃! g, ∀ (n : ℕ), CategoryTheory.CategoryStruct.comp (FormalSpectr...` |
| B06 | 8 | S | `AlgebraicGeometry.FormalScheme.IsClosedImmersion f` |
| B07 | 8 | F | `IsAdicComplete (AlgebraicGeometry.tateInvNodeChartAwayIdeal R I q...` |
| B08 | 6 | S | `AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType R I f` |
| B09 | 6 | S | `IsTopologicallyFiniteType R I B (Ideal.map (algebraMap R B) I)` |
| B10 | 5 | F | `(AlgebraicGeometry.tateInvNodeChartAwayIdeal R I q hq hI).FG` |
| B11 | 5 | F | `(AlgebraicGeometry.tateInvNodeChartAwaySubring R I q hq hI).HasCo...` |
| B12 | 5 | N | `F = G` |
| B13 | 5 | S | `J.IsCofinal (Ideal.map (algebraMap R B) I)` |
| B14 | 5 | F | `X.HasAffineChartAt y` |
| B15 | 5 | N | `u = v` |
| B16 | 4 | F | `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion self.map` |
| B17 | 4 | S | `J ≤ (Ideal.map (algebraMap R B) I).radical` |
| B18 | 4 | F | `Q.HasAffineChartAt z` |
| B19 | 4 | N | `s = t` |
| B20 | 4 | S | `x = y` |
| B21 | 3 | F | `AlgebraicGeometry.FormalScheme.IsClosedImmersion (CategoryTheory....` |
| B22 | 3 | F | `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom (CategoryTheory...` |
| B23 | 3 | R | `IsAdicRing (annulusIdealOfDefinition R I q)` |
| B24 | 3 | F | `IsAdicRing self.L` |
| B25 | 3 | F | `IsTopologicallyFiniteType R I A L` |
| B26 | 3 | R | `IsTopologicallyFiniteType R I R I` |
| B27 | 3 | S | `IsUnit a` |
| B28 | 3 | F | `¬AlgebraicGeometry.LocallyRingedSpace.IsFreeProperlyDiscontinuous...` |
| B29 | 2 | S | `(AlgebraicGeometry.tateInvNodeChartAwaySubring R I q hq hI).IsAdi...` |
| B30 | 2 | S | `(AlgebraicGeometry.tateInvNodeChartAwaySubring R I q hq hI).IsInd...` |
| B31 | 2 | D | `(CompletedTensorProduct.idealOfDefinition R I A B).FG` |
| B32 | 2 | F | `(FormalSpectrum.awayCompletionHom I g) t ∈ FormalSpectrum.awayCom...` |
| B33 | 2 | N | `AlgebraicGeometry.FormalScheme.IsLocallyTopFiniteType R I X` |
| B34 | 2 | S | `AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType R I f ↔ ...` |
| B35 | 2 | F | `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (AlgebraicGe...` |
| B36 | 2 | F | `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (AlgebraicGe...` |
| B37 | 2 | F | `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.desc k h)` |
| B38 | 2 | F | `AlgebraicGeometry.tateInvGlobalSubring hI = (algebraMap R (annulu...` |
| B39 | 2 | S | `AlgebraicGeometry.tateShiftAut R I q hq hI ^ n ≠ 1` |
| B40 | 2 | F | `CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.specAwayMap...` |
| B41 | 2 | F | `CategoryTheory.CategoryStruct.comp (D.xFormalGlueData.ι i) (Categ...` |
| B42 | 2 | F | `CategoryTheory.CategoryStruct.comp (D.xFormalGlueData.ι i) D.xStr...` |
| B43 | 2 | F | `CategoryTheory.CategoryStruct.comp self.src f =   CategoryTheory....` |
| B44 | 2 | F | `CategoryTheory.IsIso (D.desc k h)` |
| B45 | 2 | N | `CategoryTheory.IsIso f` |
| B46 | 2 | D | `CompletedTensorProduct.idealOfDefinition R I A A ≤   Ideal.comap ...` |
| B47 | 2 | F | `FormalSpectrum.HasAffineThickenings I (AlgebraicGeometry.LocallyR...` |
| B48 | 2 | F | `FormalSpectrum.HasAffineThickenings I U` |
| B49 | 2 | F | `FormalSpectrum.arbSheafComponent I J f g =   AdicCompletion.mapCo...` |
| B50 | 2 | S | `Function.Injective ⇑(algebraMap R (RestrictedLaurentSeries R I))` |
| B51 | 2 | R | `Function.Surjective   ⇑(CommRingCat.Hom.hom       (AlgebraicGeome...` |
| B52 | 2 | F | `Function.Surjective ⇑(CommRingCat.Hom.hom (AlgebraicGeometry.Loca...` |
| B53 | 2 | F | `I.radical = J.radical` |
| B54 | 2 | F | `Ideal.map (self.θ i j h).toRingHom (Ideal.map (algebraMap (self.C...` |
| B55 | 2 | S | `IsAdic J` |
| B56 | 2 | F | `IsAdicComplete (Ideal.comap S.subtype K) ↥S` |
| B57 | 2 | F | `IsAdicRing (Ideal.map (algebraMap R (self.A i)) I)` |
| B58 | 2 | F | `IsAdicRing self.I` |
| B59 | 2 | F | `IsAdicRing self.J` |
| B60 | 2 | F | `IsAdicRing self.K` |
| B61 | 2 | F | `IsHausdorff K M` |
| B62 | 2 | S | `IsPrecomplete K M` |
| B63 | 2 | S | `L.FG` |
| B64 | 2 | F | `Q.HasAffineChartAt ((CategoryTheory.ConcreteCategory.hom π.base) x)` |
| B65 | 2 | F | `RingHom.AdicKerClosed (RestrictedPowerSeries.idealOfDefinition R ...` |
| B66 | 2 | F | `S.HasCofinalInducedFiltration K` |
| B67 | 2 | F | `Set.range ⇑(CategoryTheory.ConcreteCategory.hom (D.desc k h).base...` |
| B68 | 2 | F | `Topology.IsClosedEmbedding (FormalSpectrum.map I J φ hφ) ∧   ∀ (y...` |
| B69 | 2 | N | `X.LocallyFG` |
| B70 | 2 | N | `f₁ = f₂` |
| B71 | 2 | N | `m₁ = m₂` |
| B72 | 2 | F | `n = 0 ∨ n = 1 ∨ n = -1` |
| B73 | 2 | N | `p ∈ K • ⊤` |
| B74 | 2 | F | `r₁ = r₂` |
| B75 | 2 | N | `self.J.FG` |
| B76 | 2 | N | `self.K.FG` |
| B77 | 2 | F | `self.θ j i ⋯ = (self.θ i j h).symm` |
| B78 | 2 | N | `x ∈ Set.range ⇑(CategoryTheory.ConcreteCategory.hom (AlgebraicGeo...` |
| B79 | 2 | N | `x ∈ Set.range ⇑(CategoryTheory.ConcreteCategory.hom self.map.base)` |
| B80 | 2 | N | `z = 0` |
| B81 | 2 | N | `z = w` |
| B82 | 2 | N | `z ∈ Set.range ⇑(CategoryTheory.ConcreteCategory.hom self.map.base)` |
| B83 | 2 | F | `⇑(CategoryTheory.ConcreteCategory.hom (D.specι i).base) ⁻¹'     S...` |
| B84 | 2 | F | `⇑(CategoryTheory.ConcreteCategory.hom (D.specι i).base) ⁻¹'     ⇑...` |
| B85 | 2 | F | `∃ X, X.toLocallyRingedSpace = Q` |
| B86 | 2 | R | `∃ Y,   Nonempty     (Y.toLocallyRingedSpace ≅ CategoryTheory.acti...` |
| B87 | 2 | F | `∃ g,   (∀ (i : (AlgebraicGeometry.tateChainInvFormalGlueData R I ...` |
| B88 | 2 | F | `∃ i y, (CategoryTheory.ConcreteCategory.hom (D.specι i).base) y = x` |
| B89 | 2 | N | `∃ n, J ^ n ≤ I` |
| B90 | 2 | F | `∃! g,   ∀ (i : (AlgebraicGeometry.tateChainInvFormalGlueData R I ...` |
| B91 | 2 | F | `∃! s, ∀ (i : D.toLocallyRingedSpaceGlueData.J), (CommRingCat.Hom....` |

Buckets not listed below are structure fields of parallel data types, or parallel
statements at two parallel constructions, and read in a line each.

* **B01** (F, n=16) 16 case leaves of one cocycle theorem, each with its own degeneracy
  hypotheses.
* **B02** (S, n=11) Eleven separatedness criteria. The `_of_openCover` trio subsumes the
  `_of_diagonal_cover` trio at `affineCover`; see the findings above.
* **B05** (F, n=9) EGA I 10.6.10 at nine target shapes. What separates them is the datum they take
  about the target, which is a binder, which this key hides.
* **B06** (S, n=8) Eight closed-immersion criteria; two of them are the closed-range forms
  specialised. See the findings above.
* **B07** (F, n=8) A discharge ladder for completeness of the node chart ring, each rung named in
  the next one’s docstring.
* **B08** (S, n=6) The `IsAdicOpenImmersionProperty` hypothesis is redundant and both docstrings
  say so.
* **B09** (S, n=6) The cofinality form is the containment form. Six rungs; #517 added two and
  #519 the top one, `IsTopologicallyFiniteType.of_openImmersion`, which strictly subsumes the two
  `_range_eq_*` rungs. Finding 6.
* **B10** (F, n=5) Discharge ladder, finite generation of the node chart ideal.
* **B11** (F, n=5) Discharge ladder, the filtration bridge.
* **B13** (S, n=5) The same cofinality at five strengths of hypothesis; #517 added one and #519
  `isCofinal_map_of_openImmersion`, which strictly subsumes
  `isCofinal_map_of_range_eq_basicOpenChart`. Reclassified F -> S by that arrival. Finding 6.
* **B14** (F, n=5) Chart-at from a `Spf`-shaped and a `Spec`-shaped datum, plus two assemblies of
  each.
* **B16** (F, n=4) The `isOpenImmersion` field of four unrelated chart structures.
* **B17** (S, n=4) New with #519, and cross-module only because of it: the openness half at four
  strengths, of which `le_radical_map_of_openImmersion` subsumes the two `_range_eq_*` forms.
  Finding 6.
* **B18** (F, n=4) `HasAffineChartAt` on the Tate quotient, at four different hypothesis shapes.
* **B20** (S, n=4) Two unrelated `Hom.ext`s, plus `IsHausdorff.eq_of_mk_pow_eq` and
  `..._succ_eq`, which are the same statement reindexed and say so. Declared; no row. The key is
  `x = y`, which is why this bucket was first filed N — see "The result that matters".
* **B21** (F, n=3) `comp`, and its two composites with an isomorphism. Neither of the latter
  subsumes the former.
* **B22** (F, n=3) Three presentations of EGA I 10.13’s composition law: predicate, tower, chart
  family.
* **B23** (R, n=3) Noetherian, adically-closed and separating routes to one conclusion, mutually
  documented.
* **B24** (F, n=3) The `IsAdicRing` field on `L` of three chart structures.
* **B25** (F, n=3) Three independent tf-type criteria; no two are comparable.
* **B26** (R, n=3) The established second-route example. Three routes to
  `IsTopologicallyFiniteType R I R I`, two of them deliberate non-vacuity witnesses.
* **B27** (S, n=3) `isUnit_stalk_of_isUnit_zero` is `isUnit_of_isUnit_stalkProj` at level zero.
  Finding 1.
* **B28** (F, n=3) A discharge ladder for non-discontinuity of the period-q shift.
* **B29** (S, n=2) The primed form has the hypothesis discharged; documented.
* **B30** (S, n=2) The primed form has the hypothesis discharged; documented.
* **B31** (D, n=2) One statement, two declarations, six unused instance binders on one of them.
  Finding 4. **No longer a bucket**: row 1542 deleted one of the two, so what is left is a
  singleton and the key drops out of the census.
* **B32** (F, n=2) A reduction and its discharge, each naming the other.
* **B33** (N, n=2) Two unrelated theorems about one predicate.
* **B34** (S, n=2) The `Iff` form of B08.
* **B38** (F, n=2) Two independent hypotheses, separation and Noetherianness, for one description
  of the global sections.
* **B39** (S, n=2) Freeness for |n| >= 2 is the `n != 0` statement restricted; documented.
* **B40** (F, n=2) Parallel statements at `ChartedCompletionDatum` and `ChartedSchemeDatum`.
* **B46** (D, n=2) One statement, two declarations, four unused instance binders on one of them.
  Documented.
* **B47** (F, n=2) New with #519, and **not** a subsumption in either direction.
  `hasAffineThickenings_opensRange_of_range_eq_basicOpenChart` carries
  `omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J]` and is stated
  over bare `CommRing`s; `hasAffineThickenings_opensRange` needs all four, so it cannot close the
  older statement — the restatement fails at `failed to synthesize instance TopologicalSpace R`,
  not at the mathematics. The gap is not closable by an `omit` on the newer one either: I
  measured it, and `omit [TopologicalSpace R] [IsAdicRing I] in` above
  `hasAffineThickenings_opensRange` makes its own proof fail, at `bijective_rangeSectionsHom`,
  with the same missing `TopologicalSpace R`; `[IsAdicRing J]` is load-bearing too, through
  `Ideal.eq_top_of_sup_eq_top_of_isAdicComplete J`. Two incomparable criteria, which is B48's
  shape.
* **B48** (F, n=2) New with #519: a span criterion and a basic-open-chart criterion for one
  predicate. Neither subsumes the other — the chart form goes through
  `hasAffineThickenings_basicOpen`, not through a span.
* **B49** (F, n=2) A reduction and its discharge.
* **B50** (S, n=2) `IsAdicRing` extends `IsAdicComplete`; the stronger member says so.
* **B51** (R, n=2) The established second-route example: two proofs of the Tate diagonal stalk
  fact.
* **B52** (F, n=2) Open immersion and retraction are independent sufficient conditions.
* **B53** (F, n=2) The `IsAdic` and `Ideal.IsCofinal` forms, on either side of the layer where
  `Ideal.IsCofinal` is defined. The `IsAdic` form is upstream and is what the bridge is built
  from.
* **B55** (S, n=2) `IsAdic.of_le_of_pow_le`'s two containments are an `Ideal.IsCofinal`, so it is
  `Ideal.IsCofinal.isAdic` — the same shape as Finding 2, but declared: `isAdic`'s docstring names
  it. No row. Key `IsAdic J`, so this too was first filed N.
* **B56** (F, n=2) A criterion and the general statement it feeds.
* **B61** (F, n=2) `K <= I` and cofinality are independent hypotheses; neither implies the other.
* **B62** (S, n=2) The two containments of the downward transfer are an `Ideal.IsCofinal`.
  Finding 2. **No longer a bucket**: row 1543 deleted the downward member, so what is left is a
  singleton and the key drops out of the census.
* **B63** (S, n=2) `IsTopologicallyFiniteType.fg` is `fg_of_presentation` at the witness. Finding
  3.
* **B64** (F, n=2) The general pointwise chart theorem and its Tate instantiation.
* **B65** (F, n=2) Two independent hypotheses for adic closedness of the presentation kernel.
* **B66** (F, n=2) Module-finiteness and a retraction are independent routes to the bridge.
* **B68** (F, n=2) Two independent inputs to one closed-immersion conclusion.
* **B74** (F, n=2) The general invariant-section lemma and its Tate-node instantiation.
* **B85** (F, n=2) Two incomparable hypotheses for one existence statement; the docstrings compare
  them.
* **B86** (R, n=2) One object, two constructions, the second re-derived from the general
  criterion.
* **B87** (F, n=2) A quantifier reduction and the general statement it comes from.
* **B89** (N, n=2) `IsAdic.exists_pow_le` is what `IsAdic.isCofinal` is built from, not a
  corollary of it.
* **B90** (F, n=2) A gluing statement and the `ExistsUnique` packaging of it.
* **B91** (F, n=2) The existence half of the sheaf axiom, and the same with the overlap condition
  named.
