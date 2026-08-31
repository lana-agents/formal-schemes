import FormalSchemes.CompletionBasicOpenOverlap
import FormalSchemes.CompletionBasicOpenMap
import FormalSchemes.Gluing
import FormalSchemes.OpenCoverGlueMorphisms

set_option linter.style.header false

/-!
# Gluing the basic-open completions of one affine, at an arbitrary index (EGA I, 10.8)

For a commutative ring `R`, a finitely generated ideal `I` and an **arbitrary** family
`f : ι → R`, this file builds the glue datum whose patches are the formal completions of the basic
opens `D(f i) ⊆ Spec R` and whose overlaps are the completions of the intersections
`D(f i) ∩ D(f j)`, and glues it into an `AlgebraicGeometry.FormalScheme`.

Both **completion** glue data already on the tree escape the triple-overlap fields rather than
discharging them: `FormalSchemes/CompletionGlueTwoPatch.lean` has index `ULift Bool`, where no
triple of indices is pairwise distinct, and `FormalSchemes/TateChainGlue.lean` has index
`ULift ℤ`, where non-consecutive overlaps are empty and the fields are forced by
`IsInitial.hom_ext`. Here the index type is arbitrary and neither escape is available: `t'`,
`t_fac` and `cocycle` are proved.

This is **not** the first non-vacuous cocycle on the tree, and the difference is in the route
rather than in the novelty. `FormalSchemes/ThreeChartDatum.lean` supplies an
`AffineChartedFibreDatumX` on `ULift (Fin 3)` whose six geometric triple-overlap fields are genuine
(`ThreeChart.exists_pairwise_distinct`, `ThreeChart.datumX_t'_eq`), and
`AffineChartedFibreDatum.glueData'` (`FormalSchemes/GeneralFibreProductAffineBase.lean`) turns such
a datum into a `CategoryTheory.GlueData'`. There the cocycle is **carried as data** by the datum
and supplied at the algebra level, from comparison isomorphisms of completed localizations plus the
rigidity lemma `furtherLocAlgHom_eq_awayCongrHom`. Here no algebra-level cocycle is stated at all;
the geometric fields are proved directly, as below.

## How the cocycle is discharged, and why it contains no new geometry

Every object of the datum is an open formal subscheme of one ambient object, the completion
`Spf R^ = formalCompletion R I`: the patch at `i` by
`formalCompletion.basicOpenImmersion I hI (f i)`, each overlap by one further basic-open
immersion. All of those are monomorphisms, so each of `t_inv`, `t_fac` and `cocycle` can be
cancelled (`cancel_mono`) against the relevant inclusion into `Spf R^`, and in every case what is
left is one statement:

> a ring homomorphism **over `R`** induces a morphism of completions commuting with the two
> structure morphisms down to `formalCompletion R I`.

That is `cbMapOverR` below: one application of `formalCompletion.map_comp` and a congruence. The
pullback's universal property is never used, and no property of the triple overlap beyond
`formalCompletion.basicOpenOverlapIso` enters. All the content therefore sits in the *ring maps*,
and those come from the universal property of a localization:

* the overlap `V i j` is presented as `Spf ((R_{f i})_{f j})^` — a basic open **of the chart ring**
  `R_{f i}`, not of `R`. So its inclusion into the patch `U i` is `basicOpenImmersion` at the ring
  `R_{f i}` on the nose, and `formalCompletion.basicOpenOverlapIso`
  (`FormalSchemes/CompletionBasicOpenOverlap.lean`) identifies `pullback (f i j) (f i k)` with
  `Spf ((R_{f i})_{f j f k})^` verbatim. No comparison with
  `formalCompletion.nestedBasicOpenImmersion` is needed and neither
  `FormalSchemes/CompletionNestedBasicOpen.lean` nor its `Map` companion is imported.
* `(R_{f i})_{f j}` and `(R_{f j})_{f i}` are both localizations of `R` away from `f i · f j`
  (Mathlib's `IsLocalization.Away.mul` / `IsLocalization.Away.mul'` instances), and all three
  rotations of `(R_{f i})_{f j f k}` are localizations of `R` away from `f i · f j · f k`. The
  transitions are the comparison maps `IsLocalization.Away.lift`, and
  `IsLocalization.Away.lift_comp` is precisely the "over `R`" hypothesis the display above
  consumes.

## Main definitions and results

* `AlgebraicGeometry.completionBasicOpenGlueData'`: the `CategoryTheory.GlueData'` on
  `LocallyRingedSpace`, at index `ι`, with all eleven fields discharged.
* `AlgebraicGeometry.completionBasicOpenLRSGlueData`: the induced
  `AlgebraicGeometry.LocallyRingedSpace.GlueData`, via `CategoryTheory.GlueData.ofGlueData'`
  together with the open-immersion field `f_open`.
* `AlgebraicGeometry.completionBasicOpenFormalGlueData`: the
  `AlgebraicGeometry.FormalScheme.GlueData`, each patch being a formal completion.
* `AlgebraicGeometry.completionBasicOpenGlued`: the glued formal scheme.
* `AlgebraicGeometry.completionBasicOpenι` and
  `AlgebraicGeometry.completionBasicOpenGlued_jointly_surjective`: the charts are open immersions
  and they cover the glued object.
* `AlgebraicGeometry.completionBasicOpenToCompletion`: the canonical morphism from the glued object
  to `Spf R^`, and `AlgebraicGeometry.completionBasicOpenι_comp_toCompletion`, which says it
  restricts to the basic-open immersion on each chart.
* `FormalSpectrum.exists_mem_basicOpen_of_span_eq_top` and
  `FormalSpectrum.iSup_basicOpen_eq_top_of_span_eq_top`: the covering hypothesis, derived from
  `Ideal.span (Set.range f) = ⊤`.
* `AlgebraicGeometry.basicOpenCompletionCover`: the basic-open completions as a
  `FormalScheme.OpenCover` of `Spf R^`, under that hypothesis.
* `AlgebraicGeometry.completionBasicOpenι_pullback_comp`: the chart inclusions into the glued
  object agree on the fibre-product overlaps — the descent datum for the inverse morphism.
* `AlgebraicGeometry.completionFromCompletionBasicOpen`: the inverse morphism, and
  `AlgebraicGeometry.isIso_completionBasicOpenToCompletion`.
* `AlgebraicGeometry.completionBasicOpenGluedIso`: **the glued object *is* `formalCompletion R I`**,
  as an isomorphism of formal schemes, with `completionBasicOpenι_comp_gluedIso` and
  `basicOpenImmersion_comp_gluedIso_inv` pinning it on each chart.

## What this is a slice of

Gluing the basic opens of a single affine `Spec R` back together only re-presents
`formalCompletion R I`, and that is now proved here (`completionBasicOpenGluedIso`) rather than
merely intended: it is the smallest situation in which the cocycle condition has content, and it
comes with the checkable conclusion that makes the cocycle proof falsifiable.

An earlier version of this section said that proving the comparison invertible needed a
`LocallyRingedSpace`-level replication of `Mathlib/AlgebraicGeometry/Gluing.lean:262-423`, on the
ground that Mathlib's `Scheme.OpenCover.fromGlued` chain is keyed on `Scheme.OpenCover` throughout
and `Spf R^` is not a scheme. The premise about Mathlib is correct and the conclusion did not
follow: **this tree already carries that chain**, at exactly this generality, in
`FormalSchemes/OpenCoverGlueMorphisms.lean` — `FormalScheme.OpenCover.fromGlued` with
`fromGlued_base_surjective`, `fromGlued_base_injective`, `fromGlued_base_isOpenMap`,
`isOpenImmersion_fromGlued` and `instance isIso_fromGlued`, whose module docstring says outright
that it mirrors `Scheme.OpenCover.glueMorphisms`. Nothing had to be replicated; the inverse
morphism is `OpenCover.glueMorphisms` applied to the chart inclusions, and the two round trips are
`Multicoequalizer.hom_ext` and `OpenCover.hom_ext`.

One thing is deliberately not here.

* **The glued scheme and the morphism `X_{/Y} ⟶ X` at an arbitrary index** — the arbitrary-index
  analogue of `completionTwoPatchToScheme` (`FormalSchemes/CompletionTwoPatchToScheme.lean`).
  Not here, and no longer outstanding either: they are
  `AlgebraicGeometry.ChartedSchemeDatum.specGlued` (`FormalSchemes.ChartedSchemeDatum`) and
  `AlgebraicGeometry.ChartedCompletionDatum.toScheme`
  (`FormalSchemes.ChartedCompletionToScheme`). That line does **not** reuse the cocycle below: its
  `cancel_mono` proofs need the common ambient `Spf R^` that every basic open of one affine lies
  over, and charts with unrelated coordinate rings have no such object.

  This bullet used to say instead that the missing piece was "the second ring and the overlap
  identification `θ`" of `FormalSchemes/CompletionGlueTwoPatch.lean`. That was wrong: the
  arbitrary-index, different-rings glued **formal scheme** is `AffineChartedFibreDatumX.xGlued`
  (`FormalSchemes/GeneralFibreProductExposeX.lean`), whose transitions `τ i j` are exactly that
  `θ`, and `FormalSchemes/CompletionAsChartedGlued.lean` identifies `completionBasicOpenGlued` with
  one. The object was never the obstruction; the morphism down to a glued scheme is.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-! ### The covering hypothesis

The glued object is compared with `formalCompletion R I` only when the `f i` really do cover, and
the shape the comparison needs is a *pointwise* one: every point of `Spf R^` lies in one of the
basic opens `D(f i)`. That form is deliberately not derived by rewriting with
`PrimeSpectrum.iSup_basicOpen_eq_top_iff` — `Opens (FormalSpectrum I)` and
`Opens (PrimeSpectrum (R ⧸ I))` are definitionally equal but carry syntactically different topology
instances, and `FormalSchemes/FormalLineWitness.lean` records that `rw` with a `PrimeSpectrum`
lemma against a `FormalSpectrum` goal fails under `instances` transparency. The argument below is
elementary and avoids the question: if no basic open contained the point, its prime would contain
the span, hence be `⊤`.
-/

namespace FormalSpectrum

variable {B : Type u} [CommRing B] (K : Ideal B)

/-- **The covering hypothesis, pointwise, from a generating family.** If the `r i` generate the
unit ideal then every point of `Spf B` lies in one of the basic opens `D(r i)`. -/
theorem exists_mem_basicOpen_of_span_eq_top {κ : Type*} (r : κ → B)
    (h : Ideal.span (Set.range r) = ⊤) (x : FormalSpectrum K) :
    ∃ i, x ∈ basicOpen K (r i) := by
  by_contra hx
  have hmem : ∀ i, Ideal.Quotient.mk K (r i) ∈ x.asIdeal := by
    intro i
    by_contra hi
    exact hx ⟨i, hi⟩
  have hle : Ideal.span (Set.range fun i => Ideal.Quotient.mk K (r i)) ≤
      x.asIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  refine x.isPrime.ne_top (top_le_iff.mp ?_)
  refine le_trans (le_of_eq ?_) hle
  rw [← Ideal.map_top (Ideal.Quotient.mk K), ← h, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **The covering hypothesis in `iSup` form**, which is what `FormalSchemes/SpfBasicOpenCover.lean`
and the chart machinery are stated against. -/
theorem iSup_basicOpen_eq_top_of_span_eq_top {κ : Type*} (r : κ → B)
    (h : Ideal.span (Set.range r) = ⊤) :
    (⨆ i, basicOpen K (r i)) = ⊤ :=
  eq_top_iff.mpr fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr (exists_mem_basicOpen_of_span_eq_top K r h x)

end FormalSpectrum

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) {ι : Type u} (f : ι → R)

/-- A morphism of completions induced by a ring map **over `R`** commutes with the two structure
morphisms down to `formalCompletion R I`. -/
private theorem cbMapOverR {T T' : Type u} [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']
    {L : Ideal T} {L' : Ideal T'} (hL : L.FG) (hL' : L'.FG)
    (hTL : I.map (algebraMap R T) ≤ L) (hT'L' : I.map (algebraMap R T') ≤ L')
    (φ : T →+* T') (hLL : L.map φ ≤ L') (hφ : φ.comp (algebraMap R T) = algebraMap R T') :
    formalCompletion.map hL hL' φ hLL ≫ formalCompletion.map hI hL (algebraMap R T) hTL =
      formalCompletion.map hI hL' (algebraMap R T') hT'L' := by
  rw [← formalCompletion.map_comp I hI hL hL' (algebraMap R T) φ hTL hLL]
  exact formalCompletion.map_congr hI hL' _ _ hφ

/-- The chart ring `R_{f i}`. -/
private abbrev cbS (i : ι) : Type u := Localization.Away (f i)

/-- The ideal `I·R_{f i}` of the chart ring. -/
private abbrev cbK (i : ι) : Ideal (cbS f i) := I.map (algebraMap R (cbS f i))

/-- The image of `f j` in the chart ring `R_{f i}`. -/
private abbrev cbg (i j : ι) : cbS f i := algebraMap R (cbS f i) (f j)

/-- The overlap ring `(R_{f i})_{f j}`. -/
private abbrev cbT (i j : ι) : Type u := Localization.Away (cbg f i j)

/-- The triple-overlap ring `(R_{f i})_{f j f k}`. -/
private abbrev cbT3 (i j k : ι) : Type u := Localization.Away (cbg f i j * cbg f i k)

/-- The ideal carried by an overlap ring is the extension of `I` along the structure map. -/
private theorem cbIdeal_eq (i : ι) (x : cbS f i) :
    I.map (algebraMap R (Localization.Away x)) =
      (cbK I f i).map (algebraMap (cbS f i) (Localization.Away x)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The triple-overlap ring is a localization of `R` away from `f i · f j · f k`. -/
private theorem cbIsAway3 (i j k : ι) : IsLocalization.Away (f i * f j * f k) (cbT3 f i j k) := by
  rw [mul_assoc]
  haveI : IsLocalization.Away (algebraMap R (cbS f i) (f j * f k)) (cbT3 f i j k) := by
    rw [map_mul]; infer_instance
  exact IsLocalization.Away.mul' (cbS f i) (cbT3 f i j k) (f i) (f j * f k)

/-- Being a localization away from an element depends on the element only through its value. -/
private theorem cbAwayCongr {A : Type u} [CommRing A] [Algebra R A] {p q : R} (h : p = q)
    (H : IsLocalization.Away p A) : IsLocalization.Away q A := h ▸ H

/-- **The double-overlap transition ring map** `(R_{f j})_{f i} →+* (R_{f i})_{f j}`: both sides
are localizations of `R` away from `f i · f j`, so this is the canonical comparison, obtained from
the universal property of the source. -/
private def cbTau (i j : ι) : cbT f j i →+* cbT f i j :=
  IsLocalization.Away.lift (S := cbT f j i) (f i * f j)
    (IsLocalization.Away.algebraMap_isUnit (S := cbT f i j) (f i * f j))

private theorem cbTau_comp (i j : ι) :
    (cbTau f i j).comp (algebraMap R (cbT f j i)) = algebraMap R (cbT f i j) :=
  IsLocalization.Away.lift_comp _ _

/-- **The triple-overlap transition ring map** `(R_{f j})_{f k f i} →+* (R_{f i})_{f j f k}`: both
sides are localizations of `R` away from `f i · f j · f k`. -/
private def cbSigma (i j k : ι) : cbT3 f j k i →+* cbT3 f i j k :=
  haveI := cbAwayCongr (A := cbT3 f j k i) (p := f j * f k * f i) (q := f i * f j * f k)
    (by ring) (cbIsAway3 f j k i)
  haveI := cbIsAway3 f i j k
  IsLocalization.Away.lift (S := cbT3 f j k i) (f i * f j * f k)
    (IsLocalization.Away.algebraMap_isUnit (S := cbT3 f i j k) (f i * f j * f k))

private theorem cbSigma_comp (i j k : ι) :
    (cbSigma f i j k).comp (algebraMap R (cbT3 f j k i)) = algebraMap R (cbT3 f i j k) :=
  haveI := cbAwayCongr (A := cbT3 f j k i) (p := f j * f k * f i) (q := f i * f j * f k)
    (by ring) (cbIsAway3 f j k i)
  haveI := cbIsAway3 f i j k
  IsLocalization.Away.lift_comp _ _

/-- The patch `Spf (R_{f i})^`, as a locally ringed space. -/
private abbrev cbU (i : ι) : LocallyRingedSpace.{u} :=
  (formalCompletion (cbS f i) (cbK I f i) (hI.map _)).toLocallyRingedSpace

/-- The overlap `Spf ((R_{f i})_{f j})^`, as a locally ringed space. -/
private abbrev cbV (i j : ι) : LocallyRingedSpace.{u} :=
  (formalCompletion (cbT f i j) ((cbK I f i).map (algebraMap (cbS f i) (cbT f i j)))
    ((hI.map _).map _)).toLocallyRingedSpace

/-- The triple overlap `Spf ((R_{f i})_{f j f k})^`, as a locally ringed space. -/
private abbrev cbV3 (i j k : ι) : LocallyRingedSpace.{u} :=
  (formalCompletion (cbT3 f i j k) ((cbK I f i).map (algebraMap (cbS f i) (cbT3 f i j k)))
    ((hI.map _).map _)).toLocallyRingedSpace

/-- The inclusion of an overlap into a patch, a basic-open completion immersion of `Spf (R_{f i})^`.
-/
private abbrev cbFf (i j : ι) : cbV I hI f i j ⟶ cbU I hI f i :=
  (formalCompletion.basicOpenImmersion (cbK I f i) (hI.map _) (cbg f i j)).toLRSHom

/-- The ambient object `Spf R^`. -/
private abbrev cbW : LocallyRingedSpace.{u} := (formalCompletion R I hI).toLocallyRingedSpace

/-- A basic open of a chart is a basic open of the ambient completion: the two-step composite of
basic-open completion immersions is the functoriality morphism of `R → (R_{f i})_x`. -/
private theorem cbChartComp (i : ι) (x : cbS f i) :
    formalCompletion.basicOpenImmersion (cbK I f i) (hI.map _) x ≫
        formalCompletion.basicOpenImmersion I hI (f i) =
      formalCompletion.map hI ((hI.map _).map (algebraMap (cbS f i) (Localization.Away x)))
        (algebraMap R (Localization.Away x)) (le_of_eq (cbIdeal_eq I f i x)) := by
  rw [formalCompletion.basicOpenImmersion_eq_map (cbK I f i) (hI.map _) x,
    formalCompletion.basicOpenImmersion_eq_map I hI (f i),
    ← formalCompletion.map_comp I hI (hI.map _) ((hI.map _).map _)
      (algebraMap R (cbS f i)) (algebraMap (cbS f i) (Localization.Away x))
      (le_of_eq rfl) (le_of_eq rfl)]
  exact formalCompletion.map_congr hI _ _ _
    (IsScalarTower.algebraMap_eq R (cbS f i) (Localization.Away x)).symm

/-- The overlap `V i j`, included into the ambient completion `Spf R^`. -/
private abbrev cbV_toW (i j : ι) : cbV I hI f i j ⟶ cbW I hI :=
  cbFf I hI f i j ≫ (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom

/-- The triple overlap `V3 i j k`, included into the ambient completion `Spf R^`. -/
private abbrev cbV3_toW (i j k : ι) : cbV3 I hI f i j k ⟶ cbW I hI :=
  (formalCompletion.basicOpenImmersion (cbK I f i) (hI.map _)
      (cbg f i j * cbg f i k)).toLRSHom ≫
    (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom

private theorem cbV_toW_eq (i j : ι) :
    cbV_toW I hI f i j =
      (formalCompletion.map hI ((hI.map _).map (algebraMap (cbS f i) (cbT f i j)))
        (algebraMap R (cbT f i j)) (le_of_eq (cbIdeal_eq I f i (cbg f i j)))).toLRSHom :=
  congrArg FormalScheme.Hom.toLRSHom (cbChartComp I hI f i (cbg f i j))

private theorem cbV3_toW_eq (i j k : ι) :
    cbV3_toW I hI f i j k =
      (formalCompletion.map hI ((hI.map _).map (algebraMap (cbS f i) (cbT3 f i j k)))
        (algebraMap R (cbT3 f i j k))
        (le_of_eq (cbIdeal_eq I f i (cbg f i j * cbg f i k)))).toLRSHom :=
  congrArg FormalScheme.Hom.toLRSHom (cbChartComp I hI f i (cbg f i j * cbg f i k))

instance cbV_toW_mono (i j : ι) : Mono (cbV_toW I hI f i j) := inferInstance

/-- The ideal hypothesis of the double-overlap transition. -/
private theorem cbTau_ideal (i j : ι) :
    ((cbK I f j).map (algebraMap (cbS f j) (cbT f j i))).map (cbTau f i j) ≤
      (cbK I f i).map (algebraMap (cbS f i) (cbT f i j)) :=
  le_of_eq (by
    rw [← cbIdeal_eq I f j (cbg f j i), Ideal.map_map, cbTau_comp, cbIdeal_eq I f i (cbg f i j)])

/-- The ideal hypothesis of the triple-overlap transition. -/
private theorem cbSigma_ideal (i j k : ι) :
    ((cbK I f j).map (algebraMap (cbS f j) (cbT3 f j k i))).map (cbSigma f i j k) ≤
      (cbK I f i).map (algebraMap (cbS f i) (cbT3 f i j k)) :=
  le_of_eq (by
    rw [← cbIdeal_eq I f j (cbg f j k * cbg f j i), Ideal.map_map, cbSigma_comp,
      cbIdeal_eq I f i (cbg f i j * cbg f i k)])

/-- **The transition map of a double overlap**: `Spf ((R_{f i})_{f j})^ ≅ Spf ((R_{f j})_{f i})^`,
the completion functoriality of the canonical comparison of the two presentations of `R_{f i f j}`.
-/
private def cbT_map (i j : ι) : cbV I hI f i j ⟶ cbV I hI f j i :=
  (formalCompletion.map ((hI.map _).map _) ((hI.map _).map _) (cbTau f i j)
    (cbTau_ideal I f i j)).toLRSHom

/-- The transition map of a double overlap commutes with the inclusions into `Spf R^`. -/
private theorem cbT_map_comp (i j : ι) :
    cbT_map I hI f i j ≫ cbV_toW I hI f j i = cbV_toW I hI f i j := by
  rw [cbV_toW_eq, cbV_toW_eq]
  exact congrArg FormalScheme.Hom.toLRSHom
    (cbMapOverR I hI ((hI.map _).map _) ((hI.map _).map _)
      (le_of_eq (cbIdeal_eq I f j (cbg f j i))) (le_of_eq (cbIdeal_eq I f i (cbg f i j)))
      (cbTau f i j) (cbTau_ideal I f i j) (cbTau_comp f i j))

/-- The triple-overlap object, identified with the fibre product of two chart inclusions. -/
private abbrev cbO (i j k : ι) :
    cbV3 I hI f i j k ≅ pullback (cbFf I hI f i j) (cbFf I hI f i k) :=
  formalCompletion.basicOpenOverlapIso (cbK I f i) (hI.map _) (cbg f i j) (cbg f i k)

/-- **The transition map of a triple overlap.** -/
private def cbT'_map (i j k : ι) :
    pullback (cbFf I hI f i j) (cbFf I hI f i k) ⟶
      pullback (cbFf I hI f j k) (cbFf I hI f j i) :=
  (cbO I hI f i j k).inv ≫
    (formalCompletion.map ((hI.map _).map _) ((hI.map _).map _) (cbSigma f i j k)
      (cbSigma_ideal I f i j k)).toLRSHom ≫ (cbO I hI f j k i).hom

/-- The triple-overlap object, included into the ambient completion via the first projection. -/
private abbrev cbQ (i j k : ι) :
    pullback (cbFf I hI f i j) (cbFf I hI f i k) ⟶ cbW I hI :=
  pullback.fst (cbFf I hI f i j) (cbFf I hI f i k) ≫ cbV_toW I hI f i j

private theorem cbO_hom_comp_cbQ (i j k : ι) :
    (cbO I hI f i j k).hom ≫ cbQ I hI f i j k = cbV3_toW I hI f i j k :=
  formalCompletion.basicOpenOverlapIso_hom_fst_comp_assoc (cbK I f i) (hI.map _)
    (cbg f i j) (cbg f i k) _

private theorem cbQ_eq (i j k : ι) :
    cbQ I hI f i j k = (cbO I hI f i j k).inv ≫ cbV3_toW I hI f i j k := by
  rw [← cbO_hom_comp_cbQ, Iso.inv_hom_id_assoc]

private theorem cbO_hom_comp_snd (i j k : ι) :
    (cbO I hI f i j k).hom ≫
        (pullback.snd (cbFf I hI f i j) (cbFf I hI f i k) ≫ cbV_toW I hI f i k) =
      cbV3_toW I hI f i j k :=
  formalCompletion.basicOpenOverlapIso_hom_snd_comp_assoc (cbK I f i) (hI.map _)
    (cbg f i j) (cbg f i k) _

private theorem cbSigma_map_comp (i j k : ι) :
    (formalCompletion.map ((hI.map _).map _) ((hI.map _).map _) (cbSigma f i j k)
        (cbSigma_ideal I f i j k)).toLRSHom ≫ cbV3_toW I hI f j k i =
      cbV3_toW I hI f i j k := by
  rw [cbV3_toW_eq, cbV3_toW_eq]
  exact congrArg FormalScheme.Hom.toLRSHom
    (cbMapOverR I hI ((hI.map _).map _) ((hI.map _).map _)
      (le_of_eq (cbIdeal_eq I f j (cbg f j k * cbg f j i)))
      (le_of_eq (cbIdeal_eq I f i (cbg f i j * cbg f i k)))
      (cbSigma f i j k) (cbSigma_ideal I f i j k) (cbSigma_comp f i j k))

/-- **The triple-overlap transition commutes with the inclusion into `Spf R^`.** -/
private theorem cbT'_map_comp (i j k : ι) :
    cbT'_map I hI f i j k ≫ cbQ I hI f j k i = cbQ I hI f i j k := by
  rw [cbT'_map, Category.assoc, Category.assoc, cbO_hom_comp_cbQ, cbSigma_map_comp, cbQ_eq]

instance cbQ_mono (i j k : ι) : Mono (cbQ I hI f i j k) := by
  rw [cbQ_eq]
  exact mono_comp _ _

/-- **The arbitrary-index basic-open completion glue datum.** -/
def completionBasicOpenGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ι
  U := cbU I hI f
  V := fun i j _ => cbV I hI f i j
  f := fun i j _ => cbFf I hI f i j
  f_mono := fun i j _ => inferInstance
  f_hasPullback := fun i j k _ _ => inferInstance
  t := fun i j _ => cbT_map I hI f i j
  t' := fun i j k _ _ _ => cbT'_map I hI f i j k
  t_fac := fun i j k _ _ _ => by
    rw [← cancel_mono (cbV_toW I hI f j i), Category.assoc, Category.assoc,
      cbT_map_comp, cbT'_map, Category.assoc, Category.assoc, cbO_hom_comp_snd,
      cbSigma_map_comp, ← cbQ_eq]
  t_inv := fun i j _ => by
    rw [← cancel_mono (cbV_toW I hI f i j), Category.assoc, cbT_map_comp, cbT_map_comp,
      Category.id_comp]
  cocycle := fun i j k _ _ _ => by
    rw [← cancel_mono (cbQ I hI f i j k), Category.assoc, Category.assoc, cbT'_map_comp,
      cbT'_map_comp, cbT'_map_comp, Category.id_comp]

/-- **The arbitrary-index basic-open completion glue datum as a `LocallyRingedSpace.GlueData`**:
the full `CategoryTheory.GlueData` produced by `GlueData.ofGlueData'`, together with the
open-immersion field `f_open`. Off the diagonal each glue map is
`eqToHom ≫ (basic-open completion immersion)`, a composite of an isomorphism with an open
immersion; on the diagonal it is `eqToHom`, an isomorphism. -/
def completionBasicOpenLRSGlueData : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (completionBasicOpenGlueData' I hI f) with
    f_open := by
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · exact inferInstanceAs
          (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ cbFf I hI f i j)) }

/-- **The arbitrary-index basic-open completion glue datum as a `FormalScheme.GlueData`**: each
patch is a formal completion `formalCompletion R_{f i} (I·R_{f i})`, which is by construction the
affine formal scheme `Spf` of the completed ring, so the `isFormalScheme` field is witnessed by the
patch itself. -/
def completionBasicOpenFormalGlueData : FormalScheme.GlueData.{u} where
  toLocallyRingedSpaceGlueData := completionBasicOpenLRSGlueData I hI f
  isFormalScheme := fun i =>
    ⟨formalCompletion (cbS f i) (cbK I f i) (hI.map _), ⟨Iso.refl _⟩⟩

/-- **The glued basic-open completion**: the formal scheme obtained by gluing the completions of
the basic opens `D(f i) ⊆ Spec R` along their pairwise overlaps `D(f i · f j)`. -/
def completionBasicOpenGlued : FormalScheme.{u} :=
  (completionBasicOpenFormalGlueData I hI f).gluedFormalScheme

/-- The `i`-th chart as an open formal subscheme of the glued completion. -/
def completionBasicOpenι (i : ι) :
    (formalCompletion (Localization.Away (f i))
        (I.map (algebraMap R (Localization.Away (f i)))) (hI.map _)).toLocallyRingedSpace ⟶
      (completionBasicOpenGlued I hI f).toLocallyRingedSpace :=
  (completionBasicOpenFormalGlueData I hI f).ι i

instance completionBasicOpenι_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (completionBasicOpenι I hI f i) :=
  FormalScheme.GlueData.ι_isOpenImmersion _ _

/-- **The charts cover the glued completion**: every point of `completionBasicOpenGlued` lies in
the image of one of the basic-open completions. Together with the open-immersion instances this
exhibits the glued object as covered by affine formal charts. -/
theorem completionBasicOpenGlued_jointly_surjective
    (x : (completionBasicOpenGlued I hI f).toLocallyRingedSpace) :
    ∃ i : ι, x ∈ Set.range (completionBasicOpenι I hI f i).base := by
  obtain ⟨i, y, hy⟩ := (completionBasicOpenFormalGlueData I hI f).ι_jointly_surjective x
  exact ⟨i, y, hy⟩

/-- The glue condition of the multicoequalizer, for the family of basic-open chart inclusions. -/
private theorem cbGlueCondition (i j : ι) :
    (completionBasicOpenLRSGlueData I hI f).toGlueData.f i j ≫
        (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom =
      ((completionBasicOpenLRSGlueData I hI f).toGlueData.t i j ≫
          (completionBasicOpenLRSGlueData I hI f).toGlueData.f j i) ≫
        (formalCompletion.basicOpenImmersion I hI (f j)).toLRSHom := by
  simp only [completionBasicOpenLRSGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', completionBasicOpenGlueData']
  split_ifs with h
  · subst h; simp
  · simp only [dif_neg (Ne.symm h), Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    congr 1
    exact (cbT_map_comp I hI f i j).symm

/-- **The canonical morphism from the glued completion to `Spf R^`.** Each patch
`Spf (R_{f i})^` is a basic-open formal subscheme of `Spf R^`, and the transitions are compatible
with those inclusions (`cbT_map_comp`), so the family descends along the multicoequalizer that
defines the glued object. -/
def completionBasicOpenToCompletion :
    (completionBasicOpenGlued I hI f).toLocallyRingedSpace ⟶ cbW I hI :=
  Multicoequalizer.desc _ _
    (fun i => (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom) <| by
      rintro ⟨i, j⟩; exact cbGlueCondition I hI f i j

@[reassoc (attr := simp)]
theorem completionBasicOpenι_comp_toCompletion (i : ι) :
    completionBasicOpenι I hI f i ≫ completionBasicOpenToCompletion I hI f =
      (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom :=
  Multicoequalizer.π_desc _ _ _ _ _




/-! ### The two presentations of a double overlap

`completionBasicOpenGlueData'` presents the overlap of the `i`-th and `j`-th charts as
`Spf ((R_{f i})_{f j})^` — a basic open *of the chart ring*, which is what made the cocycle cheap.
`formalCompletion.basicOpenOverlapIso` presents it as `Spf (R_{f i · f j})^`, a basic open of the
*base* ring, and that is the presentation in which it is the fibre product of the two chart
immersions into `Spf R^`. Both are localizations of `R` away from `f i · f j`, so the comparison is
`IsLocalization.Away.lift`, exactly as `cbTau` and `cbSigma` were; the lemmas below identify the
two projections of the fibre product with the two glue maps of the datum.
-/

/-- The double-overlap ring `(R_{f i})_{f j}` is a localization of `R` away from `f i · f j`. -/
private theorem cbIsAway2 (i j : ι) : IsLocalization.Away (f i * f j) (cbT f i j) :=
  inferInstance

/-- **The comparison of the two presentations of a double overlap**, from the chart-ring
presentation to the base-ring one: `(R_{f i})_{f j} →+* R_{f i · f j}`. -/
private def cbNu (i j : ι) : cbT f i j →+* Localization.Away (f i * f j) :=
  haveI := cbIsAway2 f i j
  IsLocalization.Away.lift (S := cbT f i j) (f i * f j)
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f i * f j)) (f i * f j))

private theorem cbNu_comp (i j : ι) :
    (cbNu f i j).comp (algebraMap R (cbT f i j)) =
      algebraMap R (Localization.Away (f i * f j)) :=
  haveI := cbIsAway2 f i j
  IsLocalization.Away.lift_comp _ _

/-- The same comparison from the *other* chart's presentation: `(R_{f j})_{f i} →+* R_{f i · f j}`.
A separate declaration rather than `cbNu f j i`, whose target is `R_{f j · f i}` — a different type
even though the two elements are equal. -/
private def cbNu' (i j : ι) : cbT f j i →+* Localization.Away (f i * f j) :=
  haveI := cbAwayCongr (A := cbT f j i) (p := f j * f i) (q := f i * f j) (mul_comm _ _)
    (cbIsAway2 f j i)
  IsLocalization.Away.lift (S := cbT f j i) (f i * f j)
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f i * f j)) (f i * f j))

private theorem cbNu'_comp (i j : ι) :
    (cbNu' f i j).comp (algebraMap R (cbT f j i)) =
      algebraMap R (Localization.Away (f i * f j)) :=
  haveI := cbAwayCongr (A := cbT f j i) (p := f j * f i) (q := f i * f j) (mul_comm _ _)
    (cbIsAway2 f j i)
  IsLocalization.Away.lift_comp _ _

private theorem cbNu_ideal (i j : ι) :
    ((cbK I f i).map (algebraMap (cbS f i) (cbT f i j))).map (cbNu f i j) ≤
      I.map (algebraMap R (Localization.Away (f i * f j))) :=
  le_of_eq (by rw [← cbIdeal_eq I f i (cbg f i j), Ideal.map_map, cbNu_comp])

private theorem cbNu'_ideal (i j : ι) :
    ((cbK I f j).map (algebraMap (cbS f j) (cbT f j i))).map (cbNu' f i j) ≤
      I.map (algebraMap R (Localization.Away (f i * f j))) :=
  le_of_eq (by rw [← cbIdeal_eq I f j (cbg f j i), Ideal.map_map, cbNu'_comp])

/-- The double overlap in its base-ring presentation, `Spf (R_{f i · f j})^`. -/
private abbrev cbA (i j : ι) : LocallyRingedSpace.{u} :=
  (formalCompletion (Localization.Away (f i * f j))
    (I.map (algebraMap R (Localization.Away (f i * f j)))) (hI.map _)).toLocallyRingedSpace

/-- The comparison morphism `Spf (R_{f i · f j})^ ⟶ Spf ((R_{f i})_{f j})^`. -/
private def cbNu_map (i j : ι) : cbA I hI f i j ⟶ cbV I hI f i j :=
  (formalCompletion.map ((hI.map _).map _) (hI.map _) (cbNu f i j) (cbNu_ideal I f i j)).toLRSHom

/-- The comparison morphism `Spf (R_{f i · f j})^ ⟶ Spf ((R_{f j})_{f i})^`. -/
private def cbNu'_map (i j : ι) : cbA I hI f i j ⟶ cbV I hI f j i :=
  (formalCompletion.map ((hI.map _).map _) (hI.map _) (cbNu' f i j) (cbNu'_ideal I f i j)).toLRSHom

private theorem cbNu_map_comp (i j : ι) :
    cbNu_map I hI f i j ≫ cbV_toW I hI f i j =
      (formalCompletion.basicOpenImmersion I hI (f i * f j)).toLRSHom := by
  rw [cbV_toW_eq, formalCompletion.basicOpenImmersion_eq_map I hI (f i * f j)]
  exact congrArg FormalScheme.Hom.toLRSHom
    (cbMapOverR I hI ((hI.map _).map _) (hI.map _)
      (le_of_eq (cbIdeal_eq I f i (cbg f i j))) (le_of_eq rfl)
      (cbNu f i j) (cbNu_ideal I f i j) (cbNu_comp f i j))

private theorem cbNu'_map_comp (i j : ι) :
    cbNu'_map I hI f i j ≫ cbV_toW I hI f j i =
      (formalCompletion.basicOpenImmersion I hI (f i * f j)).toLRSHom := by
  rw [cbV_toW_eq, formalCompletion.basicOpenImmersion_eq_map I hI (f i * f j)]
  exact congrArg FormalScheme.Hom.toLRSHom
    (cbMapOverR I hI ((hI.map _).map _) (hI.map _)
      (le_of_eq (cbIdeal_eq I f j (cbg f j i))) (le_of_eq rfl)
      (cbNu' f i j) (cbNu'_ideal I f i j) (cbNu'_comp f i j))

/-- The transition of the glue datum is the comparison of the two chart-ring presentations. -/
private theorem cbNu_map_comp_cbT_map (i j : ι) :
    cbNu_map I hI f i j ≫ cbT_map I hI f i j = cbNu'_map I hI f i j := by
  rw [← cancel_mono (cbV_toW I hI f j i), Category.assoc, cbT_map_comp, cbNu_map_comp,
    cbNu'_map_comp]


/-! ### The fibre-product projections are the glue maps -/

private theorem cbOverlap_fst (i j : ι) :
    (formalCompletion.basicOpenOverlapIso I hI (f i) (f j)).hom ≫
        pullback.fst (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom
          (formalCompletion.basicOpenImmersion I hI (f j)).toLRSHom =
      cbNu_map I hI f i j ≫ cbFf I hI f i j := by
  rw [← cancel_mono (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom,
    Category.assoc, Category.assoc, formalCompletion.basicOpenOverlapIso_hom_fst_comp]
  exact (cbNu_map_comp I hI f i j).symm

private theorem cbOverlap_snd (i j : ι) :
    (formalCompletion.basicOpenOverlapIso I hI (f i) (f j)).hom ≫
        pullback.snd (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom
          (formalCompletion.basicOpenImmersion I hI (f j)).toLRSHom =
      cbNu'_map I hI f i j ≫ cbFf I hI f j i := by
  rw [← cancel_mono (formalCompletion.basicOpenImmersion I hI (f j)).toLRSHom,
    Category.assoc, Category.assoc, formalCompletion.basicOpenOverlapIso_hom_snd_comp]
  exact (cbNu'_map_comp I hI f i j).symm

private theorem cbGlueι (i j : ι) (hij : i ≠ j) :
    cbFf I hI f i j ≫ completionBasicOpenι I hI f i =
      cbT_map I hI f i j ≫ cbFf I hI f j i ≫ completionBasicOpenι I hI f j := by
  have h := ((completionBasicOpenLRSGlueData I hI f).toGlueData.glue_condition i j).symm
  simp only [completionBasicOpenLRSGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', completionBasicOpenGlueData', dif_neg hij,
    dif_neg (Ne.symm hij), Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp] at h
  exact (cancel_epi _).mp h


/-! ### The comparison is an isomorphism

Under the covering hypothesis the glued object *is* `formalCompletion R I`. The route is not a
`LocallyRingedSpace`-level replication of Mathlib's `Scheme.OpenCover.fromGlued` chain: that chain
is already on this tree, at exactly this generality, in
`FormalSchemes/OpenCoverGlueMorphisms.lean` (`FormalScheme.OpenCover.fromGlued`, and the
`IsIso` instance for it). What is built here is the inverse morphism, by gluing the chart
inclusions `completionBasicOpenι` along the basic-open cover of `Spf R^`; the two round trips are
then `Multicoequalizer.hom_ext` on one side and `OpenCover.hom_ext` on the other.
-/

/-- **The chart inclusions into the glued object agree on the fibre-product overlaps.** This is the
descent datum that `FormalScheme.OpenCover.glueMorphisms` consumes. Off the diagonal it is the
glue condition of `completionBasicOpenGlueData'`, transported along the identification of the
overlap's two presentations; on the diagonal the two projections of the fibre product of a
monomorphism with itself agree, so there is nothing to prove. -/
theorem completionBasicOpenι_pullback_comp (i j : ι) :
    pullback.fst (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom
          (formalCompletion.basicOpenImmersion I hI (f j)).toLRSHom ≫
        completionBasicOpenι I hI f i =
      pullback.snd (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom
          (formalCompletion.basicOpenImmersion I hI (f j)).toLRSHom ≫
        completionBasicOpenι I hI f j := by
  rcases eq_or_ne i j with rfl | hij
  · rw [(cancel_mono (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom).mp
      pullback.condition]
  · rw [← cancel_epi (formalCompletion.basicOpenOverlapIso I hI (f i) (f j)).hom,
      ← Category.assoc, ← Category.assoc, cbOverlap_fst, cbOverlap_snd, Category.assoc,
      Category.assoc, cbGlueι I hI f i j hij, ← cbNu_map_comp_cbT_map, Category.assoc]

/-- The images of the `f i` in the completion generate the unit ideal, if the `f i` do. -/
private theorem cbSpanAway (hcov : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range fun i => AdicCompletion.awayPoint I (f i)) = ⊤ := by
  rw [← Ideal.map_top (algebraMap R (AdicCompletion I R)), ← hcov, Ideal.map_span,
    ← Set.range_comp]
  rfl

set_option linter.style.setOption false in
-- The `covers` field compares a point of `(formalCompletion R I hI).toPresheafedSpace` with a
-- point of `FormalSpectrum (idealOfDefinition I)`; the two are `rfl` but not at `instances`
-- transparency, as `FormalSchemes/SpfBasicOpenCover.lean` records for the same field.
set_option backward.isDefEq.respectTransparency false in
/-- **The basic-open completions cover `Spf R^`** when the `f i` generate the unit ideal: the
`i`-th piece is `Spf (R_{f i})^`, included by `formalCompletion.basicOpenImmersion`. -/
def basicOpenCompletionCover (hcov : Ideal.span (Set.range f) = ⊤) :
    FormalScheme.OpenCover (formalCompletion R I hI) where
  J := ι
  obj i := formalCompletion (cbS f i) (cbK I f i) (hI.map _)
  map i := formalCompletion.basicOpenImmersion I hI (f i)
  f x := (FormalSpectrum.exists_mem_basicOpen_of_span_eq_top _ _ (cbSpanAway I f hcov) x).choose
  covers x :=
    (formalCompletion.range_basicOpenImmersion I hI _).ge
      (FormalSpectrum.exists_mem_basicOpen_of_span_eq_top _ _ (cbSpanAway I f hcov) x).choose_spec
  isOpenImmersion _ := inferInstance

@[simp]
theorem basicOpenCompletionCover_cmap (hcov : Ideal.span (Set.range f) = ⊤) (i : ι) :
    (basicOpenCompletionCover I hI f hcov).cmap i =
      (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom :=
  rfl


/-- **The inverse of the comparison morphism.** The chart inclusions `completionBasicOpenι` agree
on the fibre-product overlaps (`completionBasicOpenι_pullback_comp`), so they descend along the
basic-open cover of `Spf R^` to a single morphism into the glued object. -/
def completionFromCompletionBasicOpen (hcov : Ideal.span (Set.range f) = ⊤) :
    cbW I hI ⟶ (completionBasicOpenGlued I hI f).toLocallyRingedSpace :=
  (basicOpenCompletionCover I hI f hcov).glueMorphisms (completionBasicOpenι I hI f)
    (completionBasicOpenι_pullback_comp I hI f)

@[reassoc (attr := simp)]
theorem basicOpenImmersion_comp_completionFrom (hcov : Ideal.span (Set.range f) = ⊤) (i : ι) :
    (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom ≫
        completionFromCompletionBasicOpen I hI f hcov = completionBasicOpenι I hI f i :=
  (basicOpenCompletionCover I hI f hcov).map_glueMorphisms _ _ i

theorem completionBasicOpenToCompletion_comp_from (hcov : Ideal.span (Set.range f) = ⊤) :
    completionBasicOpenToCompletion I hI f ≫ completionFromCompletionBasicOpen I hI f hcov =
      𝟙 (completionBasicOpenGlued I hI f).toLocallyRingedSpace := by
  refine Multicoequalizer.hom_ext _ _ _ fun i => Eq.trans ?_ (Category.comp_id _).symm
  exact (completionBasicOpenι_comp_toCompletion_assoc I hI f i _).trans
    (basicOpenImmersion_comp_completionFrom I hI f hcov i)

theorem completionFrom_comp_toCompletion (hcov : Ideal.span (Set.range f) = ⊤) :
    completionFromCompletionBasicOpen I hI f hcov ≫ completionBasicOpenToCompletion I hI f =
      𝟙 (cbW I hI) := by
  refine (basicOpenCompletionCover I hI f hcov).hom_ext _ _
    fun i => Eq.trans ?_ (Category.comp_id _).symm
  exact (basicOpenImmersion_comp_completionFrom_assoc I hI f hcov i _).trans
    (completionBasicOpenι_comp_toCompletion I hI f i)

/-- **The glued basic-open completion is `formalCompletion R I`** (EGA I, 10.8): when the `f i`
generate the unit ideal, the canonical comparison is an isomorphism. This is the correctness check
on the cocycle: gluing the completions of the basic opens of one affine re-presents the completion
of that affine and nothing else. -/
theorem isIso_completionBasicOpenToCompletion (hcov : Ideal.span (Set.range f) = ⊤) :
    IsIso (completionBasicOpenToCompletion I hI f) :=
  ⟨completionFromCompletionBasicOpen I hI f hcov,
    completionBasicOpenToCompletion_comp_from I hI f hcov,
    completionFrom_comp_toCompletion I hI f hcov⟩

/-- **The isomorphism of formal schemes** `completionBasicOpenGlued ≅ formalCompletion R I`.
`FormalScheme.forgetToLocallyRingedSpace` is fully faithful, so this is
`isIso_completionBasicOpenToCompletion` repackaged; it is stated because a consumer wants the
formal-scheme isomorphism, not an `IsIso` on underlying spaces. -/
def completionBasicOpenGluedIso (hcov : Ideal.span (Set.range f) = ⊤) :
    completionBasicOpenGlued I hI f ≅ formalCompletion R I hI where
  hom := FormalScheme.Hom.mk (completionBasicOpenToCompletion I hI f)
  inv := FormalScheme.Hom.mk (completionFromCompletionBasicOpen I hI f hcov)
  hom_inv_id := FormalScheme.Hom.ext' (completionBasicOpenToCompletion_comp_from I hI f hcov)
  inv_hom_id := FormalScheme.Hom.ext' (completionFrom_comp_toCompletion I hI f hcov)

/-- **The isomorphism is compatible with the charts**: on the `i`-th patch it is the basic-open
completion immersion. Without this the isomorphism above would say only that the two objects are
abstractly isomorphic. -/
@[simp]
theorem completionBasicOpenι_comp_gluedIso (hcov : Ideal.span (Set.range f) = ⊤) (i : ι) :
    completionBasicOpenι I hI f i ≫ (completionBasicOpenGluedIso I hI f hcov).hom.toLRSHom =
      (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom :=
  completionBasicOpenι_comp_toCompletion I hI f i

/-- The inverse of the isomorphism restricted to the `i`-th basic open is the `i`-th chart. -/
@[simp]
theorem basicOpenImmersion_comp_gluedIso_inv (hcov : Ideal.span (Set.range f) = ⊤) (i : ι) :
    (formalCompletion.basicOpenImmersion I hI (f i)).toLRSHom ≫
        (completionBasicOpenGluedIso I hI f hcov).inv.toLRSHom =
      completionBasicOpenι I hI f i :=
  basicOpenImmersion_comp_completionFrom I hI f hcov i

end AlgebraicGeometry

end
