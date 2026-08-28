import FormalSchemes.CompletionBasicOpenOverlap
import FormalSchemes.CompletionBasicOpenMap
import FormalSchemes.Gluing

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

## What this is a slice of

Gluing the basic opens of a single affine `Spec R` back together only re-presents
`formalCompletion R I`. That is the point of taking this case first: it is the smallest situation
in which the cocycle condition has content, and it comes with a checkable conclusion. Two things
are deliberately not here.

* **That `completionBasicOpenToCompletion` is an isomorphism** when the `f i` generate the unit
  ideal. The comparison morphism is built here; that it is invertible is not. Mathlib's route to
  a statement of this shape is `AlgebraicGeometry.Scheme.OpenCover.fromGlued` together with
  `isOpenMap_fromGlued`, `fromGlued_injective` and `instance : IsIso 𝒰.fromGlued`
  (`Mathlib/AlgebraicGeometry/Gluing.lean`), and every one of those is stated for `Scheme`, keyed
  on `Scheme.OpenCover`. `Spf R^` is not a scheme, so they do not apply and a
  `LocallyRingedSpace`-level replication of `Gluing.lean:262-423` is needed. That is issue 1123,
  which starts from `completionBasicOpenToCompletion` rather than from nothing.
* **Different charts at an arbitrary index** — an arbitrary affine cover of an arbitrary scheme,
  completed along a closed subset — which is the rest of EGA I, 10.8. This file supplies the
  triple-overlap bookkeeping that case needs; what it does not supply is the second ring and the
  overlap identification `θ` that `FormalSchemes/CompletionGlueTwoPatch.lean` carries.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) {ι : Type u} (f : ι → R)

/-- `formalCompletion.map` depends on its ring homomorphism only through its value. -/
private theorem cbMapCongr {S : Type u} [CommRing S] {J : Ideal S} (hJ : J.FG)
    {φ ψ : R →+* S} (hφ : I.map φ ≤ J) (hψ : I.map ψ ≤ J) (h : φ = ψ) :
    formalCompletion.map hI hJ φ hφ = formalCompletion.map hI hJ ψ hψ := by
  subst h; rfl

/-- A morphism of completions induced by a ring map **over `R`** commutes with the two structure
morphisms down to `formalCompletion R I`. -/
private theorem cbMapOverR {T T' : Type u} [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']
    {L : Ideal T} {L' : Ideal T'} (hL : L.FG) (hL' : L'.FG)
    (hTL : I.map (algebraMap R T) ≤ L) (hT'L' : I.map (algebraMap R T') ≤ L')
    (φ : T →+* T') (hLL : L.map φ ≤ L') (hφ : φ.comp (algebraMap R T) = algebraMap R T') :
    formalCompletion.map hL hL' φ hLL ≫ formalCompletion.map hI hL (algebraMap R T) hTL =
      formalCompletion.map hI hL' (algebraMap R T') hT'L' := by
  rw [← formalCompletion.map_comp I hI hL hL' (algebraMap R T) φ hTL hLL]
  exact cbMapCongr I hI hL' _ _ hφ

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
  exact cbMapCongr I hI _ _ _ (IsScalarTower.algebraMap_eq R (cbS f i) (Localization.Away x)).symm

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

end AlgebraicGeometry

end
