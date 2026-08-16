import FormalSchemes.CoproductOpenImmersion
import FormalSchemes.TateChainStructMap
import FormalSchemes.TateChainStructMapInv
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# The Tate curve formal model `𝔈_q = T/q^ℤ` as a two-chart circular quotient

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter `q ∈ I`,
and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus with ideal of
definition `I·A`. The **Tate curve** `𝔈_q = T/q^ℤ` is the quotient of the formal torus by the
multiplicative `q^ℤ`-action; as a *compact* (proper) formal `R`-curve it is obtained by gluing
finitely many copies of the annulus in a **circle**. This file delivers the smallest such circular
model: the **two-chart circular quotient**.

## The two-chart circular model

Two copies `U₀ = U₁ = Spf A` of the formal annulus are glued along their overlap in **two** places
at once — this is what makes the resulting formal scheme *circular* (compact), in contrast to the
open two-patch prototype `tateTwoPatch` (`FormalSchemes.TateGlueTwoPatch`), where the two patches
meet in a single overlap and the result is an open (contractible) piece of the chain.

Concretely, the overlap object is the **binary coproduct**

`V = Spf A{1/x} ⨿ Spf A{1/y}`

— the disjoint union of the two formal-`Ĝm` annuli. The combined overlap chart into a patch `Spf A`
is `coprod.desc annulusOverlapChart annulusOverlapChartY`, sending the `x`-summand to the locus
`D(x)` and the `y`-summand to the locus `D(y)`; these two loci are disjoint
(`annulusOverlapChart_range_disjoint`), so the combined chart is an open immersion
(`LocallyRingedSpace.IsOpenImmersion.coprodDesc`). The transition datum `t` glues the two summands
by the genuine **𝔾m-inversion** transition: the `x`-summand is carried by
`annulusChartTransitionInvSpf.hom` (the coordinate inversion `X ↦ Y⁻¹`, realising the locus
`x₀·y₁ = 1` of the Néron 2-gon) into the `y`-summand and the `y`-summand is carried by its inverse
into the `x`-summand. This is the model correction of issue 435: gluing by the inversion rather than
the coordinate-swap `annulusChartTransitionSpf` (which would yield the *non-separated*
line-with-doubled-origin) makes `𝔈_q` a genuinely separated (compact) formal curve. The transition
is manifestly direction-independent and self-inverse, so on the two-element index type `ULift Bool`
the fields `t'`, `t_fac`, `cocycle` remain **vacuous** (no triple of `Bool`-indices is pairwise
distinct), exactly as in the open prototype.

## Main definitions

* `AlgebraicGeometry.tateCurveGlueData'`: the `CategoryTheory.GlueData' LocallyRingedSpace` value
  assembling the two annulus copies and their coproduct overlap datum, glued by the 𝔾m-inversion
transition.
* `AlgebraicGeometry.tateCurveLRSGlueData`: the induced
  `AlgebraicGeometry.LocallyRingedSpace.GlueData`.
* `AlgebraicGeometry.tateCurveFormalGlueData`: the `AlgebraicGeometry.FormalScheme.GlueData`, each
  piece being the affine formal scheme `Spf A`.
* `AlgebraicGeometry.tateCurveModel`: **the headline object `𝔈_q`** — the glued (non-affine) formal
  scheme obtained by gluing two copies of `Spf A` along the coproduct overlap in two places.
* `AlgebraicGeometry.tateCurveModelStructMap`: the glued structural morphism `𝔈_q ⟶ Spf R` over the
  base, assembled from the per-patch structural morphisms `annulusStructMap`.

## What is delivered vs. what remains

Delivered: the circular glue datum at all three levels (`GlueData'`, `LocallyRingedSpace.GlueData`,
`FormalScheme.GlueData`), glued by the 𝔾m-inversion transition (issue 435 model fix), the glued
formal scheme `tateCurveModel`, and the structural morphism `tateCurveModelStructMap : 𝔈_q ⟶ Spf R`
over the base. With the inversion gluing in place, `𝔈_q` is the correct *separated* (compact) formal
curve; the closed-immersion diagonal witnessing separatedness (which distinguishes the circular
model from the open chain) is assembled downstream (issues 238/375/411) and is **not** proved here.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The annulus object `Spf A`, the two patches to be glued. -/
private abbrev tpU : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (annulusIdealOfDefinition R I q)

/-- The `x`-overlap `Spf A{1/x}` (the left coproduct summand of the overlap). -/
private abbrev tpVx : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))

/-- The `y`-overlap `Spf A{1/y}` (the right coproduct summand of the overlap). -/
private abbrev tpVy : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))

/-- On a two-element index type no triple is pairwise distinct: this discharges the vacuous
`t'`, `t_fac` and `cocycle` fields of the two-chart glue data. -/
private theorem tcBool_not_pairwise_distinct {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

/-- **The combined overlap chart is an open immersion.** The coproduct `coprod.desc` of the two
affine overlap charts `annulusOverlapChart` (image `D(x)`) and `annulusOverlapChartY` (image `D(y)`)
is an open immersion of locally ringed spaces, because the two images are disjoint. -/
theorem isOpenImmersion_tateCurveOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion
      (coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q)) := by
  haveI := isOpenImmersion_annulusOverlapChart R I q hI
  haveI := isOpenImmersion_annulusOverlapChartY R I q hI
  exact LocallyRingedSpace.IsOpenImmersion.coprodDesc (annulusOverlapChart R I q)
    (annulusOverlapChartY R I q) (annulusOverlapChart_range_disjoint R I q hq hI)

/-- **The two-chart circular glue datum** of the Tate curve, as a `CategoryTheory.GlueData'` on the
index type `ULift Bool`: two copies of `Spf A` glued along the coproduct overlap
`Spf A{1/x} ⨿ Spf A{1/y}` in two places, via the 𝔾m-inversion transition
`annulusChartTransitionInvSpf` (issue 435 model fix, `X ↦ Y⁻¹`). The three fields `t'`, `t_fac`,
`cocycle` are vacuous because no triple of `Bool`-indices is pairwise distinct. -/
def tateCurveGlueData' (hq : q ∈ I) (hI : I.FG) :
    CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} Bool
  U := fun _ => tpU R I q
  V := fun _ _ _ => tpVx R I q ⨿ tpVy R I q
  f := fun _ _ _ => coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q)
  f_mono := by
    haveI := isOpenImmersion_tateCurveOverlapChart R I q hq hI
    intro i j h
    exact inferInstanceAs (Mono (coprod.desc (annulusOverlapChart R I q)
      (annulusOverlapChartY R I q)))
  f_hasPullback := by
    haveI := isOpenImmersion_tateCurveOverlapChart R I q hq hI
    intro i j k hij hik
    exact inferInstanceAs (HasPullback
      (coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q))
      (coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q)))
  t := fun _ _ _ => coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
    ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl)
  t' := fun _ _ _ hij hik hjk => (tcBool_not_pairwise_distinct hij hik hjk).elim
  t_fac := fun _ _ _ hij hik hjk => (tcBool_not_pairwise_distinct hij hik hjk).elim
  t_inv := by
    intro i j h
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  cocycle := fun _ _ _ hij hik hjk => (tcBool_not_pairwise_distinct hij hik hjk).elim

/-- **The circular glue datum as a `LocallyRingedSpace.GlueData`**: the full
`CategoryTheory.GlueData` produced by `GlueData.ofGlueData'`, together with the open-immersion field
`f_open`. Off the diagonal each glue map is `eqToHom ≫ (combined overlap chart)`, a composite of an
isomorphism with an open immersion; on the diagonal it is `eqToHom`, an isomorphism. -/
def tateCurveLRSGlueData (hq : q ∈ I) (hI : I.FG) : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (tateCurveGlueData' R I q hq hI) with
    f_open := by
      haveI := isOpenImmersion_tateCurveOverlapChart R I q hq hI
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q))) }

/-- **The circular glue datum as a `FormalScheme.GlueData`**: each of the two pieces is the affine
formal scheme `Spf A`, whose underlying locally ringed space is definitionally the object
`locallyRingedSpaceObj (I·A)` used as a patch. -/
def tateCurveFormalGlueData (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] :
    FormalScheme.GlueData.{u} :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  { toLocallyRingedSpaceGlueData := tateCurveLRSGlueData R I q hq hI
    isFormalScheme := fun _ =>
      ⟨FormalScheme.Spf (annulusIdealOfDefinition R I q), ⟨Iso.refl _⟩⟩ }

/-- **The Tate curve formal model `𝔈_q = T/q^ℤ`** (two-chart circular model): the (non-affine,
compact) formal scheme obtained by gluing two copies of the formal Tate annulus `Spf A` along the
coproduct overlap `Spf A{1/x} ⨿ Spf A{1/y}` in two places. This is the headline object of this
file. -/
def tateCurveModel (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] : FormalScheme.{u} :=
  (tateCurveFormalGlueData R I q hq hI).gluedFormalScheme

/-- **The glued structural morphism of the Tate curve model** `𝔈_q ⟶ Spf R`, assembled from the
per-patch structural morphisms `annulusStructMap : Spf A ⟶ Spf R` via `glueMorphisms`. The overlap
compatibility is verified by casing on whether the two indices coincide: on the diagonal the
transition `t` is the identity so both sides collapse to `annulusStructMap`; off the diagonal the
overlap is the coproduct `Spf A{1/x} ⨿ Spf A{1/y}`, and the obligation is checked summandwise by
`coprod.hom_ext`, landing on the two geometric crux identities for the 𝔾m-inversion gluing
`annulusOverlapChart_comp_structMap_inv` (the `x`-summand) and
`annulusOverlapChartY_comp_structMap_inv` (the `y`-summand). -/
def tateCurveModelStructMap [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) :
    (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  (tateCurveFormalGlueData R I q hq hI).glueMorphisms (fun _ => annulusStructMap R I q hI) (by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · have hij' : ¬ @Eq (ULift.{u} Bool) i j := hij
      have hji' : ¬ @Eq (ULift.{u} Bool) j i := fun h => hij h.symm
      simp only [tateCurveFormalGlueData, tateCurveLRSGlueData, tateCurveGlueData',
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij',
        dif_neg hji', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      congr 1
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc, Category.assoc,
          coprod.inr_desc_assoc]
        exact annulusOverlapChart_comp_structMap_inv R I q hI
      · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc, Category.assoc,
          coprod.inl_desc_assoc]
        exact annulusOverlapChartY_comp_structMap_inv R I q hI)

end AlgebraicGeometry
