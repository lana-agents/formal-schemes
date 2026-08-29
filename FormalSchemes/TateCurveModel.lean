import FormalSchemes.CoproductOpenImmersion
import FormalSchemes.TateChainStructMap
import FormalSchemes.TateChainStructMapInv
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# The Tate curve formal model as a two-chart circular quotient

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter `q ∈ I`,
and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus with ideal of
definition `I·A`. A **Tate curve** is a quotient of the formal torus by a multiplicative
`p^ℤ`-action; as a *compact* (proper) formal `R`-curve it is obtained by gluing finitely many
copies of the annulus in a **circle**. This file delivers the smallest such circular model: the
**two-chart circular quotient** `tateCurveModel R I q`.

## Its period is `q²`, not `q` — read this before using it

`tateCurveModel R I q` is the formal model of the Tate curve **of period `q²`**. The parameter `q`
it is built from is a *square root* of the period, not the period. Throughout the tree the symbol
`𝔈_q` denotes this object, i.e. `𝔈_q := tateCurveModel R I q`; it should **not** be read as "the
Tate curve of period `q`", which would be `T_inv/⟨σ⟩` for `σ` the one-patch shift.

Two independent derivations, both short enough to redo on paper:

**1. One patch shift = multiplication by `q`.** On patch `n` the annulus relation gives
`x_n · y_n = q`. Since the issue-435 reroute, consecutive patches are glued by the 𝔾m-**inversion**
`annulusChartTransitionInvSpf`, i.e. by `x_n · y_{n+1} = 1` (`x ↦ y⁻¹`; see
`FormalSchemes.TateOverlapInversion`). Combining,

```
x_{n+1} = q / y_{n+1} = q · x_n ,
```

so the one-patch shift `σ` acts on the generic-fibre coordinate as multiplication by `q`. Hence
`T_inv/⟨σ⟩ = 𝔾ₘ/q^ℤ = E_q`, whereas `T_inv/⟨σ²⟩ = 𝔾ₘ/q^{2ℤ} = E_{q²}`.

Now, `tateCurveModel` glues its two patches `U₀`, `U₁` along **both** overlaps at once —
`D(x₀) ≅ D(y₁)` *and* `D(y₀) ≅ D(x₁)` — so `U₁` is simultaneously the patch after `U₀` and the
patch before it. That is exactly the chain modulo `σ²`. Hence period `q²`.

**2. Component count.** On the special fibre each patch is `Spec R̄[x, y]/(x·y)`, two lines meeting
at a node, and the inversion gluing joins `L_x^{(n)}` to `L_y^{(n+1)}` into a single `ℙ¹`. With two
patches identified modulo `σ²` this leaves **two** components and **two** nodes: a Néron 2-gon. A
`v(q)`-gon is the reduction of `E_q`, so over a base with `v(q) = 1` a 2-gon is `E_{q²}`.

The discrepancy only appeared after the 435 reroute: under the old coordinate-*swap* gluing the
object was not a Tate curve at all, so the earlier naming was not right either — it was differently
wrong. The construction is deliberately left as it is: re-parameterising by a square root of `q`
would change the signature of every Tate declaration in the tree for no mathematical gain.

**The `σ²` object is what the quotient criterion reaches, and `σ` is not.** One might expect the
period-`q` model `T_inv/⟨σ⟩` to be available too, now that
`AlgebraicGeometry.LocallyRingedSpace.freeActionQuotientFormalScheme` builds quotients with no glue
datum at all. It is not: that theorem needs a **free, properly discontinuous** action, and
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) shows `σ` fails that as soon as `I ≠ ⊤`. A node of the
special fibre has no separating neighbourhood: `σ` exchanges the two branches through it, and each
branch's generic point lies in *every* neighbourhood of the node. The square action escapes this
because `σ²` moves a patch clear of its neighbours
(`AlgebraicGeometry.tateInvPeriodSq_isFreeProperlyDiscontinuous`). So `E_q` is not reachable as a
formal model *by this route*. Whether some other route reaches it is open — that criterion is
sufficient, not necessary — but the question is now localised:
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) makes `T_inv/⟨σ⟩` a formal scheme as soon as the
images of a *single* patch's node locus carry affine charts, every other point of the quotient
having one already. In the literature `E_q` is formed on the rigid generic fibre.

Consequence for the quotient presentation (issue 224): `𝔈_q = T_inv/⟨σ²⟩`, so the acting map is
`n ↦ tateInvShiftAut ^ (2 * n)`, **not** `tateInvPeriodAction`.

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
(`LocallyRingedSpace.IsOpenImmersion.coprodDesc`). The transition datum `t` is the **𝔾m-inversion**
`x₀·y₁ = 1` (`X ↦ Y⁻¹`, the geometrically correct Néron 2-gon gluing that makes `𝔈_q` *separated*):
the `x`-summand is carried by the geometric inversion transition `annulusChartTransitionInvSpf.hom`
into the `y`-summand and the `y`-summand is carried by its inverse into the `x`-summand. This
transition is manifestly direction-independent and self-inverse, so on the two-element index type
`ULift Bool`
the fields `t'`, `t_fac`, `cocycle` remain **vacuous** (no triple of `Bool`-indices is pairwise
distinct), exactly as in the open prototype.

## Main definitions

* `AlgebraicGeometry.tateCurveGlueData'`: the `CategoryTheory.GlueData' LocallyRingedSpace` value
  assembling the two annulus copies and their coproduct overlap datum.
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
`FormalScheme.GlueData`), the glued formal scheme `tateCurveModel`, and the structural morphism
`tateCurveModelStructMap : 𝔈_q ⟶ Spf R` over the base. Separatedness/properness of `𝔈_q` (which
exhibits it as a genuinely *compact* formal curve, the geometric content distinguishing the circular
model from the open chain) is **not** proved here and remains a documented follow-up.

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
`Spf A{1/x} ⨿ Spf A{1/y}` in two places, via the 𝔾m-inversion transition (`x₀·y₁ = 1`). The three
fields `t'`, `t_fac`, `cocycle` are vacuous because no triple of `Bool`-indices is pairwise
distinct. -/
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

/-- **The Tate curve formal model `𝔈_q`** (two-chart circular model): the (non-affine, compact)
formal scheme obtained by gluing two copies of the formal Tate annulus `Spf A` along the coproduct
overlap `Spf A{1/x} ⨿ Spf A{1/y}` in two places. This is the headline object of this file.

**Its period is `q²`, not `q`**: gluing along both overlaps identifies the chain modulo the
*square* of the one-patch shift, and the one-patch shift is multiplication by `q`. So
`𝔈_q = T_inv/⟨σ²⟩ = E_{q²}`, and the parameter `q` is a square root of the period. The module
docstring carries both derivations. -/
def tateCurveModel (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] : FormalScheme.{u} :=
  (tateCurveFormalGlueData R I q hq hI).gluedFormalScheme

/-- **The glued structural morphism of the Tate curve model** `𝔈_q ⟶ Spf R`, assembled from the
per-patch structural morphisms `annulusStructMap : Spf A ⟶ Spf R` via `glueMorphisms`. The overlap
compatibility is verified by casing on whether the two indices coincide: on the diagonal the
transition `t` is the identity so both sides collapse to `annulusStructMap`; off the diagonal the
overlap is the coproduct `Spf A{1/x} ⨿ Spf A{1/y}`, and the obligation is checked summandwise by
`coprod.hom_ext`, landing on the two geometric crux identities
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
