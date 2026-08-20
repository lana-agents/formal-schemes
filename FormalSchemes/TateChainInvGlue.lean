import FormalSchemes.TateChainStructMapInv

set_option linter.style.header false

/-!
# The Tate chain glued by the 𝔾m-inversion transition

The ℤ-indexed chain of formal annuli `T` (`FormalSchemes.TateChainGlue`) glues consecutive patches
`U_n = Spf A` along `{x invertible} ≅ {y invertible}` using `annulusChartTransitionSpf`, the
transition induced by the **coordinate swap** `x ↦ y`. The two-chart Tate curve model
`tateCurveModel` (`FormalSchemes.TateCurveModel`) was rerouted (issue 435 and its successors) onto
`annulusChartTransitionInvSpf`, the transition induced by the **𝔾m-inversion**. The chain was never
rerouted, so the two objects on master today are glued by *different* identifications of the same
overlap `Ĝm`, and neither `T ⟶ 𝔈_q` nor the quotient presentation `𝔈_q = T/q^ℤ` can be stated
while that is so.

This file builds the inversion-glued chain `T_inv`, additively and alongside the swap-glued `T`,
which is left untouched.

## The finding, formally

The first section records the discrepancy in Lean rather than in prose. Read in the coordinates of
the overlap `Ĝm` (`overlapEquiv : A{1/x}^ ≅ R{X, X⁻¹}`), the two candidate transitions transport
chart-1's coordinate `y` to *different* elements:

* `overlapEquiv_annulusOverlapTransitionInv_overlapY` — the swap gives `X`;
* `overlapEquiv_annulusOverlapInversion_symm_overlapY` (issue 436, on master) — the inversion gives
  `X⁻¹`.

So the swap is the **identity** on the overlap `Ĝm`, i.e. it glues `x_n = y_{n+1}`. That is the
gluing that makes the two-chart model the line with a doubled point rather than the Néron 2-gon,
and the argument is local to a single overlap, hence applies verbatim to a consecutive pair of
chain patches: the end `X → 0` of the overlap `Ĝm` limits to the node of `U_n` and to the node of
`U_{n+1}`, two distinct points of the glued chain. Under the inversion `x_n · y_{n+1} = 1` the two
nodes sit at the opposite ends `X → 0` and `X → ∞` of a genuine `ℙ¹`, and the pathology
disappears. `annulusOverlapTransitionInv_ne_inversion_symm` turns this into a formal
non-equality of the two ring maps, on the (necessary) hypothesis that `X ≠ X⁻¹` in `R{X, X⁻¹}`.

## What is built

Everything except the transition is shared with the swap chain: the patches `tcU`, the overlaps
`tateV`, the chart inclusions `tateF` and their open-immersion property are re-used verbatim from
`FormalSchemes.TateChainGlue`, since none of them mentions `t`. The triple-overlap fields are again
forced by initiality — the geometric input is that the triple overlap of any pairwise-distinct
triple is empty, which likewise does not mention `t`.

* `AlgebraicGeometry.tateTInv`: the transition `V(i, j) ⟶ V(j, i)`, built from
  `annulusChartTransitionInvSpf`.
* `AlgebraicGeometry.tateChainInvGlueData'`: the `CategoryTheory.GlueData'` of the chain.
* `AlgebraicGeometry.tateChainInvLRSGlueData`, `tateChainInvFormalGlueData`.
* `AlgebraicGeometry.tateChainInv`: the glued formal scheme `T_inv`.
* `AlgebraicGeometry.tateChainInvStructMap`: the structural morphism `T_inv ⟶ Spf R`, assembled by
  `glueMorphisms` from the per-patch `annulusStructMap`. Its adjacent-overlap obligation is the
  merged crux `annulusOverlapChart_comp_structMap_inv` (issue 440), which was built for the model
  and applies to the chain unchanged.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open RestrictedLaurentSeries

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The finding: the chain's transition is the identity on the overlap `Ĝm` -/

section Finding

variable (hI : I.FG)

/-- **The swap transition is the identity in `Ĝm` coordinates.** Transporting chart-1's coordinate
`y` back through the transition `annulusOverlapTransitionInv` that the *chain* glues by, and
reading the result through the crux identification `overlapEquiv`, gives `X` — the same coordinate
one started with. Contrast `overlapEquiv_annulusOverlapInversion_symm_overlapY`, the corresponding
statement for the transition the *model* glues by, which gives `X⁻¹`. -/
theorem overlapEquiv_annulusOverlapTransitionInv_overlapY :
    overlapEquiv R I q hI (annulusOverlapTransitionInv R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) (overlapY R I q))) =
      X R I 1 := by
  have hxy : (annulusOverlapTransition R I q hI).symm
      (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) (overlapY R I q)) =
        algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q) := by
    rw [RingEquiv.symm_apply_eq]
    exact (annulusOverlapTransition_overlapX R I q hI).symm
  rw [← annulusOverlapTransition_symm_apply, hxy, overlapEquiv_overlapX]

/-- **The two transitions are genuinely different maps.** Whenever `X ≠ X⁻¹` in the overlap
`R{X, X⁻¹}` — the hypothesis is needed, since over the zero ring every pair of maps agrees — the
transition the chain is glued by is not the transition the rerouted curve model is glued by. This
is the formal content of the finding of issue 606: the model fix of issue 435 never reached the
chain. The two maps are separated by their common witness, the image of chart-1's coordinate `y`
read in `Ĝm` coordinates. -/
theorem annulusOverlapTransitionInv_ne_inversion_symm (hne : X R I 1 ≠ X R I (-1)) :
    annulusOverlapTransitionInv R I q hI ≠
      ((annulusOverlapInversion R I q hI).symm :
        annulusOverlapY R I q →+* annulusOverlap R I q) := by
  intro h
  apply hne
  rw [← overlapEquiv_annulusOverlapTransitionInv_overlapY R I q hI,
    ← overlapEquiv_annulusOverlapInversion_symm_overlapY R I q hI]
  exact congrArg (overlapEquiv R I q hI) (congrFun (congrArg DFunLike.coe h) _)

end Finding

/-! ### The inversion-glued chain -/

/-- The transition `t i j : V(i, j) ⟶ V(j, i)` of the **inversion-glued** Tate chain: the geometric
𝔾m-inversion chart transition `annulusChartTransitionInvSpf : Spf A{1/x} ≅ Spf A{1/y}` forward
(`.hom`) and backward (`.inv`), the empty map otherwise. `Inv` analogue of `tateT`. -/
def tateTInv (hI : I.FG) (i j : ULift.{u} ℤ) : tateV R I q i j ⟶ tateV R I q j i :=
  if h1 : j.down - i.down = 1 then
    eqToHom (tateV_forward R I q h1) ≫ (annulusChartTransitionInvSpf R I q hI).hom ≫
      eqToHom (tateV_backward R I q (show i.down - j.down = -1 by omega)).symm
  else if h2 : j.down - i.down = -1 then
    eqToHom (tateV_backward R I q h2) ≫ (annulusChartTransitionInvSpf R I q hI).inv ≫
      eqToHom (tateV_forward R I q (show i.down - j.down = 1 by omega)).symm
  else
    eqToHom (tateV_far R I q h1 h2) ≫
      LocallyRingedSpace.emptyTo _ ≫
      eqToHom (tateV_far R I q (show i.down - j.down ≠ 1 by omega)
        (show i.down - j.down ≠ -1 by omega)).symm

theorem tateTInv_forward (hI : I.FG) {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    tateTInv R I q hI i j =
      eqToHom (tateV_forward R I q h) ≫ (annulusChartTransitionInvSpf R I q hI).hom ≫
        eqToHom (tateV_backward R I q (show i.down - j.down = -1 by omega)).symm := by
  simp only [tateTInv, dif_pos h]

theorem tateTInv_backward (hI : I.FG) {i j : ULift.{u} ℤ} (h : j.down - i.down = -1) :
    tateTInv R I q hI i j =
      eqToHom (tateV_backward R I q h) ≫ (annulusChartTransitionInvSpf R I q hI).inv ≫
        eqToHom (tateV_forward R I q (show i.down - j.down = 1 by omega)).symm := by
  have h1 : j.down - i.down ≠ 1 := by omega
  simp only [tateTInv, dif_neg h1, dif_pos h]

/-- The range of `f i j` on underlying spaces is unchanged by the `eqToHom` pre-composition.
(Duplicate of the private helper of `FormalSchemes.TateChainGlue`, kept here so that this file is
purely additive.) -/
private theorem range_eqToHom_comp {X Y Z : LocallyRingedSpace.{u}} (e : X = Y) (g : Y ⟶ Z) :
    Set.range (eqToHom e ≫ g).base = Set.range g.base := by
  subst e; simp

/-- The empty-source initial map has empty range. (Duplicate of the private helper of
`FormalSchemes.TateChainGlue`.) -/
private theorem range_emptyTo_empty (X : LocallyRingedSpace.{u}) :
    Set.range (LocallyRingedSpace.emptyTo X).base = ∅ := by
  rw [Set.range_eq_empty_iff]
  exact inferInstanceAs (IsEmpty (∅ : LocallyRingedSpace.{u}))

/-- **The legs of any pairwise-distinct triple overlap have disjoint ranges** — the geometric crux
of `FormalSchemes.TateOverlapDisjoint`, restated for the chain's inclusions. This depends only on
`tateF`, never on the transition, so it is the same statement for both chains. (Duplicate of the
private helper of `FormalSchemes.TateChainGlue`.) -/
private theorem tateF_range_disjoint (hq : q ∈ I) (hI : I.FG) {i j k : ULift.{u} ℤ}
    (hjk : j ≠ k) :
    Disjoint (Set.range (tateF R I q i j).base) (Set.range (tateF R I q i k).base) := by
  by_cases h1j : j.down - i.down = 1
  · by_cases h1k : k.down - i.down = 1
    · exact absurd (ULift.down_injective (show j.down = k.down by omega)) hjk
    · by_cases h2k : k.down - i.down = -1
      · rw [tateF_forward R I q h1j, tateF_backward R I q h2k,
          range_eqToHom_comp, range_eqToHom_comp]
        exact annulusOverlapChart_range_disjoint R I q hq hI
      · rw [tateF_far R I q h1k h2k, range_eqToHom_comp, range_emptyTo_empty]
        exact Set.disjoint_right.mpr fun a ha => ha.elim
  · by_cases h2j : j.down - i.down = -1
    · by_cases h1k : k.down - i.down = 1
      · rw [tateF_backward R I q h2j, tateF_forward R I q h1k,
          range_eqToHom_comp, range_eqToHom_comp]
        exact (annulusOverlapChart_range_disjoint R I q hq hI).symm
      · by_cases h2k : k.down - i.down = -1
        · exact absurd (ULift.down_injective (show j.down = k.down by omega)) hjk
        · rw [tateF_far R I q h1k h2k, range_eqToHom_comp, range_emptyTo_empty]
          exact Set.disjoint_right.mpr fun a ha => ha.elim
    · rw [tateF_far R I q h1j h2j, range_eqToHom_comp, range_emptyTo_empty]
      exact Set.disjoint_left.mpr fun a ha => ha.elim

/-- **The triple overlap of any pairwise-distinct triple is empty**, hence initial: the tool that
degenerates the cocycle fields. (Duplicate of the private helper of
`FormalSchemes.TateChainGlue`.) -/
private theorem isEmpty_tatePullback (hq : q ∈ I) (hI : I.FG) (i : ULift.{u} ℤ)
    {j k : ULift.{u} ℤ} (hjk : j ≠ k) [HasPullback (tateF R I q i j) (tateF R I q i k)] :
    IsEmpty (pullback (tateF R I q i j) (tateF R I q i k) : LocallyRingedSpace.{u}) :=
  LocallyRingedSpace.isEmpty_pullback _ _ (tateF_range_disjoint R I q hq hI hjk)

/-- **The ℤ-indexed glue datum of the Tate annulus chain, glued by the 𝔾m-inversion.** Identical to
`tateChainGlueData'` except in the field `t`, which is `tateTInv` in place of `tateT`; the
patches, the overlaps, the inclusions and the (initiality-forced) triple-overlap fields are the
same. -/
def tateChainInvGlueData' (hq : q ∈ I) (hI : I.FG) :
    CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} ℤ
  U := fun _ => locallyRingedSpaceObj (annulusIdealOfDefinition R I q)
  V := fun i j _ => tateV R I q i j
  f := fun i j _ => tateF R I q i j
  f_mono := fun i j _ => by haveI := tateF_isOpenImmersion R I q hI i j; infer_instance
  f_hasPullback := fun i j k _ _ =>
    haveI := tateF_isOpenImmersion R I q hI i j
    inferInstance
  t := fun i j _ => tateTInv R I q hI i j
  t' := fun i j k _ _ hjk => by
    haveI := tateF_isOpenImmersion R I q hI i j
    haveI := isEmpty_tatePullback R I q hq hI i hjk
    exact (LocallyRingedSpace.isInitialOfIsEmpty).to _
  t_fac := fun i j k _ _ hjk => by
    haveI := tateF_isOpenImmersion R I q hI i j
    haveI := isEmpty_tatePullback R I q hq hI i hjk
    exact (LocallyRingedSpace.isInitialOfIsEmpty).hom_ext _ _
  t_inv := fun i j hij => by
    by_cases h1 : j.down - i.down = 1
    · have h2j : i.down - j.down = -1 := by omega
      rw [tateTInv, dif_pos h1, tateTInv, dif_neg (show i.down - j.down ≠ 1 by omega), dif_pos h2j]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
        Iso.hom_inv_id_assoc, eqToHom_trans_assoc]
    · by_cases h2 : j.down - i.down = -1
      · have h1j : i.down - j.down = 1 := by omega
        rw [tateTInv, dif_neg h1, dif_pos h2, tateTInv, dif_pos h1j]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
          Iso.inv_hom_id_assoc, eqToHom_trans_assoc]
      · rw [tateTInv, dif_neg h1, dif_neg h2]
        haveI : IsEmpty (tateV R I q i j) := (tateV_far R I q h1 h2) ▸ inferInstance
        exact (LocallyRingedSpace.isInitialOfIsEmpty (X := tateV R I q i j)).hom_ext _ _
  cocycle := fun i j k _ _ hjk => by
    haveI := tateF_isOpenImmersion R I q hI i j
    haveI := isEmpty_tatePullback R I q hq hI i hjk
    exact (LocallyRingedSpace.isInitialOfIsEmpty).hom_ext _ _

/-- **The inversion-glued Tate chain datum as a `LocallyRingedSpace.GlueData`.** The `f_open` field
is verified exactly as for the swap chain: off the diagonal each glue map is `eqToHom ≫ (chart or
empty map)`, on the diagonal it is `eqToHom`. -/
def tateChainInvLRSGlueData (hq : q ∈ I) (hI : I.FG) : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (tateChainInvGlueData' R I q hq hI) with
    f_open := by
      haveI hoi : ∀ a b : ULift.{u} ℤ, LocallyRingedSpace.IsOpenImmersion (tateF R I q a b) :=
        tateF_isOpenImmersion R I q hI
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ tateF R I q i j)) }

/-- **The inversion-glued Tate chain datum as a `FormalScheme.GlueData`**: each patch is the affine
formal scheme `Spf A`. -/
def tateChainInvFormalGlueData (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] :
    FormalScheme.GlueData.{u} :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  { toLocallyRingedSpaceGlueData := tateChainInvLRSGlueData R I q hq hI
    isFormalScheme := fun _ =>
      ⟨FormalScheme.Spf (annulusIdealOfDefinition R I q), ⟨Iso.refl _⟩⟩ }

/-- **The formal Tate chain `T_inv`, glued by the 𝔾m-inversion.** The ℤ-indexed chain of formal
annuli `Spf A` glued along `x_n · y_{n+1} = 1` — the identification the rerouted `tateCurveModel`
uses, so that `T_inv` (and not the swap-glued `tateChain`) is the object that can carry the
quotient presentation `𝔈_q = T/q^ℤ`. -/
def tateChainInv (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] : FormalScheme.{u} :=
  (tateChainInvFormalGlueData R I q hq hI).gluedFormalScheme

/-- **The glued structural morphism of the inversion-glued Tate chain** `T_inv ⟶ Spf R`, assembled
from the per-patch `annulusStructMap : Spf A ⟶ Spf R` by `glueMorphisms`. The overlap compatibility
cases exactly as for the swap chain, except that the adjacent-overlap steps are discharged by the
inversion cruxes `annulusOverlapChart_comp_structMap_inv` /
`annulusOverlapChartY_comp_structMap_inv` (issue 440), which were proved for the rerouted model and
apply here unchanged. -/
def tateChainInvStructMap [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) :
    (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  (tateChainInvFormalGlueData R I q hq hI).glueMorphisms (fun _ => annulusStructMap R I q hI) (by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · have hij' : ¬ @Eq (ULift.{u} ℤ) i j := hij
      have hji' : ¬ @Eq (ULift.{u} ℤ) j i := fun h => hij h.symm
      simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij',
        dif_neg hji', Category.assoc]
      by_cases h1 : j.down - i.down = 1
      · rw [tateF_forward R I q h1, tateTInv, dif_pos h1,
          tateF_backward R I q (show i.down - j.down = -1 by omega)]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [annulusOverlapChart_comp_structMap_inv R I q hI]
      · by_cases h2 : j.down - i.down = -1
        · rw [tateF_backward R I q h2, tateTInv, dif_neg h1, dif_pos h2,
            tateF_forward R I q (show i.down - j.down = 1 by omega)]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [annulusOverlapChartY_comp_structMap_inv R I q hI]
        · haveI : IsEmpty (tateV R I q i j) := (tateV_far R I q h1 h2) ▸ inferInstance
          simp only [eqToHom_trans_assoc]
          congr 1
          exact (LocallyRingedSpace.isInitialOfIsEmpty (X := tateV R I q i j)).hom_ext _ _)

end AlgebraicGeometry
