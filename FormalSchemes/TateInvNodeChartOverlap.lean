import FormalSchemes.TateInvNodeChartGlue
import FormalSchemes.GlueDataOverlapCompat

set_option linter.style.header false

/-!
# The overlap condition on the Tate chain, as a condition on one section of one patch

`FormalSchemes.TateInvNodeChartGlue` proved that a section `s` of the model patch `Spf A` over
`AlgebraicGeometry.tateInvPatchSaturateOpens` extends to a section of the chain over the saturation
**iff** its constant family is compatible
(`AlgebraicGeometry.exists_tateInvConstFamily_iff_isCompatible`), and that any such extension is
automatically `σ`-invariant (`AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`). The
compatibility there is `TopCat.Presheaf.IsCompatible`: a condition on the *glued* space, stated for
the transported family. It names no map of the chain and no open of `Spf A`.

`FormalSchemes.GlueDataOverlapCompat` translates that condition, for an arbitrary glue datum, into
one on the datum's own overlaps. This file instantiates the translation at the chain, and then
removes the last trace of the chain from it: because every patch pulls the saturation back to the
same open (`AlgebraicGeometry.map_ι_tateInvSaturateOpens`), the constant family's two restrictions
to `V (i, j)` are the two restrictions of the **single** section `s`, and the condition becomes

> for every pair `i j`, the two legs `f i j` and `t i j ≫ f j i` out of the overlap `V (i, j)`
> carry `s` to the same section.

That is `AlgebraicGeometry.IsTateInvOverlapCompatible`: a statement about `s`, the patch, and the
chain's transition data alone. Nothing about `T_inv`, its topology, or the quotient occurs in it.

## What is here

* `AlgebraicGeometry.map_f_tateInvPatchSaturateOpens`: the two legs pull
  `tateInvPatchSaturateOpens` back to the same open of `V (i, j)` — the equality that makes the
  condition a statement about two sections of one ring.
* `AlgebraicGeometry.c_app_tateInvConstFamily`: pulling the constant family back along any morphism
  into the patch is pulling `s` back and transporting. This is where the family's independence of
  the index is used, and it is used for both legs at once.
* `AlgebraicGeometry.IsTateInvOverlapCompatible`: **the condition on `s`.**
* `AlgebraicGeometry.isOverlapCompatible_tateInvConstFamily_iff`: it is the general overlap
  condition of `AlgebraicGeometry.FormalScheme.GlueData.IsOverlapCompatible` at the constant
  family.
* `AlgebraicGeometry.exists_tateInvConstFamily_iff_tateInvOverlapCompatible` and
  `AlgebraicGeometry.existsUnique_tateInvConstFamily_of_tateInvOverlapCompatible`: hence `s`
  extends to a section of the chain over `W` exactly when it satisfies the condition, and then the
  extension is unique.
* `AlgebraicGeometry.exists_tateInvShiftAut_zpow_invariant_of_tateInvOverlapCompatible`: **the
  application.** Combined with the invariance of `FormalSchemes.TateInvNodeChartGlue`, a section of
  the patch satisfying the condition produces a `σ`-invariant section of the chain over the
  saturation.

## What is left

The condition still quantifies over **all** pairs `i j`, and it is stated in the glue datum's
morphisms rather than in the chain's charts. Two reductions are available and neither is attempted
here.

* **Only the diagonal and the adjacent pairs can carry content.** `AlgebraicGeometry.tateV_far`
  (`FormalSchemes.TateChainGlue`) says `tateV R I q i j = ∅` when `j - i ∉ {1, -1}`, and
  `AlgebraicGeometry.LocallyRingedSpace.empty`'s presheaf is the *constant* functor at
  `CommRingCat.of PUnit`, so every section ring over such an overlap is a subsingleton and the
  condition there is automatic. At `i = j` the overlap is the patch itself,
  `CategoryTheory.GlueData.f_id` makes `f i i` an isomorphism and `CategoryTheory.GlueData.t_id`
  makes `t i i` the identity. This is the section-level form of the four-case
  split of `AlgebraicGeometry.tateChainInv_glueMorphisms_compat`
  (`FormalSchemes.TateChainInvGlue`); the reason it is not free is that
  `tateV_far` is an equality of locally ringed spaces, so reaching the `IsEmpty` instance means
  unfolding `CategoryTheory.GlueData.ofGlueData'` exactly as that morphism-level proof does.
* **Naming the two legs on an adjacent pair.** `AlgebraicGeometry.tateF` and
  `AlgebraicGeometry.tateTInv` present them through `annulusOverlapChart`,
  `annulusOverlapChartY` and the `𝔾m`-inversion transition, but each behind an
  `eqToHom` between two locally ringed spaces — and transporting a *section* along an equality of
  spaces is a step this tree has not taken. That is the harder of the two.

Descent from the chain to the quotient `T_inv/⟨σ⟩` is a separate matter and is **not** touched
here; see `FormalSchemes.TateInvNodeChartGlue`'s module docstring for what blocks it.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}
variable {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
variable {W : Opens (tateChainInv R I q hq hI).toLocallyRingedSpace}

/-! ### The open the overlap sees -/

/-- **The two legs pull the patch's open back to the same open of the overlap.** Both sides are
`(f i j ≫ ι i)⁻¹` of the saturation, by
`AlgebraicGeometry.FormalScheme.GlueData.map_glue_condition_obj` in the middle and
`AlgebraicGeometry.map_ι_tateInvSaturateOpens` at each end — the latter is what makes the two ends
the *same* open of `Spf A`, and it is the patch-independence proved in
`FormalSchemes.TateInvNodeChartRing`. -/
theorem map_f_tateInvPatchSaturateOpens (hS : IsOpen S)
    (i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (Opens.map ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).base).obj
        (tateInvPatchSaturateOpens hq hI hS) =
      (Opens.map ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f
        i j).base).obj (tateInvPatchSaturateOpens hq hI hS) := by
  have hi := map_ι_tateInvSaturateOpens (hq := hq) (hI := hI) hS i
  have hj := map_ι_tateInvSaturateOpens (hq := hq) (hI := hI) hS j
  calc (Opens.map ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).base).obj
        (tateInvPatchSaturateOpens hq hI hS)
      = (Opens.map ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
          (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).base).obj
          ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι j).base).obj
            (tateInvSaturateOpens hq hI hS)) := congrArg _ hj.symm
    _ = (Opens.map ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f
          i j).base).obj ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj
            (tateInvSaturateOpens hq hI hS)) :=
        (tateChainInvFormalGlueData R I q hq hI).map_glue_condition_obj
          (tateInvSaturateOpens hq hI hS) i j
    _ = (Opens.map ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f
          i j).base).obj (tateInvPatchSaturateOpens hq hI hS) := congrArg _ hi

/-! ### Pulling the constant family back -/

/-- **Pulling the constant family back along a morphism into the patch is pulling `s` back.** For
*any* `ψ` into `Spf A` and any index `k`, since the family at `k` is `s` transported along an
equality of opens (`AlgebraicGeometry.tateInvConstFamily`), `ψ` sees it as `ψ`'s own pullback of
`s`, transported.

Stated for a general `ψ` because both legs of the overlap need it — `f i j` at the index `i` and
`t i j ≫ f j i` at the index `j` — and the two uses differ only in the arguments. The transport is
moved past `ψ` by `AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom`
(`FormalSchemes.ActionQuotientInvariantSections`); the resulting transport is identified with the
one asked for by `AlgebraicGeometry.LocallyRingedSpace.presheaf_map_congr`. -/
theorem c_app_tateInvConstFamily (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (k : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    {V' : LocallyRingedSpace.{u}}
    (ψ : V' ⟶ FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))
    (hA : (Opens.map ψ.base).obj (tateInvPatchSaturateOpens hq hI hS) =
      (Opens.map ψ.base).obj
        ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι k).base).obj W)) :
    (ψ.c.app (op ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι k).base).obj W))).hom
        (tateInvConstFamily hS hW s k) =
      (V'.presheaf.map (eqToHom (congrArg op hA))).hom
        ((ψ.c.app (op (tateInvPatchSaturateOpens hq hI hS))).hom s) := by
  have hc := PresheafedSpace.c_app_map_eqToHom ψ.toShHom.hom
    (map_ι_of_eq_tateInvSaturateOpens hS hW k).symm s
  refine Eq.trans ?_ (hc.trans ?_)
  · rfl
  · exact ConcreteCategory.congr_hom (LocallyRingedSpace.presheaf_map_congr V'.presheaf _
      (eqToHom (congrArg op hA))) _

/-! ### The condition on `s` -/

/-- **The overlap condition on a single section of the model patch.** For every pair of indices, the
two legs `f i j` and `t i j ≫ f j i` out of the chain's overlap `V (i, j)` carry `s` to the same
section of `V (i, j)`, over the open `map_f_tateInvPatchSaturateOpens` identifies.

Only `s`, the patch, and the chain's glue data occur. Compare
`AlgebraicGeometry.tateChainInv_glueMorphisms_compat` (`FormalSchemes.TateChainInvGlue`), the
morphism-level obligation of the same shape. -/
def IsTateInvOverlapCompatible (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) : Prop :=
  ∀ i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J,
    (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j).c.app
        (op (tateInvPatchSaturateOpens hq hI hS))).hom s =
      (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V (i, j)).presheaf.map
        (eqToHom (congrArg op (map_f_tateInvPatchSaturateOpens hS i j)))).hom
        ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
          (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).c.app
          (op (tateInvPatchSaturateOpens hq hI hS))).hom s)

/-- **The constant family satisfies the general overlap condition exactly when `s` satisfies this
one.** Both sides are the same equation at each pair, read over two opens that
`map_f_tateInvPatchSaturateOpens` and `map_ι_tateInvSaturateOpens` identify;
`c_app_tateInvConstFamily` performs the identification on each leg and
`AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff` (`FormalSchemes.ActionQuotientSections`)
cancels the two transports against each other. -/
theorem isOverlapCompatible_tateInvConstFamily_iff (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    (tateChainInvFormalGlueData R I q hq hI).IsOverlapCompatible W
        (tateInvConstFamily hS hW s) ↔ IsTateInvOverlapCompatible hS s := by
  have key : ∀ i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J,
      ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j).c.app
          (op ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj W))).hom
          (tateInvConstFamily hS hW s i) =
        (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V
            (i, j)).presheaf.map (eqToHom (congrArg op
              ((tateChainInvFormalGlueData R I q hq hI).map_glue_condition_obj W i j)))).hom
          ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
            (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).c.app
            (op ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι j).base).obj W))).hom
            (tateInvConstFamily hS hW s j))) ↔
      ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j).c.app
          (op (tateInvPatchSaturateOpens hq hI hS))).hom s =
        (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V
            (i, j)).presheaf.map
          (eqToHom (congrArg op (map_f_tateInvPatchSaturateOpens hS i j)))).hom
          ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
            (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).c.app
            (op (tateInvPatchSaturateOpens hq hI hS))).hom s)) := by
    intro i j
    have hAL := congrArg (Opens.map
      ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j).base).obj
      (map_ι_of_eq_tateInvSaturateOpens hS hW i).symm
    have hAR := congrArg (Opens.map
      ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).base).obj
      (map_ι_of_eq_tateInvSaturateOpens hS hW j).symm
    have hB := hAR.trans
      ((tateChainInvFormalGlueData R I q hq hI).map_glue_condition_obj W i j)
    have hL := c_app_tateInvConstFamily hS hW s i
      ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j) hAL
    have hR := c_app_tateInvConstFamily hS hW s j
      ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i) hAR
    have hstep := Eq.trans (congrArg (fun z =>
      ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V
          (i, j)).presheaf.map (eqToHom (congrArg op
            ((tateChainInvFormalGlueData R I q hq hI).map_glue_condition_obj W i j)))).hom z)) hR)
      ((LocallyRingedSpace.presheaf_map_comp_apply _ _ _ _).trans
        (ConcreteCategory.congr_hom (LocallyRingedSpace.presheaf_map_congr _ _
          (eqToHom (congrArg op hB))) _))
    constructor
    · intro heq
      exact (PresheafedSpace.map_eqToHom_eq_iff _ hAL hB _ _).1
        (hL.symm.trans (heq.trans hstep))
    · intro heq
      exact hL.trans (((PresheafedSpace.map_eqToHom_eq_iff _ hAL hB _ _).2 heq).trans hstep.symm)
  exact ⟨fun h i j => (key i j).1 (h i j), fun h i j => (key i j).2 (h i j)⟩

/-! ### What the condition buys -/

/-- **`s` extends to the chain iff it satisfies the overlap condition.**
`AlgebraicGeometry.FormalScheme.GlueData.exists_ι_c_app_eq_iff_isOverlapCompatible`
(`FormalSchemes.GlueDataOverlapCompat`) at the chain and the constant family, with the condition
rewritten by `isOverlapCompatible_tateInvConstFamily_iff`. This is
`AlgebraicGeometry.exists_tateInvConstFamily_iff_isCompatible`
(`FormalSchemes.TateInvNodeChartGlue`) with its hypothesis made concrete. -/
theorem exists_tateInvConstFamily_iff_tateInvOverlapCompatible (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    (∃ g : (tateChainInv R I q hq hI).presheaf.obj (op W),
        ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
          tateInvConstFamily hS hW s i) ↔ IsTateInvOverlapCompatible hS s :=
  ((tateChainInvFormalGlueData R I q hq hI).exists_ι_c_app_eq_iff_isOverlapCompatible W _).trans
    (isOverlapCompatible_tateInvConstFamily_iff hS hW s)

/-- **And the extension is unique.** The `ExistsUnique` form; uniqueness is the separation half
`AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq` (`FormalSchemes.GlueDataSectionExt`),
carried through `FormalScheme.GlueData.existsUnique_ι_c_app_eq_of_isOverlapCompatible`. -/
theorem existsUnique_tateInvConstFamily_of_tateInvOverlapCompatible (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (h : IsTateInvOverlapCompatible hS s) :
    ∃! g : (tateChainInv R I q hq hI).presheaf.obj (op W),
      ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
        tateInvConstFamily hS hW s i :=
  (tateChainInvFormalGlueData R I q hq hI).existsUnique_ι_c_app_eq_of_isOverlapCompatible W _
    ((isOverlapCompatible_tateInvConstFamily_iff hS hW s).2 h)

/-- **A section of the patch satisfying the overlap condition produces a `σ`-invariant section of
the chain.** The extension is the one above; its invariance is
`AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`
(`FormalSchemes.TateInvNodeChartGlue`), which needs exactly that the family of pullbacks does not
depend on the index.

This is the whole of the description of the invariant sections of the chain over a saturation, with
no condition left that mentions `T_inv`: the hypothesis is about `s`, the model patch and the two
legs of an overlap. What it does **not** do is descend to `T_inv/⟨σ⟩`; see
`FormalSchemes.TateInvNodeChartGlue`'s module docstring for what blocks that. -/
theorem exists_tateInvShiftAut_zpow_invariant_of_tateInvOverlapCompatible (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (h : IsTateInvOverlapCompatible hS s) :
    ∃ g : (tateChainInv R I q hq hI).presheaf.obj (op W),
      (∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
          tateInvConstFamily hS hW s i) ∧
        ∀ k : ℤ, (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app (op W)) g =
          (tateChainInv R I q hq hI).presheaf.map
            (eqToHom (congrArg op (eq_map_tateInvShiftAut_zpow hS hW k))) g := by
  obtain ⟨g, hg, -⟩ := existsUnique_tateInvConstFamily_of_tateInvOverlapCompatible hS hW s h
  exact ⟨g, hg, fun k => c_app_tateInvShiftAut_zpow_eq_of_const hS hW s g hg k⟩

end AlgebraicGeometry
