import FormalSchemes.TateInvNodeChartRing
import FormalSchemes.GlueDataSectionGlue

set_option linter.style.header false

/-!
# A section of the model patch extends to a `σ`-invariant section of the chain

`FormalSchemes.TateInvNodeChartRing` proved the **uniqueness** half of the description of
`Γ (T_inv/⟨σ⟩, π V)` for `V = tateInvSaturate S`: a section of the quotient is determined by its
pullback to one patch `Spf A`, and the open it lives on is
`AlgebraicGeometry.tateInvPatchSaturate S`. Its module docstring names the missing half — the
*existence* half of the sheaf axiom on the cover by the patch images — and
`FormalSchemes.GlueDataSectionGlue` now supplies that for an arbitrary
`AlgebraicGeometry.FormalScheme.GlueData`.

This file is that general statement, instantiated at the chain, plus the step which is special to
the period-`q` action and is the reason the instantiation is worth making:

> the family that puts **the same** section `s` on every patch is `σ`-invariant automatically.

The shift permutes the patch inclusions, `ι i ≫ σ ^ k = ι ⟨i + k⟩`
(`AlgebraicGeometry.ι_tateInvShiftAut_zpow`), so a family that does not depend on the index cannot
see it. Concretely: if a section `g` of the chain over `tateInvSaturate S` pulls back to the same
`s` on every patch, then `(σ ^ k)^* g = g` for every `k`, and that is
`AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`.

## What is here

* `AlgebraicGeometry.tateInvSaturateOpens`, `AlgebraicGeometry.tateInvPatchSaturateOpens`: the two
  sets of `FormalSchemes.TateInvSaturation` and `FormalSchemes.TateInvNodeChartRing`, bundled as
  opens, and `AlgebraicGeometry.map_ι_tateInvSaturateOpens` — the first is pulled back to the
  second by every patch inclusion. The statements below are all phrased at an open `W` **equal to**
  the saturation rather than at the saturation itself, so that a `subst` is available at the one
  place where the two sides of an `eqToHom` have to meet; that generality is also what a consumer
  needs, since the open it will want is `π⁻¹` of an open of the quotient.
* `AlgebraicGeometry.tateInvConstFamily`: `s`, read on every patch.
* `AlgebraicGeometry.existsUnique_tateInvConstFamily` and
  `AlgebraicGeometry.exists_tateInvConstFamily_iff_isCompatible`: `s` extends to a section of the
  chain over `W` **iff** the constant family is compatible, and then uniquely.
* `AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`: **the invariance.** A section whose
  pullbacks are a constant family is fixed by every `σ ^ k`.

## What is left

The remaining step is **descent**: an invariant section of `T_inv` over `π⁻¹ V` is the pullback of
a section of the quotient over `V`. The tree's statement of it,
`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`
(`FormalSchemes.ActionQuotientInvariantSections`), takes exactly the invariance above as its
hypothesis, and it now applies here: the acting group has its own universe, so the theorem may be
read at `AlgebraicGeometry.tateInvPeriodAction`, which acts by `Multiplicative ℤ`, over a base
ring `R : Type u`. `AlgebraicGeometry.exists_actionQuotientπ_c_app_eq_of_const`
(`FormalSchemes.TateInvQuotientSections`) is `c_app_tateInvShiftAut_zpow_eq_of_const` fed to it,
and `AlgebraicGeometry.existsUnique_actionQuotientπ_c_app_eq_of_isCompatible` puts that together
with the gluing above: a compatible `s` on the model patch determines a unique section of the
quotient.

What is still open, and is not a universe question, is making the compatibility condition
**concrete**. `TopCat.Presheaf.IsCompatible` for the transported constant family is a condition on
opens of the chain; translating it into the chain's `𝔾m`-inversion transition on the overlap, and
so exhibiting `Γ (T_inv/⟨σ⟩, π V)` as an equalizer over the single patch, is the piece neither
this file nor `FormalSchemes.TateInvQuotientSections` touches.

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

/-! ### The two opens -/

/-- **The saturation of an open of the model patch, as an open of the chain.**
`AlgebraicGeometry.tateInvSaturate` with `AlgebraicGeometry.isOpen_tateInvSaturate`
(`FormalSchemes.TateInvSaturation`). -/
def tateInvSaturateOpens (hq : q ∈ I) (hI : I.FG) (hS : IsOpen S) :
    Opens (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  ⟨tateInvSaturate R I q hq hI S, isOpen_tateInvSaturate hq hI hS⟩

/-- **The open of the model patch that a saturation sees, as an open.**
`AlgebraicGeometry.tateInvPatchSaturate` with `AlgebraicGeometry.isOpen_tateInvPatchSaturate`
(`FormalSchemes.TateInvNodeChartRing`). It contains `S` and is in general larger; that is the point
of the row this file belongs to. -/
def tateInvPatchSaturateOpens (hq : q ∈ I) (hI : I.FG) (hS : IsOpen S) :
    Opens (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) :=
  ⟨tateInvPatchSaturate hq hI S, isOpen_tateInvPatchSaturate hq hI hS⟩

/-- **Every patch pulls the saturation back to the same open.** The `Opens` form of
`AlgebraicGeometry.preimage_ι_tateInvSaturate` (`FormalSchemes.TateInvNodeChartRing`), which is
where the patch-independence is proved. -/
theorem map_ι_tateInvSaturateOpens (hS : IsOpen S) (i : ULift.{u} ℤ) :
    (Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj
        (tateInvSaturateOpens hq hI hS) = tateInvPatchSaturateOpens hq hI hS :=
  Opens.ext (preimage_ι_tateInvSaturate hq hI S i)

variable {W : Opens (tateChainInv R I q hq hI).toLocallyRingedSpace}

/-- `map_ι_tateInvSaturateOpens` at an open merely *equal* to the saturation. The hypothesis is
carried rather than substituted at the statement level because a consumer's open is
`π⁻¹` of an open of the quotient, which is equal to the saturation and not definitionally so. -/
theorem map_ι_of_eq_tateInvSaturateOpens (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj W =
      tateInvPatchSaturateOpens hq hI hS := by
  subst hW
  exact map_ι_tateInvSaturateOpens hS i

/-- **A saturation is invariant under the shift, as an open.** The `Opens` form of
`AlgebraicGeometry.mem_tateInvSaturate_shift_iff` (`FormalSchemes.TateInvNodeChartRing`). It is
stated in the direction `W = (σ ^ k)⁻¹ W` because that is the direction the transport of a section
along it is wanted in. -/
theorem eq_map_tateInvShiftAut_zpow (hS : IsOpen S) (hW : W = tateInvSaturateOpens hq hI hS)
    (k : ℤ) :
    W = (Opens.map ((tateInvShiftAut R I q hq hI) ^ k).hom.base).obj W := by
  subst hW
  exact Opens.ext (Set.ext fun x => (mem_tateInvSaturate_shift_iff hq hI k S x).symm)

/-! ### The constant family and its gluing -/

/-- **One section of the model patch, read on every patch of the chain.** The transport is along
`map_ι_of_eq_tateInvSaturateOpens`, an equality of opens and not an inclusion, so no information is
lost: the family really is `s` on each patch. -/
def tateInvConstFamily (hS : IsOpen S) (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj W)) :=
  (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
    (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens hS hW i).symm)) s

/-- **A compatible `s` extends to the chain, uniquely.**
`AlgebraicGeometry.FormalScheme.GlueData.existsUnique_ι_c_app_eq`
(`FormalSchemes.GlueDataSectionGlue`) at the chain's glue datum and the constant family. -/
theorem existsUnique_tateInvConstFamily (hS : IsOpen S) (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (h : IsCompatible ((tateChainInvFormalGlueData R I q hq hI).gluedFormalScheme).presheaf
      ((tateChainInvFormalGlueData R I q hq hI).ιCover W)
      (fun i => (((tateChainInvFormalGlueData R I q hq hI).ιSectionIso W i).hom).hom
        (tateInvConstFamily hS hW s i))) :
    ∃! g : (tateChainInv R I q hq hI).presheaf.obj (op W),
      ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
        tateInvConstFamily hS hW s i :=
  (tateChainInvFormalGlueData R I q hq hI).existsUnique_ι_c_app_eq _ _ h

/-- **`s` extends to the chain iff its constant family is compatible.** The `iff` form, from
`AlgebraicGeometry.FormalScheme.GlueData.exists_ι_c_app_eq_iff_isCompatible`. This is the
description of the sections of the chain over a saturation that are constant on the patches; the
step from here to the sections of the *quotient* is the descent the module docstring describes. -/
theorem exists_tateInvConstFamily_iff_isCompatible (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    (∃ g : (tateChainInv R I q hq hI).presheaf.obj (op W),
        ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
          tateInvConstFamily hS hW s i) ↔
      IsCompatible ((tateChainInvFormalGlueData R I q hq hI).gluedFormalScheme).presheaf
        ((tateChainInvFormalGlueData R I q hq hI).ιCover W)
        (fun i => (((tateChainInvFormalGlueData R I q hq hI).ιSectionIso W i).hom).hom
          (tateInvConstFamily hS hW s i)) :=
  (tateChainInvFormalGlueData R I q hq hI).exists_ι_c_app_eq_iff_isCompatible _ _

/-! ### Invariance -/

/-- **A section of the chain that is constant on the patches is `σ`-invariant.** For every `k`,
`(σ ^ k)^* g = g`, the two sides being compared over `(σ ^ k)⁻¹ W = W`
(`eq_map_tateInvShiftAut_zpow`).

The proof is the whole content of this file. By
`AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq` (`FormalSchemes.GlueDataSectionExt`) it
is enough to compare the two sides patch by patch. On the left,
`AlgebraicGeometry.LocallyRingedSpace.c_app_comp_of_eq`
(`FormalSchemes.ActionInvariantExtension`) applied to the factorisation
`ι ⟨i + k⟩ = ι i ≫ σ ^ k` (`AlgebraicGeometry.ι_tateInvShiftAut_zpow`) turns the pullback along the
`i`-th patch of `(σ ^ k)^* g` into the pullback of `g` along the `⟨i + k⟩`-th; on the right,
`AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom` moves the transport past the pullback. The
hypothesis then says that both are `s`, at indices `⟨i + k⟩` and `i` — and the family does not
depend on the index, which is exactly why the shift is invisible.

Everything else is bookkeeping between equal opens:
`AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff` (`FormalSchemes.ActionQuotientSections`) and
`AlgebraicGeometry.PresheafedSpace.map_eqToHom_trans_apply`. Note the two spellings of a
`c`-component: the hypothesis arrives in the locally-ringed-space spelling and the lemmas above are
in the presheafed-space one, so `hg'` restates it — the two are definitionally equal but do not
unify for `rw`. -/
theorem c_app_tateInvShiftAut_zpow_eq_of_const (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (g : (tateChainInv R I q hq hI).presheaf.obj (op W))
    (hg : ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
      tateInvConstFamily hS hW s i) (k : ℤ) :
    (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app (op W)) g =
      (tateChainInv R I q hq hI).presheaf.map
        (eqToHom (congrArg op (eq_map_tateInvShiftAut_zpow hS hW k))) g := by
  refine FormalScheme.GlueData.eq_of_ι_c_app_eq (tateChainInvFormalGlueData R I q hq hI) _ _ _
    (fun i => ?_)
  have hWk := eq_map_tateInvShiftAut_zpow hS hW k
  have hR := AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom
    ((tateChainInvFormalGlueData R I q hq hI).ι i).toShHom.hom hWk g
  have hphi : (tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + k⟩ =
      (tateChainInvFormalGlueData R I q hq hI).ι i ≫ ((tateInvShiftAut R I q hq hI) ^ k).hom :=
    (ι_tateInvShiftAut_zpow R I q hq hI k i).symm
  have hL := AlgebraicGeometry.LocallyRingedSpace.c_app_comp_of_eq
    ((tateChainInvFormalGlueData R I q hq hI).ι i) ((tateInvShiftAut R I q hq hI) ^ k).hom hphi
    W g
  have hA : (Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj
        ((Opens.map ((tateInvShiftAut R I q hq hI) ^ k).hom.base).obj W) =
      (Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + k⟩).base).obj W := by
    rw [hphi]
    rfl
  have hg' : ∀ j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J,
      (((tateChainInvFormalGlueData R I q hq hI).ι j).toShHom.hom.c.app (op W)) g =
        tateInvConstFamily hS hW s j := hg
  have hL2 := (hg' ⟨i.down + k⟩).symm.trans hL
  refine Eq.trans ?_ hR.symm
  rw [hg' i]
  have hLeft := (AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff _ hA
    (map_ι_of_eq_tateInvSaturateOpens hS hW ⟨i.down + k⟩).symm _ s).1 hL2.symm
  refine hLeft.trans ?_
  simp only [tateInvConstFamily]
  exact (AlgebraicGeometry.PresheafedSpace.map_eqToHom_trans_apply _
    (map_ι_of_eq_tateInvSaturateOpens hS hW i).symm
    (congrArg (Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj hWk) s).symm

end AlgebraicGeometry
