import FormalSchemes.TateInvNodeChartOverlap
import FormalSchemes.TateInvQuotientSections

set_option linter.style.header false

/-!
# Placeholder
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

/-! ### The shift factorisation, at a pair of indices -/

theorem ι_tateInvShiftAut_zpow_of_eq (k : ℤ) (i j : ULift.{u} ℤ) (h : i.down + k = j.down) :
    (tateChainInvFormalGlueData R I q hq hI).ι i ≫ ((tateInvShiftAut R I q hq hI) ^ k).hom =
      (tateChainInvFormalGlueData R I q hq hI).ι j := by
  obtain rfl : (⟨i.down + k⟩ : ULift.{u} ℤ) = j := ULift.down_injective h
  exact ι_tateInvShiftAut_zpow R I q hq hI k i

/-! ### The section of the model patch cut out by a section of the chain -/

def tateInvPatchSection (hS : IsOpen S) (hW : W = tateInvSaturateOpens hq hI hS)
    (g : (tateChainInv R I q hq hI).presheaf.obj (op W)) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)) :=
  ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
    (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens hS hW ⟨(0 : ℤ)⟩)))).hom
    ((((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).c.app (op W)).hom g)

theorem tateInvConstFamily_tateInvPatchSection (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (g : (tateChainInv R I q hq hI).presheaf.obj (op W))
    (hinv : ∀ k : ℤ, (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app (op W)) g =
      (tateChainInv R I q hq hI).presheaf.map
        (eqToHom (congrArg op (eq_map_tateInvShiftAut_zpow hS hW k))) g)
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
      tateInvConstFamily hS hW (tateInvPatchSection hS hW g) i := by
  have hphi : (tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩ ≫
      ((tateInvShiftAut R I q hq hI) ^ i.down).hom =
      (tateChainInvFormalGlueData R I q hq hI).ι i :=
    ι_tateInvShiftAut_zpow_of_eq i.down ⟨(0 : ℤ)⟩ i (zero_add _)
  have hL := LocallyRingedSpace.c_app_comp_of_eq
    ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩)
    ((tateInvShiftAut R I q hq hI) ^ i.down).hom hphi.symm W g
  have hc := AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom
    ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).toShHom.hom
    (eq_map_tateInvShiftAut_zpow hS hW i.down) g
  refine hL.trans ?_
  refine Eq.trans (congrArg _ (congrArg _ (hinv i.down))) ?_
  refine Eq.trans (congrArg _ hc) ?_
  simp only [tateInvConstFamily, tateInvPatchSection]
  exact ((LocallyRingedSpace.presheaf_map_comp_apply _ _ _ _).trans
    (ConcreteCategory.congr_hom (LocallyRingedSpace.presheaf_map_congr _ _ _) _)).trans
    (LocallyRingedSpace.presheaf_map_comp_apply _ _ _ _).symm

theorem tateInvConstFamily_injective (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    Function.Injective (fun s => tateInvConstFamily hS hW s i) := by
  intro s s' h
  have hkey := (AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff _
    (map_ι_of_eq_tateInvSaturateOpens hS hW i).symm
    (map_ι_of_eq_tateInvSaturateOpens hS hW i).symm s s').1 h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hkey
  exact hkey


/-! ### At the quotient -/

section Quotient

variable (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)

theorem c_app_tateInvShiftAut_zpow_actionQuotientπ (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) (k : ℤ) :
    (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V)))
        (((actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.c.app (op V)) t) =
      (tateChainInv R I q hq hI).presheaf.map
        (eqToHom (congrArg op (eq_map_tateInvShiftAut_zpow hS hV k)))
        (((actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.c.app (op V)) t) :=
  (exists_actionQuotientπ_c_app_eq_iff_forall_zpow V _).1 ⟨t, rfl⟩ k

def tateInvChartSection (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)) :=
  tateInvPatchSection hS hV
    ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app (op V))).hom t)

theorem tateInvConstFamily_tateInvChartSection (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V))
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))).hom
        ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app (op V))).hom t) =
      tateInvConstFamily hS hV (tateInvChartSection V hS hV t) i :=
  tateInvConstFamily_tateInvPatchSection hS hV _
    (c_app_tateInvShiftAut_zpow_actionQuotientπ V hS hV t) i

theorem isTateInvOverlapCompatible_tateInvChartSection (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) :
    IsTateInvOverlapCompatible hS (tateInvChartSection V hS hV t) :=
  (exists_tateInvConstFamily_iff_tateInvOverlapCompatible hS hV _).1
    ⟨_, tateInvConstFamily_tateInvChartSection V hS hV t⟩

theorem tateInvChartSection_injective (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS) :
    Function.Injective (tateInvChartSection V hS hV) := by
  intro t t' h
  refine LocallyRingedSpace.injective_coequalizer_π_c_app _ _ V ?_
  refine FormalScheme.GlueData.eq_of_ι_c_app_eq (tateChainInvFormalGlueData R I q hq hI) _ _ _
    fun i => ?_
  refine (tateInvConstFamily_tateInvChartSection V hS hV t i).trans ?_
  refine Eq.trans ?_ (tateInvConstFamily_tateInvChartSection V hS hV t' i).symm
  exact congrArg (fun z => tateInvConstFamily hS hV z i) h

theorem exists_tateInvChartSection_eq_of_isTateInvOverlapCompatible (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (h : IsTateInvOverlapCompatible hS s) :
    ∃ t, tateInvChartSection V hS hV t = s := by
  obtain ⟨t, ht, -⟩ := existsUnique_actionQuotientπ_c_app_eq_of_isCompatible hS V hV s
    ((FormalScheme.GlueData.isCompatible_iff_isOverlapCompatible _ _ _).2
      ((isOverlapCompatible_tateInvConstFamily_iff hS hV s).2 h))
  refine ⟨t, tateInvConstFamily_injective hS hV ⟨(0 : ℤ)⟩ ?_⟩
  exact (tateInvConstFamily_tateInvChartSection V hS hV t ⟨(0 : ℤ)⟩).symm.trans (ht ⟨(0 : ℤ)⟩)


/-! ### The ring -/

def tateInvChartSubring (hS : IsOpen S) :
    Subring ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :=
  ⨅ i, ⨅ j, RingHom.eqLocus
    ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j).c.app
      (op (tateInvPatchSaturateOpens hq hI hS))).hom)
    ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V
        (i, j)).presheaf.map
      (eqToHom (congrArg op (map_f_tateInvPatchSaturateOpens hS i j)))).hom.comp
      ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).c.app
        (op (tateInvPatchSaturateOpens hq hI hS))).hom))

theorem mem_tateInvChartSubring_iff (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    s ∈ tateInvChartSubring hS ↔ IsTateInvOverlapCompatible hS s := by
  simp only [tateInvChartSubring, Subring.mem_iInf, RingHom.mem_eqLocus,
    IsTateInvOverlapCompatible]
  exact Iff.rfl

def tateInvChartSectionHom (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) →+*
      ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI hS))) :=
  (((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
      (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens hS hV ⟨(0 : ℤ)⟩)))).hom).comp
    (((((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))).hom).comp
      (((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app (op V)).hom))

theorem tateInvChartSectionHom_apply (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) :
    tateInvChartSectionHom V hS hV t = tateInvChartSection V hS hV t :=
  rfl

def tateInvChartRingEquiv (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
      tateInvChartSubring (hq := hq) (hI := hI) hS :=
  RingEquiv.ofBijective
    ((tateInvChartSectionHom V hS hV).codRestrict (tateInvChartSubring hS) fun t =>
      (mem_tateInvChartSubring_iff hS _).2
        (isTateInvOverlapCompatible_tateInvChartSection V hS hV t))
    ⟨fun a b h => tateInvChartSection_injective V hS hV (congrArg Subtype.val h), fun z => by
      obtain ⟨t, ht⟩ := exists_tateInvChartSection_eq_of_isTateInvOverlapCompatible V hS hV z.1
        ((mem_tateInvChartSubring_iff hS _).1 z.2)
      exact ⟨t, Subtype.ext ht⟩⟩

end Quotient

end AlgebraicGeometry
