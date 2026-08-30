import FormalSchemes.TateInvChartAnnulusRing
import FormalSchemes.TateChartTransitionInvAlgEq
import FormalSchemes.AdicOnSections
import FormalSchemes.SpfGammaFunctorial

set_option linter.style.header false

/-!
# `Γ (T_inv/⟨σ⟩)` as an explicit subring of `A = R{x, y}/(x·y − q)`

PLACEHOLDER MODULE DOCSTRING
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace FormalSpectrum

section EqTop

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- **Sections over an open that happens to be `⊤` are the ring itself.**
`FormalSpectrum.globalSectionsEquiv` (EGA I 10.1.3) after the transport along `hU`. -/
def sectionsEquivOfEqTop {U : Opens (FormalSpectrum I)} (hU : U = ⊤) :
    ((locallyRingedSpaceObj I).presheaf.obj (op U) : Type u) ≃+* R :=
  (((locallyRingedSpaceObj I).presheaf.mapIso
    (eqToIso (congrArg op hU))).commRingCatIsoToRingEquiv).trans (globalSectionsEquiv I)

theorem sectionsEquivOfEqTop_apply {U : Opens (FormalSpectrum I)} (hU : U = ⊤)
    (s : (locallyRingedSpaceObj I).presheaf.obj (op U)) :
    sectionsEquivOfEqTop I hU s =
      globalSectionsEquiv I (((locallyRingedSpaceObj I).presheaf.map
        (eqToHom (congrArg op hU))).hom s) := rfl

end EqTop

section Map

variable {A B : Type u} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
variable (J : Ideal A) (K : Ideal B) [IsAdicRing J] [IsAdicRing K]

/-- **A `c`-component read over an open that is `⊤` is the global-sections map.** For a morphism
`f : Spf K ⟶ Spf J`, an open `U` of `Spf J` equal to `⊤`, an open `W` of `Spf K` equal to `⊤` and
an identification `hfUW` of `f⁻¹ U` with `W`, the composite of `f.c.app (op U)` with the transport
along `hfUW` is `FormalSpectrum.globalSectionsMap J K f` read through
`FormalSpectrum.sectionsEquivOfEqTop` on both sides.

`hfUW` is not derived from `hU` and `hW` because the consumers need it at a `W` that is not
syntactically `f⁻¹ U`: the two legs of the Tate overlap condition are compared over one and the
same open of `Spf A{1/x}`, reached from the two chart preimages by
`AlgebraicGeometry.map_annulusOverlapChartY_tateInvPatchSaturateOpens`. -/
theorem globalSectionsMap_sectionsEquivOfEqTop
    (f : locallyRingedSpaceObj K ⟶ locallyRingedSpaceObj J)
    {U : Opens (FormalSpectrum J)} (hU : U = ⊤)
    {W : Opens (FormalSpectrum K)} (hW : W = ⊤)
    (hfUW : (Opens.map f.base).obj U = W)
    (s : (locallyRingedSpaceObj J).presheaf.obj (op U)) :
    globalSectionsMap J K f (sectionsEquivOfEqTop J hU s) =
      sectionsEquivOfEqTop K hW
        (((locallyRingedSpaceObj K).presheaf.map (eqToHom (congrArg op hfUW))).hom
          ((f.c.app (op U)).hom s)) := by
  rw [sectionsEquivOfEqTop_apply, sectionsEquivOfEqTop_apply, globalSectionsMap_apply,
    RingEquiv.symm_apply_apply]
  congr 1
  refine (AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom f.toShHom.hom hU s).trans ?_
  exact (AlgebraicGeometry.PresheafedSpace.map_eqToHom_trans_apply
    (locallyRingedSpaceObj K).presheaf hfUW hW _).symm

end Map

end FormalSpectrum

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}

/-! ### The two opens at `S = Set.univ` -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The saturation of the whole model patch is `⊤`.** The `Opens` form of
`AlgebraicGeometry.tateInvSaturate_univ` (`FormalSchemes.TateInvSaturation`). -/
theorem tateInvSaturateOpens_univ :
    tateInvSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI isOpen_univ = ⊤ :=
  Opens.ext (tateInvSaturate_univ hq hI)

/-- **`V = ⊤` is an admissible chart open at `S = Set.univ`**, exhibited rather than assumed:
`AlgebraicGeometry.tateInvChartAnnulusRingEquiv` asks for an open `V` of the quotient with
`π⁻¹ V = tateInvSaturateOpens hq hI hS`, and at `S = Set.univ` the preimage of `⊤` is `⊤`, which is
that saturation by `tateInvSaturateOpens_univ`. -/
theorem map_actionQuotientπ_top_eq :
    (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj ⊤ =
      tateInvSaturateOpens (S := Set.univ) hq hI isOpen_univ := by
  rw [tateInvSaturateOpens_univ]; rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Every morphism into `Spf A` pulls the whole patch back to `⊤`.**
`AlgebraicGeometry.tateInvPatchSaturateOpens_univ` (`FormalSchemes.TateInvChartAnnulusRing`)
followed by `Opens.map_top`. Stated for an arbitrary `g` because it is used at the two overlap
charts and at the two composites with the `𝔾m`-inversion transition. -/
theorem map_base_tateInvPatchSaturateOpens_univ {X : LocallyRingedSpace.{u}}
    (g : X ⟶ FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) :
    (Opens.map g.base).obj
        (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI isOpen_univ)
      = ⊤ := by
  rw [tateInvPatchSaturateOpens_univ]; rfl

end AlgebraicGeometry
