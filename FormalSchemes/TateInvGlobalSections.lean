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

/-! ### The four legs as ring maps of `A` -/

/-- **The `x`-chart restriction of `A`**: `A → A{1/x}`. -/
def tateInvGlobalLegX :
    annulusAlgebra R I q →+* awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) :=
  awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)

/-- **The `y`-chart restriction of `A` followed by the `𝔾m`-inversion transition**:
`A → A{1/y} → A{1/x}`. -/
def tateInvGlobalLegYX (hI : I.FG) :
    annulusAlgebra R I q →+* awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) :=
  (annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))

/-- **The `y`-chart restriction of `A`**: `A → A{1/y}`. -/
def tateInvGlobalLegY :
    annulusAlgebra R I q →+* awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)

/-- **The `x`-chart restriction of `A` followed by the inverse `𝔾m`-inversion transition**:
`A → A{1/x} → A{1/y}`. -/
def tateInvGlobalLegXY (hI : I.FG) :
    annulusAlgebra R I q →+* awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  (annulusChartTransitionInvAlg R I q hI).toRingHom.comp
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))

/-- **The candidate ring, as a subring of `A` cut out by two equations.** No locally ringed space,
no glue datum and no presheaf occurs: the four legs are `awayCompletionHom` and the ring-level
`𝔾m`-inversion transition `AlgebraicGeometry.annulusChartTransitionInvAlg`. -/
def tateInvGlobalSubring (hI : I.FG) : Subring (annulusAlgebra R I q) :=
  RingHom.eqLocus (tateInvGlobalLegX (R := R) (I := I) (q := q)) (tateInvGlobalLegYX hI) ⊓
    RingHom.eqLocus (tateInvGlobalLegY (R := R) (I := I) (q := q)) (tateInvGlobalLegXY hI)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **Membership is the pair of equations.** `Subring.mem_inf` and `RingHom.mem_eqLocus`. -/
theorem mem_tateInvGlobalSubring_iff (hI : I.FG) (a : annulusAlgebra R I q) :
    a ∈ tateInvGlobalSubring hI ↔
      tateInvGlobalLegX a = tateInvGlobalLegYX hI a ∧
        tateInvGlobalLegY a = tateInvGlobalLegXY hI a := by
  simp only [tateInvGlobalSubring, Subring.mem_inf, RingHom.mem_eqLocus]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **Non-vacuity: the subring contains the image of the base ring.** All four legs are
`R`-algebra homomorphisms — `FormalSpectrum.awayCompletionHom_comp_algebraMap` for the two chart
restrictions, `AlgEquiv.commutes` for the transition — so they agree on `algebraMap R A`.

This is *not* issue 1223's goal 3, which asks for an element of the ring **outside** this image;
it is its trivial half, and the two must not be confused. -/
theorem algebraMap_mem_tateInvGlobalSubring (hI : I.FG) (r : R) :
    algebraMap R (annulusAlgebra R I q) r ∈ tateInvGlobalSubring hI := by
  have hx : awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
      (algebraMap R (annulusAlgebra R I q) r) =
        algebraMap R (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) r :=
    congrArg (fun φ : R →+* _ => φ r)
      (FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (overlapX R I q))
  have hy : awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
      (algebraMap R (annulusAlgebra R I q) r) =
        algebraMap R (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) r :=
    congrArg (fun φ : R →+* _ => φ r)
      (FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (overlapY R I q))
  refine (mem_tateInvGlobalSubring_iff hI _).2 ⟨?_, ?_⟩ <;>
    simp only [tateInvGlobalLegX, tateInvGlobalLegY, tateInvGlobalLegYX, tateInvGlobalLegXY,
      RingHom.comp_apply, hx, hy]
  · exact ((annulusChartTransitionInvAlg R I q hI).symm.commutes r).symm
  · exact ((annulusChartTransitionInvAlg R I q hI).commutes r).symm

/-! ### The four legs at `S = Set.univ`, computed -/

section GlobalCollapse

variable [IsAdicRing (annulusIdealOfDefinition R I q)]

/-- **The patch's sections at `S = Set.univ` are `A` itself.** -/
def tateInvGlobalPatchEquiv (hq : q ∈ I) (hI : I.FG) :
    ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ)) : Type u) ≃+* annulusAlgebra R I q :=
  FormalSpectrum.sectionsEquivOfEqTop _ tateInvPatchSaturateOpens_univ

section X

variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]

/-- **The `x`-overlap's sections over the open both forward legs are read on are `A{1/x}`.** -/
def tateInvGlobalXEquiv (hq : q ∈ I) (hI : I.FG) :
    ((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (overlapX R I q))).presheaf.obj
      (op ((Opens.map (annulusOverlapChart R I q).base).obj
        (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
          isOpen_univ))) : Type u) ≃+*
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) :=
  FormalSpectrum.sectionsEquivOfEqTop _ (map_base_tateInvPatchSaturateOpens_univ _)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A forward leg is its global-sections map.** `f` is left abstract: instantiating it is
substitution and does not re-elaborate, whereas stating this at
`(annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q` directly makes the
kernel's defeq check on this cluster time out. -/
theorem tateInvGlobalXEquiv_c_app (hq : q ∈ I) (hI : I.FG)
    (f : FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
        (annulusIdealOfDefinition R I q) (overlapX R I q)) ⟶
      FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))
    (hf : (Opens.map f.base).obj
        (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI isOpen_univ) =
      (Opens.map (annulusOverlapChart R I q).base).obj
        (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI isOpen_univ))
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))) :
    tateInvGlobalXEquiv hq hI
        (((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
          (annulusIdealOfDefinition R I q) (overlapX R I q))).presheaf.map
            (eqToHom (congrArg op hf))).hom ((f.c.app (op (tateInvPatchSaturateOpens hq hI
              (S := Set.univ) isOpen_univ))).hom s)) =
      FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _ f
        (tateInvGlobalPatchEquiv hq hI s) :=
  (FormalSpectrum.globalSectionsMap_sectionsEquivOfEqTop (annulusIdealOfDefinition R I q) _ f
    tateInvPatchSaturateOpens_univ (map_base_tateInvPatchSaturateOpens_univ _) hf s).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `x`-chart leg is `Γ` of the `x`-chart.** -/
theorem tateInvGlobalXEquiv_tateInvChartLegX (hq : q ∈ I) (hI : I.FG)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))) :
    tateInvGlobalXEquiv hq hI (tateInvChartLegX (hq := hq) (hI := hI) isOpen_univ s) =
      FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        (annulusOverlapChart R I q) (tateInvGlobalPatchEquiv hq hI s) := by
  refine Eq.trans ?_ (tateInvGlobalXEquiv_c_app hq hI (annulusOverlapChart R I q) rfl s)
  congr 1
  simp only [tateInvChartLegX, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- **The transition-then-`y`-chart leg is `Γ` of that composite.** -/
theorem tateInvGlobalXEquiv_tateInvChartLegYX (hq : q ∈ I) (hI : I.FG)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))) :
    tateInvGlobalXEquiv hq hI (tateInvChartLegYX (hq := hq) (hI := hI) isOpen_univ s) =
      FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q)
        (tateInvGlobalPatchEquiv hq hI s) :=
  tateInvGlobalXEquiv_c_app hq hI _
    (map_annulusOverlapChartY_tateInvPatchSaturateOpens (hq := hq) (hI := hI) isOpen_univ) s

end X

section Y

variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))]

/-- **The `y`-overlap's sections over the open both backward legs are read on are `A{1/y}`.** -/
def tateInvGlobalYEquiv (hq : q ∈ I) (hI : I.FG) :
    ((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (overlapY R I q))).presheaf.obj
      (op ((Opens.map (annulusOverlapChartY R I q).base).obj
        (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
          isOpen_univ))) : Type u) ≃+*
      awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  FormalSpectrum.sectionsEquivOfEqTop _ (map_base_tateInvPatchSaturateOpens_univ _)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A backward leg is its global-sections map.** The mirror of
`tateInvGlobalXEquiv_c_app`, and abstract in `f` for the same reason. -/
theorem tateInvGlobalYEquiv_c_app (hq : q ∈ I) (hI : I.FG)
    (f : FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
        (annulusIdealOfDefinition R I q) (overlapY R I q)) ⟶
      FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))
    (hf : (Opens.map f.base).obj
        (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI isOpen_univ) =
      (Opens.map (annulusOverlapChartY R I q).base).obj
        (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI isOpen_univ))
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))) :
    tateInvGlobalYEquiv hq hI
        (((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
          (annulusIdealOfDefinition R I q) (overlapY R I q))).presheaf.map
            (eqToHom (congrArg op hf))).hom ((f.c.app (op (tateInvPatchSaturateOpens hq hI
              (S := Set.univ) isOpen_univ))).hom s)) =
      FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _ f
        (tateInvGlobalPatchEquiv hq hI s) :=
  (FormalSpectrum.globalSectionsMap_sectionsEquivOfEqTop (annulusIdealOfDefinition R I q) _ f
    tateInvPatchSaturateOpens_univ (map_base_tateInvPatchSaturateOpens_univ _) hf s).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `y`-chart leg is `Γ` of the `y`-chart.** -/
theorem tateInvGlobalYEquiv_tateInvChartLegY (hq : q ∈ I) (hI : I.FG)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))) :
    tateInvGlobalYEquiv hq hI (tateInvChartLegY (hq := hq) (hI := hI) isOpen_univ s) =
      FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        (annulusOverlapChartY R I q) (tateInvGlobalPatchEquiv hq hI s) := by
  refine Eq.trans ?_ (tateInvGlobalYEquiv_c_app hq hI (annulusOverlapChartY R I q) rfl s)
  congr 1
  simp only [tateInvChartLegY, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- **The inverse-transition-then-`x`-chart leg is `Γ` of that composite.** -/
theorem tateInvGlobalYEquiv_tateInvChartLegXY (hq : q ∈ I) (hI : I.FG)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))) :
    tateInvGlobalYEquiv hq hI (tateInvChartLegXY (hq := hq) (hI := hI) isOpen_univ s) =
      FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        ((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q)
        (tateInvGlobalPatchEquiv hq hI s) :=
  tateInvGlobalYEquiv_c_app hq hI _
    (map_annulusOverlapChart_tateInvPatchSaturateOpens (hq := hq) (hI := hI) isOpen_univ) s

end Y

/-! ### The legs, in the coordinates of `A` -/

section XY

variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- `Γ` of the `x`-chart is `awayCompletionHom` at `x`: the chart **is**
`FormalSpectrum.basicOpenChart` at `overlapX`, so this is
`FormalSpectrum.globalSectionsMap_basicOpenChart`. -/
theorem globalSectionsMap_annulusOverlapChart :
    FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        (annulusOverlapChart R I q) = tateInvGlobalLegX (R := R) (I := I) (q := q) :=
  FormalSpectrum.globalSectionsMap_basicOpenChart _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- `Γ` of the `y`-chart is `awayCompletionHom` at `y`. Note `annulusOverlapChartY` is
`FormalSpectrum.basicOpenChart` at `overlapY` by definition and not by a named lemma. -/
theorem globalSectionsMap_annulusOverlapChartY :
    FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        (annulusOverlapChartY R I q) = tateInvGlobalLegY (R := R) (I := I) (q := q) :=
  FormalSpectrum.globalSectionsMap_basicOpenChart _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
  [IsAdicRing (annulusIdealOfDefinition R I q)] in
/-- `Γ` of the `𝔾m`-inversion transition is its `R`-algebra avatar, by
`AlgebraicGeometry.annulusChartTransitionInvSpf_hom_eq` (the transition is `Spf` of a ring map)
and `FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap` (EGA I 10.4.6). -/
theorem globalSectionsMap_annulusChartTransitionInvSpf_hom (hI : I.FG) :
    FormalSpectrum.globalSectionsMap _ _ (annulusChartTransitionInvSpf R I q hI).hom =
      (annulusChartTransitionInvAlg R I q hI).symm.toRingHom := by
  rw [annulusChartTransitionInvSpf_hom_eq R I q hI]
  exact FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap _ _ _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
  [IsAdicRing (annulusIdealOfDefinition R I q)] in
/-- `Γ` of the inverse transition is the forward `R`-algebra avatar. Derived from the previous
theorem by functoriality (`FormalSpectrum.globalSectionsMap_comp` and `_id`) rather than by
re-running `annulusChartTransitionInvSpf_hom_eq`'s proof, which needs a raised heartbeat budget. -/
theorem globalSectionsMap_annulusChartTransitionInvSpf_inv (hI : I.FG) :
    FormalSpectrum.globalSectionsMap _ _ (annulusChartTransitionInvSpf R I q hI).inv =
      (annulusChartTransitionInvAlg R I q hI).toRingHom := by
  refine RingHom.ext fun a => ?_
  have hcomp := FormalSpectrum.globalSectionsMap_comp
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    (annulusChartTransitionInvSpf R I q hI).hom (annulusChartTransitionInvSpf R I q hI).inv
  rw [(annulusChartTransitionInvSpf R I q hI).hom_inv_id, FormalSpectrum.globalSectionsMap_id,
    globalSectionsMap_annulusChartTransitionInvSpf_hom] at hcomp
  have hpt := congrArg (fun φ : awayCompletion (annulusIdealOfDefinition R I q)
    (overlapX R I q) →+* _ => φ a) hcomp
  simp only [RingHom.id_apply, RingHom.comp_apply] at hpt
  exact ((congrArg (annulusChartTransitionInvAlg R I q hI) hpt).trans
    ((annulusChartTransitionInvAlg R I q hI).apply_symm_apply _)).symm

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- `Γ` of the transition-then-`y`-chart composite is `tateInvGlobalLegYX`. Contravariant, so the
transition's map comes second. -/
theorem globalSectionsMap_transitionInv_comp_chartY (hI : I.FG) :
    FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q) =
      tateInvGlobalLegYX hI := by
  rw [FormalSpectrum.globalSectionsMap_comp,
    globalSectionsMap_annulusChartTransitionInvSpf_hom, globalSectionsMap_annulusOverlapChartY]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- `Γ` of the inverse-transition-then-`x`-chart composite is `tateInvGlobalLegXY`. -/
theorem globalSectionsMap_transitionInv_inv_comp_chart (hI : I.FG) :
    FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
        ((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q) =
      tateInvGlobalLegXY hI := by
  rw [FormalSpectrum.globalSectionsMap_comp,
    globalSectionsMap_annulusChartTransitionInvSpf_inv, globalSectionsMap_annulusOverlapChart]
  rfl

/-! ### The subring, transported -/

set_option maxHeartbeats 800000 in
-- Each of the two `rw` chains re-elaborates a `c`-component over the collapsed open, and the two
-- share one declaration's heartbeat budget.
/-- **The two chart conditions at `S = Set.univ` are the two equations in `A`.** A section of the
model patch over the whole patch satisfies
`AlgebraicGeometry.IsTateInvChartCompatibleForward`/`Backward` exactly when the element of `A` it
corresponds to lies in `tateInvGlobalSubring`. This is where the presheaf leaves the statement. -/
theorem mem_tateInvChartAnnulusSubring_iff_mem_tateInvGlobalSubring (hq : q ∈ I) (hI : I.FG)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))) :
    s ∈ tateInvChartAnnulusSubring (hq := hq) (hI := hI) isOpen_univ ↔
      tateInvGlobalPatchEquiv hq hI s ∈ tateInvGlobalSubring hI := by
  rw [mem_tateInvChartAnnulusSubring_iff, mem_tateInvGlobalSubring_iff]
  refine and_congr ?_ ?_
  · rw [isTateInvChartCompatibleForward_iff, ← (tateInvGlobalXEquiv hq hI).injective.eq_iff,
      tateInvGlobalXEquiv_tateInvChartLegX, tateInvGlobalXEquiv_tateInvChartLegYX,
      globalSectionsMap_annulusOverlapChart, globalSectionsMap_transitionInv_comp_chartY]
  · rw [isTateInvChartCompatibleBackward_iff, ← (tateInvGlobalYEquiv hq hI).injective.eq_iff,
      tateInvGlobalYEquiv_tateInvChartLegY, tateInvGlobalYEquiv_tateInvChartLegXY,
      globalSectionsMap_annulusOverlapChartY, globalSectionsMap_transitionInv_inv_comp_chart]

end XY

end GlobalCollapse

/-! ### `Γ (T_inv/⟨σ⟩)` -/

/-- **`Γ (T_inv/⟨σ⟩)` is the subring of `A = R{x, y}/(x·y − q)` cut out by two equations.**

`V = ⊤` is exhibited, not assumed: `map_actionQuotientπ_top_eq` says the preimage of `⊤` under the
quotient projection is the saturation of `Set.univ`, so
`AlgebraicGeometry.tateInvChartAnnulusRingEquiv` (`FormalSchemes.TateInvChartAnnulusRing`) applies
at `V = ⊤` and `S = Set.univ`, and
`mem_tateInvChartAnnulusSubring_iff_mem_tateInvGlobalSubring` restricts the identification of the
patch's sections with `A` to the two subrings.

No locally ringed space, no glue datum and no presheaf occurs in `tateInvGlobalSubring`: its two
equations are between composites of `FormalSpectrum.awayCompletionHom` and
`AlgebraicGeometry.annulusChartTransitionInvAlg`. Nothing here says the quotient is a formal
scheme, and nothing here is a chart. -/
def tateInvGlobalSectionsRingEquiv (hq : q ∈ I) (hI : I.FG) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (⊤ : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat))) ≃+*
      tateInvGlobalSubring (R := R) (I := I) (q := q) hI :=
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hax : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hay : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  (tateInvChartAnnulusRingEquiv (⊤ : Opens (actionQuotient
      (tateInvPeriodAction R I q hq hI)).toTopCat) isOpen_univ map_actionQuotientπ_top_eq).trans
    (RingEquiv.restrict (tateInvGlobalPatchEquiv hq hI) _ _
      (mem_tateInvChartAnnulusSubring_iff_mem_tateInvGlobalSubring hq hI))

end AlgebraicGeometry
