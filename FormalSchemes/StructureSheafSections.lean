import FormalSchemes.StructureSheaf
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

set_option linter.style.header false

/-!
# Sections of the structure sheaf of the formal spectrum

The structure sheaf `O_{Spf R}` of the formal spectrum of an adic ring `R` with ideal of
definition `I` is, by construction (`FormalSpectrum.structureSheaf`), the limit of the inverse
system `FormalSpectrum.structureSheafFunctor I` of the structure sheaves of the infinitesimal
thickenings `Spec (R ⧸ I ^ (n + 1))`, transported to `Spf R`.

Because the forgetful functor `TopCat.Sheaf.forget` *creates* limits and limits of presheaves are
computed pointwise (evaluation preserves limits), the sections of `O_{Spf R}` over any fixed open
`U` are the limit, in `CommRingCat`, of the tower `n ↦ Γ(U, thickeningSheaf I n)`. This file records
that description (`FormalSpectrum.sectionsLimitIso`), which is the entry point for identifying
sections on basic opens `D(f)` with the `I`-adic completion of the localization `R_f` (EGA I
10.5.6ff / Stacks Tag 0AI7).

## Main definitions

* `FormalSpectrum.sectionsFunctor I U`: the functor sending a sheaf of rings on `Spf R` to its ring
  of sections over the open `U`, i.e. `TopCat.Sheaf.forget` followed by evaluation at `U`.
* `FormalSpectrum.sectionsLimitIso I U`: the ring isomorphism `Γ(U, O_{Spf R}) ≅ lim_n Γ(U,
  thickeningSheaf I n)` exhibiting sections of `O_{Spf R}` as the limit of the tower of sections of
  the thickening sheaves.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §10.5.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

variable {R : Type*} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

namespace FormalSpectrum

/-- The functor sending a sheaf of commutative rings on `Spf R` to its ring of sections over a
fixed open `U`, obtained by forgetting the sheaf condition and evaluating the underlying presheaf
at `U`. It preserves limits, since `TopCat.Sheaf.forget` creates limits and evaluation preserves
them. -/
abbrev sectionsFunctor (U : (Opens ↑(TopCat.of (FormalSpectrum I)))ᵒᵖ) :
    TopCat.Sheaf CommRingCat (TopCat.of (FormalSpectrum I)) ⥤ CommRingCat :=
  TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I)) ⋙ (evaluation _ _).obj U

/-- The ring of sections of `O_{Spf R}` over an open `U` is the limit, in `CommRingCat`, of the
tower `n ↦ Γ(U, thickeningSheaf I n)` of sections of the structure sheaves of the infinitesimal
thickenings. This is the pointwise description of the limit sheaf `O_{Spf R}`, valid because
`TopCat.Sheaf.forget` creates limits and evaluation preserves them. -/
def sectionsLimitIso (U : (Opens ↑(TopCat.of (FormalSpectrum I)))ᵒᵖ) :
    (structureSheaf I).presheaf.obj U ≅
      limit (structureSheafFunctor I ⋙ sectionsFunctor I U) :=
  haveI _hf : PreservesLimitsOfShape ℕᵒᵖ
      (TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _
  -- `Sheaf.forget` preserves the limit, so the underlying presheaf of `O_{Spf R}` is the limit of
  -- the underlying presheaves of the thickening sheaves; then evaluate this presheaf limit at `U`.
  ((evaluation (Opens ↑(TopCat.of (FormalSpectrum I)))ᵒᵖ CommRingCat).obj U).mapIso
      (preservesLimitIso (TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I)))
        (structureSheafFunctor I)) ≪≫
    limitObjIsoLimitCompEvaluation
      (structureSheafFunctor I ⋙ TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) U

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The identification `sectionsLimitIso` is compatible with the projections: composing with
the limit projection at level `n` recovers the component at `U` of the limit projection of
sheaves. -/
theorem sectionsLimitIso_hom_π (U : (Opens ↑(TopCat.of (FormalSpectrum I)))ᵒᵖ) (n : ℕ) :
    (sectionsLimitIso I U).hom ≫
        limit.π (structureSheafFunctor I ⋙ sectionsFunctor I U) ⟨n⟩ =
      (limit.π (structureSheafFunctor I) ⟨n⟩).hom.app U := by
  haveI _hf : PreservesLimitsOfShape ℕᵒᵖ
      (TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _
  have key : (limitObjIsoLimitCompEvaluation
        (structureSheafFunctor I ⋙
          TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) U).hom ≫
      limit.π ((structureSheafFunctor I ⋙
          TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) ⋙
        (evaluation (Opens ↑(TopCat.of (FormalSpectrum I)))ᵒᵖ CommRingCat).obj U) ⟨n⟩ =
      (limit.π (structureSheafFunctor I ⋙
        TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) ⟨n⟩).app U :=
    limitObjIsoLimitCompEvaluation_hom_π _ _ _
  have key2 : (preservesLimitIso
        (TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I)))
        (structureSheafFunctor I)).hom ≫
      limit.π (structureSheafFunctor I ⋙
        TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) ⟨n⟩ =
      (TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))).map
        (limit.π (structureSheafFunctor I) ⟨n⟩) :=
    preservesLimitIso_hom_π _ _ _
  have key2' : (preservesLimitIso
        (TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I)))
        (structureSheafFunctor I)).hom.app U ≫
      (limit.π (structureSheafFunctor I ⋙
        TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I))) ⟨n⟩).app U =
      (limit.π (structureSheafFunctor I) ⟨n⟩).hom.app U :=
    NatTrans.congr_app key2 U
  refine Eq.trans ?_ key2'
  rw [← key]
  rfl

end FormalSpectrum
