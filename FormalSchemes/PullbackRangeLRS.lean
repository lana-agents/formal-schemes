import Mathlib.Geometry.RingedSpace.OpenImmersion

set_option linter.style.header false

/-!
# Ranges of pullbacks of open immersions of locally ringed spaces

Let `X, Y, Z` be locally ringed spaces and `f : X ⟶ Z`, `g : Y ⟶ Z` two open immersions. This file
records two general facts about the pullback `X ×_Z Y`, both purely at the level of
`LocallyRingedSpace` and its underlying spaces:

* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_snd`: the range of the
  underlying map of `pullback.snd f g` is the preimage `g⁻¹(im f)`. This is the locally-ringed-space
  analogue of the scheme-level `AlgebraicGeometry.range_pullbackSnd`.
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_fst_comp`: the range of the
  underlying map of `pullback.fst f g ≫ f` (the canonical map `X ×_Z Y ⟶ Z`) is the intersection
  `im f ∩ im g` of the two images.
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq`: any open immersion
  `h : W ⟶ Z` whose image is exactly `im f ∩ im g` is canonically isomorphic to the pullback
  `X ×_Z Y`, compatibly with the maps down to the common target `Z`.

These are the geometric input to identifying a triple-overlap `V i j` of a glue datum, cut out as an
open immersion of prescribed image, with the pullback of two of its open charts.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

variable {X Y Z W : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- The range of the underlying map of `pullback.snd f g` is `g⁻¹(im f)`. This is the
locally-ringed-space analogue of `AlgebraicGeometry.range_pullbackSnd`; its proof mirrors that of
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_range`. -/
theorem range_pullback_snd [LocallyRingedSpace.IsOpenImmersion f] :
    Set.range (pullback.snd f g).base = g.base ⁻¹' Set.range f.base := by
  rw [← show _ = (pullback.snd f g).base from
        PreservesPullback.iso_hom_snd
          (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g,
      TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr,
      ← @Set.preimage_univ _ _ (pullback.fst f.base g.base)]
  · erw [TopCat.pullback_snd_image_fst_preimage]
    rw [Set.image_univ]
    rfl
  · rw [← TopCat.epi_iff_surjective]
    infer_instance

/-- The range of the underlying map of the canonical map `pullback.fst f g ≫ f : X ×_Z Y ⟶ Z` is the
intersection `im f ∩ im g` of the two images. This is the locally-ringed-space analogue of
`AlgebraicGeometry.range_pullback_to_base_of_left`. -/
theorem range_pullback_fst_comp [LocallyRingedSpace.IsOpenImmersion f]
    [LocallyRingedSpace.IsOpenImmersion g] :
    Set.range (pullback.fst f g ≫ f).base = Set.range f.base ∩ Set.range g.base := by
  rw [pullback.condition, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullback_snd, Set.image_preimage_eq_inter_range]

/-- Any open immersion `h : W ⟶ Z` whose image is exactly `im f ∩ im g` is canonically isomorphic to
the pullback `X ×_Z Y`, compatibly with the maps down to the common target `Z`
(see `pullbackIsoOfRangeEq_hom_fst_comp`).

The isomorphism is built by the universal property of open immersions: since the canonical map
`pullback.fst f g ≫ f : X ×_Z Y ⟶ Z` and `h` have equal images
(`range_pullback_fst_comp`), each lifts uniquely through the other, and the two lifts are mutually
inverse. -/
noncomputable def pullbackIsoOfRangeEq (h : W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    [LocallyRingedSpace.IsOpenImmersion h]
    (e : Set.range h.base = Set.range f.base ∩ Set.range g.base) :
    W ≅ pullback f g where
  hom := lift (pullback.fst f g ≫ f) h (by rw [e]; exact (range_pullback_fst_comp f g).ge)
  inv := lift h (pullback.fst f g ≫ f) (by rw [range_pullback_fst_comp]; exact e.ge)
  hom_inv_id := by
    rw [← cancel_mono h, Category.assoc, Category.id_comp, lift_fac, lift_fac]
  inv_hom_id := by
    rw [← cancel_mono (pullback.fst f g ≫ f), Category.assoc, Category.id_comp, lift_fac, lift_fac]

@[reassoc]
theorem pullbackIsoOfRangeEq_hom_fst_comp (h : W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    [LocallyRingedSpace.IsOpenImmersion h]
    (e : Set.range h.base = Set.range f.base ∩ Set.range g.base) :
    (pullbackIsoOfRangeEq f g h e).hom ≫ pullback.fst f g ≫ f = h :=
  lift_fac (pullback.fst f g ≫ f) h (by rw [e]; exact (range_pullback_fst_comp f g).ge)

@[reassoc]
theorem pullbackIsoOfRangeEq_hom_snd_comp (h : W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    [LocallyRingedSpace.IsOpenImmersion h]
    (e : Set.range h.base = Set.range f.base ∩ Set.range g.base) :
    (pullbackIsoOfRangeEq f g h e).hom ≫ pullback.snd f g ≫ g = h := by
  rw [← pullback.condition]
  exact pullbackIsoOfRangeEq_hom_fst_comp f g h e

@[reassoc]
theorem pullbackIsoOfRangeEq_inv_comp (h : W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    [LocallyRingedSpace.IsOpenImmersion h]
    (e : Set.range h.base = Set.range f.base ∩ Set.range g.base) :
    (pullbackIsoOfRangeEq f g h e).inv ≫ h = pullback.fst f g ≫ f :=
  lift_fac h (pullback.fst f g ≫ f) (by rw [range_pullback_fst_comp]; exact e.ge)

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
