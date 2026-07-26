import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Algebra.Category.Ring.Constructions

set_option linter.style.header false

/-!
# Coproducts of open immersions of locally ringed spaces

Let `X, Y, Z` be locally ringed spaces and `f : X ⟶ Z`, `g : Y ⟶ Z` two open immersions whose
underlying-space images are disjoint. Then the induced map out of the coproduct

`coprod.desc f g : X ⨿ Y ⟶ Z`

is again an open immersion. Geometrically, the binary coproduct `X ⨿ Y` is the disjoint union of
`X` and `Y`, and `coprod.desc f g` realises it as the open subspace `im f ∪ im g` of `Z`.

This is the locally-ringed-space input to the two-chart Tate-curve model `𝔈_q = T/q^ℤ` (issue 223):
the overlap object `V(0,1)` of the two-patch glue datum is the coproduct of the two formal-`Ĝm`
charts `Spf A{1/x} ⊔ Spf A{1/y}`, and the combined overlap chart into a patch `Spf A` is exactly
`coprod.desc` of the two affine overlap charts, whose images `D(x)` and `D(y)` are disjoint
(`annulusOverlapChart_range_disjoint`).

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_coprod_inl` /
  `isOpenImmersion_coprod_inr`: the two coproduct inclusions `X ⟶ X ⨿ Y`, `Y ⟶ X ⨿ Y` are open
  immersions.
* `AlgebraicGeometry.LocallyRingedSpace.isCompl_range_coprod_inl_inr`: their underlying-space ranges
  are complementary (disjoint and covering).
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.coprodDesc`: the coproduct of two open
  immersions with disjoint images is an open immersion.

The proof reuses Mathlib's `SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion` (coproduct
inclusions of sheafed spaces over a category with strict terminal objects are open immersions —
`CommRingCat` qualifies) transported along `LocallyRingedSpace.forgetToSheafedSpace`, together with
`SheafedSpace.IsOpenImmersion.of_stalk_iso` (a topological open embedding with iso stalks is an open
immersion).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}

section CoprodInclusions

/-- Coproduct inclusions of sheafed spaces (over `CommRingCat`, which has strict terminal objects)
are open immersions — a repackaging of `sigma_ι_isOpenImmersion` for the binary coproduct. -/
instance sheafedSpace_isOpenImmersion_coprod_inl {A B : SheafedSpace CommRingCat.{u}} :
    SheafedSpace.IsOpenImmersion (coprod.inl : A ⟶ A ⨿ B) :=
  SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion (pair A B) ⟨WalkingPair.left⟩

instance sheafedSpace_isOpenImmersion_coprod_inr {A B : SheafedSpace CommRingCat.{u}} :
    SheafedSpace.IsOpenImmersion (coprod.inr : B ⟶ A ⨿ B) :=
  SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion (pair A B) ⟨WalkingPair.right⟩

/-- The left coproduct inclusion is an open immersion: under `forgetToSheafedSpace` it is the
sheafed-space coproduct inclusion (an open immersion) postcomposed with the coproduct-comparison
isomorphism. -/
instance isOpenImmersion_coprod_inl :
    LocallyRingedSpace.IsOpenImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  haveI hg : IsIso (coprodComparison forgetToSheafedSpace X Y) := by
    rw [← PreservesColimitPair.iso_hom]; infer_instance
  -- `LocallyRingedSpace.IsOpenImmersion (coprod.inl)` unfolds definitionally to the sheafed-space
  -- statement about `forgetToSheafedSpace.map coprod.inl`, which factors through the coproduct
  -- comparison. We supply both factors' open-immersion instances explicitly: instance search
  -- stumbles on a `HasBinaryCoproduct` diamond at the `SheafedSpace` level, so we hand it
  -- `sheafedSpace_…_inl` for the left factor and `of_isIso hg` for the comparison isomorphism.
  have key : SheafedSpace.IsOpenImmersion (forgetToSheafedSpace.map (coprod.inl : X ⟶ X ⨿ Y)) := by
    rw [← coprodComparison_inl (F := forgetToSheafedSpace) (A := X) (B := Y)]
    exact @SheafedSpace.IsOpenImmersion.comp _ _ _ _ _ _ (coprodComparison forgetToSheafedSpace X Y)
      sheafedSpace_isOpenImmersion_coprod_inl
      (@SheafedSpace.IsOpenImmersion.of_isIso _ _ _ _ _ hg)
  exact key

instance isOpenImmersion_coprod_inr :
    LocallyRingedSpace.IsOpenImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  haveI hg : IsIso (coprodComparison forgetToSheafedSpace X Y) := by
    rw [← PreservesColimitPair.iso_hom]; infer_instance
  -- As for `inl`, supply both factors' instances explicitly to dodge the `HasBinaryCoproduct`
  -- diamond at the `SheafedSpace` level.
  have key : SheafedSpace.IsOpenImmersion (forgetToSheafedSpace.map (coprod.inr : Y ⟶ X ⨿ Y)) := by
    rw [← coprodComparison_inr (F := forgetToSheafedSpace) (A := X) (B := Y)]
    exact @SheafedSpace.IsOpenImmersion.comp _ _ _ _ _ _ (coprodComparison forgetToSheafedSpace X Y)
      sheafedSpace_isOpenImmersion_coprod_inr
      (@SheafedSpace.IsOpenImmersion.of_isIso _ _ _ _ _ hg)
  exact key

end CoprodInclusions

section Topology

/-- Underlying-space description of the binary coproduct: the two coproduct inclusions are open
embeddings with complementary ranges. This is `TopCat.binaryCofan_isColimit_iff` applied to the
coproduct cofan pushed forward along the colimit-preserving functor `forgetToTop`. -/
theorem coprod_base_isCompl_and_isOpenEmbedding :
    IsOpenEmbedding (coprod.inl : X ⟶ X ⨿ Y).base ∧
      IsOpenEmbedding (coprod.inr : Y ⟶ X ⨿ Y).base ∧
        IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y).base)
          (Set.range (coprod.inr : Y ⟶ X ⨿ Y).base) := by
  haveI : PreservesColimit (pair X Y) forgetToTop.{u} :=
    inferInstanceAs
      (PreservesColimit (pair X Y) (forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat.{u}))
  exact (TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit forgetToTop _ _ (coprodIsCoprod X Y)⟩

theorem isOpenEmbedding_coprod_inl_base :
    IsOpenEmbedding (coprod.inl : X ⟶ X ⨿ Y).base :=
  coprod_base_isCompl_and_isOpenEmbedding.1

theorem isOpenEmbedding_coprod_inr_base :
    IsOpenEmbedding (coprod.inr : Y ⟶ X ⨿ Y).base :=
  coprod_base_isCompl_and_isOpenEmbedding.2.1

/-- The underlying-space ranges of the two coproduct inclusions are complementary. -/
theorem isCompl_range_coprod_inl_inr :
    IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range (coprod.inr : Y ⟶ X ⨿ Y).base) :=
  coprod_base_isCompl_and_isOpenEmbedding.2.2

/-- The two coproduct inclusions cover the coproduct. -/
theorem range_coprod_inl_union_inr :
    Set.range (coprod.inl : X ⟶ X ⨿ Y).base ∪ Set.range (coprod.inr : Y ⟶ X ⨿ Y).base =
      Set.univ := by
  have h := (isCompl_range_coprod_inl_inr (X := X) (Y := Y)).codisjoint
  rw [codisjoint_iff] at h
  exact h

/-- Every point of the coproduct is in the image of one of the two inclusions. -/
theorem coprod_base_mem_range (w : (X ⨿ Y : LocallyRingedSpace.{u})) :
    w ∈ Set.range (coprod.inl : X ⟶ X ⨿ Y).base ∨
      w ∈ Set.range (coprod.inr : Y ⟶ X ⨿ Y).base :=
  (Set.mem_union _ _ _).mp (range_coprod_inl_union_inr (X := X) (Y := Y) ▸ Set.mem_univ w)

end Topology

namespace IsOpenImmersion

variable (f : X ⟶ Z) (g : Y ⟶ Z)
variable [hf : LocallyRingedSpace.IsOpenImmersion f] [hg : LocallyRingedSpace.IsOpenImmersion g]

omit hf hg in
/-- The base map `d.base` of `coprod.desc f g` composed with the left inclusion is `f.base`. -/
theorem coprodDesc_base_comp_inl :
    (coprod.inl : X ⟶ X ⨿ Y).base ≫ (coprod.desc f g).base = f.base := by
  rw [← comp_base, coprod.inl_desc]

omit hf hg in
theorem coprodDesc_base_comp_inr :
    (coprod.inr : Y ⟶ X ⨿ Y).base ≫ (coprod.desc f g).base = g.base := by
  rw [← comp_base, coprod.inr_desc]

/-- Each stalk map of `coprod.desc f g` is an isomorphism: at a point coming from `X` it factors
the iso `f.stalkMap` through the iso `(coprod.inl).stalkMap`, and dually for `Y`. -/
theorem isIso_coprodDesc_stalkMap (w : (X ⨿ Y : LocallyRingedSpace.{u})) :
    IsIso ((coprod.desc f g).stalkMap w) := by
  rcases coprod_base_mem_range w with ⟨a, ha⟩ | ⟨b, hb⟩
  · subst ha
    -- `(coprod.inl ≫ coprod.desc f g).stalkMap a = f.stalkMap a` is an iso (since `f` is);
    -- its factorisation `desc.stalkMap ≫ inl.stalkMap` then forces `desc.stalkMap` to be an iso.
    haveI : IsIso ((coprod.inl : X ⟶ X ⨿ Y).stalkMap a) := inferInstance
    haveI hcompiso : IsIso ((coprod.inl ≫ coprod.desc f g : X ⟶ Z).stalkMap a) := by
      rw [coprod.inl_desc]; infer_instance
    rw [stalkMap_comp] at hcompiso
    exact (isIso_comp_right_iff _ ((coprod.inl : X ⟶ X ⨿ Y).stalkMap a)).mp hcompiso
  · subst hb
    haveI : IsIso ((coprod.inr : Y ⟶ X ⨿ Y).stalkMap b) := inferInstance
    haveI hcompiso : IsIso ((coprod.inr ≫ coprod.desc f g : Y ⟶ Z).stalkMap b) := by
      rw [coprod.inr_desc]; infer_instance
    rw [stalkMap_comp] at hcompiso
    exact (isIso_comp_right_iff _ ((coprod.inr : Y ⟶ X ⨿ Y).stalkMap b)).mp hcompiso

/-- The base map of `coprod.desc f g` is an open embedding, provided `f` and `g` have disjoint
images. -/
theorem isOpenEmbedding_coprodDesc_base
    (h : Disjoint (Set.range f.base) (Set.range g.base)) :
    IsOpenEmbedding (coprod.desc f g).base := by
  have hfb : IsOpenEmbedding f.base := hf.base_open
  have hgb : IsOpenEmbedding g.base := hg.base_open
  have hil : IsOpenEmbedding (coprod.inl : X ⟶ X ⨿ Y).base := isOpenEmbedding_coprod_inl_base
  have hir : IsOpenEmbedding (coprod.inr : Y ⟶ X ⨿ Y).base := isOpenEmbedding_coprod_inr_base
  have hcl : ∀ a, (coprod.desc f g).base ((coprod.inl : X ⟶ X ⨿ Y).base a) = f.base a :=
    fun a => congrArg (fun m => m a) (coprodDesc_base_comp_inl f g)
  have hcr : ∀ b, (coprod.desc f g).base ((coprod.inr : Y ⟶ X ⨿ Y).base b) = g.base b :=
    fun b => congrArg (fun m => m b) (coprodDesc_base_comp_inr f g)
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (coprod.desc f g).base.hom.continuous ?_ ?_
  · -- injectivity
    intro w w' hww'
    rcases coprod_base_mem_range w with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases coprod_base_mem_range w' with ⟨a', ha'⟩ | ⟨a', ha'⟩ <;>
      subst ha <;> subst ha'
    · rw [hcl, hcl] at hww'
      rw [hil.injective.eq_iff.mpr (hfb.injective hww')]
    · rw [hcl, hcr] at hww'
      exact (Set.disjoint_left.mp h ⟨a, rfl⟩ ⟨a', hww'.symm⟩).elim
    · rw [hcr, hcl] at hww'
      exact (Set.disjoint_left.mp h ⟨a', rfl⟩ ⟨a, hww'⟩).elim
    · rw [hcr, hcr] at hww'
      rw [hir.injective.eq_iff.mpr (hgb.injective hww')]
  · -- open map
    intro U hU
    have hcov : U = (U ∩ Set.range (coprod.inl : X ⟶ X ⨿ Y).base) ∪
        (U ∩ Set.range (coprod.inr : Y ⟶ X ⨿ Y).base) := by
      rw [← Set.inter_union_distrib_left, range_coprod_inl_union_inr, Set.inter_univ]
    rw [hcov, Set.image_union]
    apply IsOpen.union
    · have himg : (coprod.desc f g).base '' (U ∩ Set.range (coprod.inl : X ⟶ X ⨿ Y).base) =
          f.base '' ((coprod.inl : X ⟶ X ⨿ Y).base ⁻¹' U) := by
        rw [← Set.image_preimage_eq_inter_range, ← Set.image_comp]
        exact Set.image_congr' (fun a => hcl a)
      rw [himg]
      exact hfb.isOpenMap _ (hil.continuous.isOpen_preimage _ hU)
    · have himg : (coprod.desc f g).base '' (U ∩ Set.range (coprod.inr : Y ⟶ X ⨿ Y).base) =
          g.base '' ((coprod.inr : Y ⟶ X ⨿ Y).base ⁻¹' U) := by
        rw [← Set.image_preimage_eq_inter_range, ← Set.image_comp]
        exact Set.image_congr' (fun b => hcr b)
      rw [himg]
      exact hgb.isOpenMap _ (hir.continuous.isOpen_preimage _ hU)

/-- **The coproduct of two open immersions with disjoint images is an open immersion.** -/
theorem coprodDesc (h : Disjoint (Set.range f.base) (Set.range g.base)) :
    LocallyRingedSpace.IsOpenImmersion (coprod.desc f g) := by
  have hbase : IsOpenEmbedding (coprod.desc f g).base := isOpenEmbedding_coprodDesc_base f g h
  exact SheafedSpace.IsOpenImmersion.of_stalk_iso (coprod.desc f g).toShHom hbase
    (H := fun w => isIso_coprodDesc_stalkMap f g w)

end IsOpenImmersion

end AlgebraicGeometry.LocallyRingedSpace
