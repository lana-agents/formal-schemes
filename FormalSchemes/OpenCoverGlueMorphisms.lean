import FormalSchemes.OpenCoverHomExt
import FormalSchemes.GlueMorphisms
import FormalSchemes.GlueDataCarrier

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Gluing morphisms out of an open cover of a formal scheme

Given an open cover `𝒰 : FormalScheme.OpenCover X` and a family of morphisms `k j : 𝒰.obj j ⟶ Y`
(to any locally ringed space `Y`) that agree on the pairwise overlaps, we assemble a single
morphism `X.toLocallyRingedSpace ⟶ Y`. This is the *construction* half of descent for morphisms
of formal schemes; its uniqueness companion `OpenCover.hom_ext` is in `OpenCoverHomExt.lean`
(issue 397). Together they exhibit an open cover as a jointly effective-epimorphic family, the
load-bearing input to the mediating-morphism half of the general fibre-product universal property
(EGA I §10.7).

## Strategy

We mirror Mathlib's `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms`. From the cover `𝒰` we build
a `FormalScheme.GlueData` `𝒰.gluedCover` whose pieces are the `𝒰.obj i` and whose overlaps are the
locally ringed space pullbacks `𝒰.obj i ×_X 𝒰.obj j` (these exist because the cover maps are open
immersions, `LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left`). The canonical morphism
`𝒰.fromGlued : 𝒰.gluedCover.gluedFormalScheme ⟶ X` (glued from the cover maps via
`GlueData.glueMorphisms`) is an isomorphism: it is an open immersion whose base map is surjective,
so `LocallyRingedSpace.IsOpenImmersion.to_iso` applies. Precomposing the glued-object morphism
`GlueData.glueMorphisms` with `inv 𝒰.fromGlued` then produces the desired morphism out of `X`.

## Main definitions

* `FormalScheme.OpenCover.gluedCover`: the glue data associated to an open cover.
* `FormalScheme.OpenCover.fromGlued`: the canonical morphism from the glued cover into `X`, an iso.
* `FormalScheme.OpenCover.glueMorphisms`: the glued morphism `X ⟶ Y`.
* `FormalScheme.OpenCover.map_glueMorphisms`: its restriction to the `j`-th piece is `k j`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms` / `fromGlued`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.FormalScheme.OpenCover

variable {X : FormalScheme.{u}} (𝒰 : OpenCover.{u} X)

/-- The underlying locally ringed space map of the `i`-th cover piece. -/
abbrev cmap (i : 𝒰.J) : (𝒰.obj i).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  (𝒰.map i).toLRSHom

instance (i : 𝒰.J) : LocallyRingedSpace.IsOpenImmersion (𝒰.cmap i) := 𝒰.isOpenImmersion i

/-- (Implementation) the transition maps in the glue data associated with an open cover: the
locally-ringed-space analogue of `AlgebraicGeometry.Scheme.OpenCover.gluedCoverT'`. The definition
uses only the generic pullback API, so it ports verbatim. -/
def gluedCoverT' (x y z : 𝒰.J) :
    pullback (pullback.fst (𝒰.cmap x) (𝒰.cmap y)) (pullback.fst (𝒰.cmap x) (𝒰.cmap z)) ⟶
      pullback (pullback.fst (𝒰.cmap y) (𝒰.cmap z)) (pullback.fst (𝒰.cmap y) (𝒰.cmap x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta gluedCoverT'; simp

theorem glued_cover_cocycle_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

theorem glued_cover_cocycle_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

theorem glued_cover_cocycle (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd

/-- The **glue data of locally ringed spaces** associated to an open cover of a formal scheme: the
pieces are the cover objects, the overlaps are the pullbacks `𝒰.obj i ×_X 𝒰.obj j`. Mirrors
`AlgebraicGeometry.Scheme.OpenCover.gluedCover`. -/
def gluedCoverLRS : LocallyRingedSpace.GlueData.{u} where
  J := 𝒰.J
  U i := (𝒰.obj i).toLocallyRingedSpace
  V p := pullback (𝒰.cmap p.1) (𝒰.cmap p.2)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := 𝒰.gluedCoverT' x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  cocycle x y z := 𝒰.glued_cover_cocycle x y z
  f_open _ _ := inferInstance

/-- The **glue data of formal schemes** associated to an open cover. -/
def gluedCover : FormalScheme.GlueData.{u} where
  toLocallyRingedSpaceGlueData := 𝒰.gluedCoverLRS
  isFormalScheme i := ⟨𝒰.obj i, ⟨Iso.refl _⟩⟩

/-- The `i`-th inclusion of the glued cover, an open immersion. -/
abbrev glueι (i : 𝒰.J) :
    (𝒰.obj i).toLocallyRingedSpace ⟶ 𝒰.gluedCover.gluedFormalScheme.toLocallyRingedSpace :=
  𝒰.gluedCover.ι i

/-- The **canonical morphism** from the glued cover into `X`, glued from the cover maps. It is an
isomorphism (see the `IsIso` instance below). Mirrors `AlgebraicGeometry.Scheme.OpenCover.fromGlued`.
-/
def fromGlued :
    𝒰.gluedCover.gluedFormalScheme.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  𝒰.gluedCover.glueMorphisms (fun i => 𝒰.cmap i) fun i j => by
    simpa using pullback.condition (f := 𝒰.cmap i) (g := 𝒰.cmap j)

@[reassoc (attr := simp)]
theorem ι_fromGlued (i : 𝒰.J) : 𝒰.glueι i ≫ 𝒰.fromGlued = 𝒰.cmap i :=
  𝒰.gluedCover.ι_glueMorphisms _ _ i

/-- The stalk map of `fromGlued` is an isomorphism at every point: locally `fromGlued` restricts
to the open immersion `cmap i` along the open immersion `glueι i`. -/
instance isIso_fromGlued_stalkMap
    (x : 𝒰.gluedCover.gluedFormalScheme.toLocallyRingedSpace) :
    IsIso (𝒰.fromGlued.stalkMap x) := by
  obtain ⟨i, y, rfl⟩ := 𝒰.gluedCoverLRS.ι_jointly_surjective x
  have h := LocallyRingedSpace.stalkMap_congr_hom _ _ (𝒰.ι_fromGlued i) y
  rw [LocallyRingedSpace.stalkMap_comp, ← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

/-- `fromGlued` is surjective on base points: every point of `X` is covered. -/
theorem fromGlued_base_surjective : Function.Surjective 𝒰.fromGlued.base := by
  intro x
  obtain ⟨i, y, hy⟩ := 𝒰.exists_preimage x
  refine ⟨(𝒰.glueι i).base y, ?_⟩
  have hι := ConcreteCategory.congr_hom
    (congrArg (fun φ : (𝒰.obj i).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace => φ.base)
      (𝒰.ι_fromGlued i)) y
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hι ⊢
  rw [hι]
  exact hy

/-- `fromGlued` is injective on base points. Mirrors `Scheme.OpenCover.fromGlued_injective`. -/
theorem fromGlued_base_injective : Function.Injective 𝒰.fromGlued.base := by
  sorry

/-- `fromGlued` is an open map on base points. Mirrors `Scheme.OpenCover.isOpenMap_fromGlued`. -/
theorem fromGlued_base_isOpenMap : IsOpenMap 𝒰.fromGlued.base := by
  sorry

theorem fromGlued_base_isOpenEmbedding : IsOpenEmbedding ⇑𝒰.fromGlued.base :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (by fun_prop)
    𝒰.fromGlued_base_injective 𝒰.fromGlued_base_isOpenMap

instance isOpenImmersion_fromGlued : LocallyRingedSpace.IsOpenImmersion 𝒰.fromGlued :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso (H := fun x => inferInstance)
    𝒰.fromGlued.toShHom 𝒰.fromGlued_base_isOpenEmbedding

instance : Epi 𝒰.fromGlued.toShHom.hom.base := by
  rw [TopCat.epi_iff_surjective]
  exact 𝒰.fromGlued_base_surjective

instance isIso_fromGlued : IsIso 𝒰.fromGlued := by
  haveI : IsIso 𝒰.fromGlued.toShHom := SheafedSpace.IsOpenImmersion.to_iso 𝒰.fromGlued.toShHom
  exact isIso_of_reflects_iso 𝒰.fromGlued LocallyRingedSpace.forgetToSheafedSpace

/-- **Gluing a family of morphisms out of an open cover.** Given a family `k i : 𝒰.obj i ⟶ Y`
of morphisms to a locally ringed space that agree on the pairwise overlaps
`𝒰.obj i ×_X 𝒰.obj j`, the induced morphism `X ⟶ Y`. -/
def glueMorphisms {Y : LocallyRingedSpace.{u}} (k : ∀ i, (𝒰.obj i).toLocallyRingedSpace ⟶ Y)
    (h : ∀ i j, pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i =
      pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j) :
    X.toLocallyRingedSpace ⟶ Y :=
  inv 𝒰.fromGlued ≫ 𝒰.gluedCover.glueMorphisms k fun i j => by
    have := h i j
    simpa using this

@[reassoc (attr := simp)]
theorem map_glueMorphisms {Y : LocallyRingedSpace.{u}} (k : ∀ i, (𝒰.obj i).toLocallyRingedSpace ⟶ Y)
    (h : ∀ i j, pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i =
      pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j) (i : 𝒰.J) :
    𝒰.cmap i ≫ 𝒰.glueMorphisms k h = k i := by
  rw [glueMorphisms, ← 𝒰.ι_fromGlued i, Category.assoc, IsIso.hom_inv_id_assoc,
    𝒰.gluedCover.ι_glueMorphisms]

end AlgebraicGeometry.FormalScheme.OpenCover

end
