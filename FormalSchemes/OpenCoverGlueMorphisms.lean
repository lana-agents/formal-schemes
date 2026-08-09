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

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

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
    change pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ 𝒰.cmap i =
      (pullbackSymmetry _ _).hom ≫ pullback.fst (𝒰.cmap j) (𝒰.cmap i) ≫ 𝒰.cmap j
    rw [pullbackSymmetry_hom_comp_fst_assoc]
    exact pullback.condition

@[reassoc (attr := simp)]
theorem ι_fromGlued (i : 𝒰.J) : 𝒰.glueι i ≫ 𝒰.fromGlued = 𝒰.cmap i :=
  𝒰.gluedCover.ι_glueMorphisms _ _ i

/-- The stalk map of `fromGlued` is an isomorphism at every point: locally `fromGlued` restricts
to the open immersion `cmap i` along the open immersion `glueι i`. -/
instance isIso_fromGlued_stalkMap
    (x : 𝒰.gluedCover.gluedFormalScheme.toLocallyRingedSpace) :
    IsIso (𝒰.fromGlued.stalkMap x) := by
  obtain ⟨i, y, rfl⟩ := 𝒰.gluedCoverLRS.ι_jointly_surjective x
  haveI hci : IsIso ((𝒰.cmap i).stalkMap y) :=
    inferInstanceAs (IsIso ((𝒰.map i).toLRSHom.toShHom.hom.stalkMap y))
  haveI hgi : IsIso ((𝒰.glueι i).stalkMap y) :=
    inferInstanceAs (IsIso ((𝒰.gluedCover.ι i).toShHom.hom.stalkMap y))
  haveI hcomp : IsIso ((𝒰.glueι i ≫ 𝒰.fromGlued).stalkMap y) := by
    rw [𝒰.ι_fromGlued i]; exact hci
  rw [LocallyRingedSpace.stalkMap_comp] at hcomp
  exact (CategoryTheory.isIso_comp_right_iff (𝒰.fromGlued.stalkMap _)
    ((𝒰.glueι i).stalkMap y)).mp hcomp

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

/-- (Helper) A point of the overlap `𝒰.obj i ×_X 𝒰.obj j` maps to equal points of the glued cover
along the two inclusions. This is the glue-relation direction of
`AlgebraicGeometry.Scheme.GlueData.ι_eq_iff` we need, obtained directly from the glue condition
`f i j ≫ ι i = t i j ≫ f j i ≫ ι j` of the underlying `CategoryTheory.GlueData`. -/
private theorem gluedCoverLRS_ι_base_eq_of (i j : 𝒰.J) (z : 𝒰.gluedCoverLRS.V (i, j)) :
    (𝒰.gluedCoverLRS.toGlueData.ι i).base ((𝒰.gluedCoverLRS.f i j).base z) =
      (𝒰.gluedCoverLRS.toGlueData.ι j).base
        ((𝒰.gluedCoverLRS.t i j ≫ 𝒰.gluedCoverLRS.f j i).base z) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun m : 𝒰.gluedCoverLRS.V (i, j) ⟶ 𝒰.gluedCoverLRS.toGlueData.glued => m.base)
      (𝒰.gluedCoverLRS.toGlueData.glue_condition i j)) z
  simpa only [LocallyRingedSpace.comp_base, TopCat.comp_app, ConcreteCategory.comp_apply]
    using h.symm

/-- (Helper) A set of the glued cover is open iff its preimage along every inclusion `ι i` is open.
The locally-ringed-space analogue of `AlgebraicGeometry.Scheme.GlueData.isOpen_iff`, obtained by
transporting `TopCat.GlueData.isOpen_iff` across the carrier homeomorphism `isoCarrier`. -/
private theorem gluedCoverLRS_isOpen_iff
    (U : Set 𝒰.gluedCoverLRS.toGlueData.glued.carrier) :
    IsOpen U ↔ ∀ i, IsOpen ((𝒰.gluedCoverLRS.toGlueData.ι i).base ⁻¹' U) := by
  rw [← (TopCat.homeoOfIso 𝒰.gluedCoverLRS.isoCarrier.symm).isOpen_preimage,
    TopCat.GlueData.isOpen_iff]
  refine forall_congr' fun i => ?_
  rw [← Set.preimage_comp, ← 𝒰.gluedCoverLRS.ι_isoCarrier_inv]
  rfl

/-- (Helper) `fromGlued.base` sends `ι i x` to `cmap i x`. -/
private theorem fromGlued_base_glueι (i : 𝒰.J) (z : 𝒰.gluedCoverLRS.U i) :
    𝒰.fromGlued.base ((𝒰.glueι i).base z) = (𝒰.cmap i).base z := by
  have hι := ConcreteCategory.congr_hom
    (congrArg (fun φ : (𝒰.obj i).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace => φ.base)
      (𝒰.ι_fromGlued i)) z
  simpa only [LocallyRingedSpace.comp_base, TopCat.comp_app] using hι

/-- `fromGlued` is injective on base points. Mirrors `Scheme.OpenCover.fromGlued_injective`. -/
theorem fromGlued_base_injective : Function.Injective 𝒰.fromGlued.base := by
  intro p q h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCoverLRS.ι_jointly_surjective p
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCoverLRS.ι_jointly_surjective q
  have h' : (𝒰.cmap i).base x = (𝒰.cmap j).base y := by
    rw [← 𝒰.fromGlued_base_glueι i x, ← 𝒰.fromGlued_base_glueι j y]
    exact h
  haveI : PreservesLimit (cospan (𝒰.cmap i) (𝒰.cmap j)) LocallyRingedSpace.forgetToTop :=
    inferInstanceAs (PreservesLimit (cospan (𝒰.cmap i) (𝒰.cmap j))
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))
  let e := (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
    (isLimitOfHasPullbackOfPreservesLimit LocallyRingedSpace.forgetToTop (𝒰.cmap i) (𝒰.cmap j))
  have hzx : (𝒰.gluedCoverLRS.f i j).base (e.hom ⟨⟨x, y⟩, h'⟩) = x := by
    erw [← ConcreteCategory.comp_apply,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
    rfl
  have hzy : (𝒰.gluedCoverLRS.t i j ≫ 𝒰.gluedCoverLRS.f j i).base (e.hom ⟨⟨x, y⟩, h'⟩) = y := by
    erw [← ConcreteCategory.comp_apply, pullbackSymmetry_hom_comp_fst,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl
  have key := 𝒰.gluedCoverLRS_ι_base_eq_of i j (e.hom ⟨⟨x, y⟩, h'⟩)
  rw [hzx, hzy] at key
  exact key

/-- `fromGlued` is an open map on base points. Mirrors `Scheme.OpenCover.isOpenMap_fromGlued`. -/
theorem fromGlued_base_isOpenMap : IsOpenMap 𝒰.fromGlued.base := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  replace hU := (𝒰.gluedCoverLRS_isOpen_iff U).mp hU
  refine ⟨𝒰.fromGlued.base '' U ∩ Set.range (𝒰.cmap (𝒰.idx x)).base,
    Set.inter_subset_left, ?_, hx, 𝒰.covers x⟩
  rw [← Set.image_preimage_eq_inter_range]
  apply (𝒰.isOpenImmersion (𝒰.idx x)).base_open.isOpenMap
  convert! hU (𝒰.idx x) using 1
  simp only [← 𝒰.ι_fromGlued, LocallyRingedSpace.comp_base, TopCat.hom_comp,
    ContinuousMap.coe_comp, Set.preimage_comp]
  congr! 1
  exact Set.preimage_image_eq _ 𝒰.fromGlued_base_injective

theorem fromGlued_base_isOpenEmbedding : IsOpenEmbedding ⇑𝒰.fromGlued.base :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (by fun_prop)
    𝒰.fromGlued_base_injective 𝒰.fromGlued_base_isOpenMap

instance isOpenImmersion_fromGlued : LocallyRingedSpace.IsOpenImmersion 𝒰.fromGlued :=
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso 𝒰.fromGlued 𝒰.fromGlued_base_isOpenEmbedding

instance epi_fromGlued_base : Epi 𝒰.fromGlued.base := by
  rw [TopCat.epi_iff_surjective]
  exact 𝒰.fromGlued_base_surjective

instance isIso_fromGlued : IsIso 𝒰.fromGlued :=
  LocallyRingedSpace.IsOpenImmersion.to_iso 𝒰.fromGlued

/-- **Gluing a family of morphisms out of an open cover.** Given a family `k i : 𝒰.obj i ⟶ Y`
of morphisms to a locally ringed space that agree on the pairwise overlaps
`𝒰.obj i ×_X 𝒰.obj j`, the induced morphism `X ⟶ Y`. -/
def glueMorphisms {Y : LocallyRingedSpace.{u}} (k : ∀ i, (𝒰.obj i).toLocallyRingedSpace ⟶ Y)
    (h : ∀ i j, pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i =
      pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j) :
    X.toLocallyRingedSpace ⟶ Y :=
  inv 𝒰.fromGlued ≫ 𝒰.gluedCover.glueMorphisms k fun i j => by
    change pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i =
      (pullbackSymmetry _ _).hom ≫ pullback.fst (𝒰.cmap j) (𝒰.cmap i) ≫ k j
    rw [pullbackSymmetry_hom_comp_fst_assoc]
    exact h i j

@[reassoc (attr := simp)]
theorem map_glueMorphisms {Y : LocallyRingedSpace.{u}} (k : ∀ i, (𝒰.obj i).toLocallyRingedSpace ⟶ Y)
    (h : ∀ i j, pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i =
      pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j) (i : 𝒰.J) :
    𝒰.cmap i ≫ 𝒰.glueMorphisms k h = k i := by
  rw [glueMorphisms, ← 𝒰.ι_fromGlued i, Category.assoc, IsIso.hom_inv_id_assoc]
  exact 𝒰.gluedCover.ι_glueMorphisms _ _ i

end AlgebraicGeometry.FormalScheme.OpenCover

end
