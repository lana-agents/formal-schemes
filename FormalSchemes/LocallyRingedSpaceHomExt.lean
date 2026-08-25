import Mathlib.Geometry.RingedSpace.OpenImmersion

set_option linter.style.header false

/-!
# Morphisms of locally ringed spaces are determined on an open cover of the source

A family of open immersions `m i : P i ⟶ Z` of locally ringed spaces whose images exhaust `Z` is
**jointly epimorphic**: two morphisms out of `Z` agreeing after precomposition with every `m i`
are equal (`LocallyRingedSpace.hom_ext_of_jointly_surjective`). The form actually used downstream
takes the cover as a family of *opens* of `Z` with `⨆ i, V i = ⊤`
(`LocallyRingedSpace.hom_ext_of_iSup_eq_top`).

## Why this file exists, and why it is this low

`FormalSchemes/OpenCoverHomExt.lean` proves the same statement for a
`FormalScheme.OpenCover`, and `FormalSchemes/ThickeningHomExt.lean` proves the analogous
joint-epi statement for the thickenings of `Spf R`. Neither applies to a source that is merely a
locally ringed space — and that is the case the colimit property of `Spf` needs, where the source
is one thickening `Spec (R ⧸ Iⁿ⁺¹)` covered by the charts of the basic opens `D(r)`.

Nothing in the statements below mentions a ring, an ideal, a spectrum or a formal scheme, so the
module sits directly on Mathlib and is in the import closure of everything that could want it.
`OpenCoverHomExt.lean`'s `OpenCover.hom_ext` is this lemma at a `FormalScheme.OpenCover` and could
be rerouted through it; that is a relocation row, not this one, and is deliberately not done here
because it would edit a landed module with consumers.

## Route

Equality of morphisms of locally ringed spaces is detected on base points and on stalks
(`SheafedSpace.hom_stalk_ext`). The base maps agree because the images of the `m i` exhaust `Z`;
the stalk maps agree after cancelling the stalk map of the covering open immersion, which is an
isomorphism (`LocallyRingedSpace.IsOpenImmersion.stalk_iso`). This is the argument
`OpenCoverHomExt.lean` gives for a formal-scheme cover, with the cover structure removed.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_jointly_surjective`
* `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_iSup_eq_top`

## References

* Mathlib `AlgebraicGeometry.Scheme.Cover.hom_ext`, `SheafedSpace.hom_stalk_ext`.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **A jointly surjective family of open immersions is jointly epimorphic.** Two morphisms
`g₁ g₂ : Z ⟶ Y` of locally ringed spaces that agree after precomposition with every member of a
family of open immersions covering `Z` are equal. -/
theorem hom_ext_of_jointly_surjective {ι : Type v} {Z Y : LocallyRingedSpace.{u}}
    {P : ι → LocallyRingedSpace.{u}} (m : ∀ i, P i ⟶ Z)
    [∀ i, IsOpenImmersion (m i)]
    (hsurj : ∀ z : Z.toTopCat, ∃ (i : ι) (y : (P i).toTopCat), (m i).base y = z)
    {g₁ g₂ : Z ⟶ Y} (h : ∀ i, m i ≫ g₁ = m i ≫ g₂) :
    g₁ = g₂ := by
  -- The base maps agree, pointwise, because the family exhausts `Z`.
  have hbase_pt : ∀ z : Z.toTopCat, g₁.base z = g₂.base z := by
    intro z
    obtain ⟨i, y, rfl⟩ := hsurj z
    have hi := congrArg (fun φ : P i ⟶ Y => φ.base y) (h i)
    simpa only [LocallyRingedSpace.comp_base, TopCat.comp_app] using hi
  have hbase : g₁.base = g₂.base := by
    apply ConcreteCategory.hom_ext
    exact hbase_pt
  -- Reduce to `SheafedSpace.hom_stalk_ext`.
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  refine SheafedSpace.hom_stalk_ext _ _ hbase (fun z => ?_)
  obtain ⟨i, y, rfl⟩ := hsurj z
  -- The goal is stated with `PresheafedSpace` stalk maps of `forgetToSheafedSpace.map gᵢ`, which
  -- are definitionally the `LocallyRingedSpace` stalk maps of `gᵢ`; prove the equality in
  -- `LocallyRingedSpace` terms and transport it across the defeq with `exact`.
  have key : g₁.stalkMap ((m i).base y) =
      (Y.presheaf.stalkCongr (hbase ▸ rfl)).hom ≫ g₂.stalkMap ((m i).base y) := by
    rw [← cancel_mono ((m i).stalkMap y), Category.assoc,
      ← LocallyRingedSpace.stalkMap_comp, ← LocallyRingedSpace.stalkMap_comp,
      LocallyRingedSpace.stalkMap_congr_hom _ _ (h i) y, TopCat.Presheaf.stalkCongr_hom]
    -- The two `stalkSpecializes` factors record the same specialization, so agree by proof
    -- irrelevance.
    rfl
  exact key

/-- **A morphism of locally ringed spaces is determined by its restrictions to an open cover of
its source.** The form the colimit property of `Spf` consumes: the cover is given as a family of
opens with `⨆ i, V i = ⊤`, and the restriction maps are the canonical `Z|_{V i} ⟶ Z`. -/
theorem hom_ext_of_iSup_eq_top {ι : Type v} {Z Y : LocallyRingedSpace.{u}}
    (V : ι → Opens Z.toTopCat) (hV : ⨆ i, V i = ⊤) {g₁ g₂ : Z ⟶ Y}
    (h : ∀ i, Z.ofRestrict (V i).isOpenEmbedding ≫ g₁ =
      Z.ofRestrict (V i).isOpenEmbedding ≫ g₂) :
    g₁ = g₂ :=
  hom_ext_of_jointly_surjective (fun i => Z.ofRestrict (V i).isOpenEmbedding)
    (fun z => by
      have hz : z ∈ ⨆ i, V i := by rw [hV]; trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
      exact ⟨i, ⟨z, hi⟩, rfl⟩)
    h

end AlgebraicGeometry.LocallyRingedSpace

end
