import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# Open covers of formal schemes

Just as for schemes, a formal scheme is by definition locally an affine formal spectrum, so it
is covered by open immersions from affine formal schemes. This file packages that data into a
`FormalScheme.OpenCover` structure, mirroring the classic `AlgebraicGeometry.Scheme.OpenCover`
design, and produces the canonical affine cover of an arbitrary formal scheme from
`FormalScheme.exists_openImmersion`.

## Main definitions

* `FormalScheme.OpenCover X`: a family of open immersions `map j : obj j ⟶ X` from formal
  schemes `obj j`, together with, for each point `x`, an index `f x` whose piece covers `x`.
* `FormalScheme.AffineChart X x`: the bundled choice of an affine formal spectrum open immersion
  around a point `x`, extracted from `FormalScheme.exists_openImmersion`.
* `FormalScheme.affineCover X`: the canonical open cover of `X` by affine formal schemes,
  indexed by the points of `X`.
* `FormalScheme.GlueData.openCover`: the canonical cover of a glued formal scheme by its pieces.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
* [The Stacks Project, Tag 0AIL](https://stacks.math.columbia.edu/tag/0AIL)
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.FormalScheme

/-- An **open cover** of a formal scheme `X` is a family of open immersions `map j : obj j ⟶ X`
from formal schemes, such that every point of `X` lies in the range of one of them. This mirrors
the classic `AlgebraicGeometry.Scheme.OpenCover`. -/
structure OpenCover (X : FormalScheme.{u}) where
  /-- The index type of the cover. -/
  J : Type u
  /-- The formal scheme covering the `j`-th piece. -/
  obj : J → FormalScheme.{u}
  /-- The open immersion of the `j`-th piece into `X`. -/
  map : (j : J) → obj j ⟶ X
  /-- For each point `x`, an index whose piece covers `x`. -/
  f : X → J
  /-- The piece `f x` really does cover `x`. -/
  covers : ∀ x, x ∈ Set.range (map (f x)).toLRSHom.base
  /-- Every component map is an open immersion of locally ringed spaces. -/
  isOpenImmersion : ∀ j, LocallyRingedSpace.IsOpenImmersion (map j).toLRSHom := by infer_instance

attribute [instance] OpenCover.isOpenImmersion

namespace OpenCover

variable {X : FormalScheme.{u}} (𝒰 : OpenCover X)

/-- The chosen index covering a point, `𝒰.idx x := 𝒰.f x`. -/
abbrev idx (x : X) : 𝒰.J := 𝒰.f x

/-- The ranges of the component maps of an open cover exhaust the space. -/
theorem iUnion_range : ⋃ j, Set.range (𝒰.map j).toLRSHom.base = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  exact Set.mem_iUnion.mpr ⟨𝒰.f x, 𝒰.covers x⟩

end OpenCover

/-- A **choice of affine chart** around a point `x` of a formal scheme `X`: an adic ring `(R, I)`
together with an open immersion `Spf I ↪ X` whose range contains `x`. This bundles the data
provided existentially by `FormalScheme.exists_openImmersion`. -/
structure AffineChart (X : FormalScheme.{u}) (x : X) where
  /-- The underlying ring of the affine model. -/
  R : Type u
  /-- Its commutative ring structure. -/
  [commRing : CommRing R]
  /-- Its topology. -/
  [topR : TopologicalSpace R]
  /-- The ideal of definition. -/
  I : Ideal R
  /-- `(R, I)` is an adic ring, so `Spf I` is an affine formal scheme. -/
  [adic : IsAdicRing I]
  /-- The open immersion `Spf I ↪ X`. -/
  map : FormalSpectrum.locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace
  /-- Its range contains `x`. -/
  mem : x ∈ Set.range map.base
  /-- It is an open immersion. -/
  [isOpenImmersion : LocallyRingedSpace.IsOpenImmersion map]

attribute [instance] AffineChart.commRing AffineChart.topR AffineChart.adic
  AffineChart.isOpenImmersion

/-- Every point of a formal scheme admits an affine chart (from
`FormalScheme.exists_openImmersion`). -/
theorem nonempty_affineChart (X : FormalScheme.{u}) (x : X) : Nonempty (AffineChart X x) := by
  obtain ⟨R, _, _, I, _, f, hmem, hf⟩ := X.exists_openImmersion x
  exact ⟨{ R := R, I := I, map := f, mem := hmem }⟩

/-- A chosen affine chart around a point, via `Classical.choice`. -/
def AffineChart.choice (X : FormalScheme.{u}) (x : X) : AffineChart X x :=
  (nonempty_affineChart X x).some

/-- The **canonical affine open cover** of a formal scheme `X`, indexed by its points: around each
point `x` we take the affine chart `AffineChart.choice X x`, whose piece is the affine formal
scheme `Spf` of the chosen adic ring. -/
def affineCover (X : FormalScheme.{u}) : OpenCover X where
  J := X
  obj x := FormalScheme.Spf (AffineChart.choice X x).I
  map x := Hom.mk (AffineChart.choice X x).map
  f x := x
  covers x := (AffineChart.choice X x).mem
  isOpenImmersion x := (AffineChart.choice X x).isOpenImmersion

instance (X : FormalScheme.{u}) : Nonempty (OpenCover X) := ⟨affineCover X⟩

namespace GlueData

variable (D : GlueData.{u})

/-- The **canonical open cover** of a glued formal scheme by its pieces: the `i`-th piece is the
formal scheme `Y` isomorphic to `D.U i`, mapped in via that isomorphism composed with the open
immersion `ι i`. -/
def openCover : OpenCover D.gluedFormalScheme where
  J := D.toLocallyRingedSpaceGlueData.J
  obj i := (D.isFormalScheme i).choose
  map i := Hom.mk ((D.isFormalScheme i).choose_spec.some.hom ≫ D.ι i)
  f x := (D.ι_jointly_surjective x).choose
  covers x := by
    obtain ⟨y, hy⟩ := (D.ι_jointly_surjective x).choose_spec
    refine ⟨(D.isFormalScheme _).choose_spec.some.inv.base y, ?_⟩
    have hcancel : (D.isFormalScheme _).choose_spec.some.hom.base
        ((D.isFormalScheme _).choose_spec.some.inv.base y) = y := by simp
    simp only [Hom.toLRSHom, LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Function.comp_apply]
    rw [hcancel]
    exact hy
  isOpenImmersion i :=
    have : LocallyRingedSpace.IsOpenImmersion
        (D.isFormalScheme i).choose_spec.some.hom := inferInstance
    LocallyRingedSpace.IsOpenImmersion.comp _ _

end GlueData

end AlgebraicGeometry.FormalScheme
