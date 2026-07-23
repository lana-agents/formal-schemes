import FormalSchemes.BasicOpenImmersionAssembly
import Mathlib.Geometry.RingedSpace.OpenImmersion

set_option linter.style.header false

/-!
# The affine basic-open chart is a `LocallyRingedSpace` open immersion (issue 163)

For an adic ring `(R, I)` with `I.FG` and `f : R`, this file upgrades the affine basic-open chart
`FormalSpectrum.basicOpenChart I f : Spf R{1/f} ⟶ Spf R` to a genuine
`LocallyRingedSpace.IsOpenImmersion` — the formal-geometry analogue of
`AlgebraicGeometry.basicOpenIsoSpecAway` (`Spec R_f ≅ D(f) ⊆ Spec R`).

The base map is already known to be an open embedding onto `D(f)`
(`isOpenEmbedding_basicOpenChartBase`/`range_basicOpenChartBase`), and the merged development
supplies the `c_iso`-on-basic-opens fact (`bijective_chartComponent`, issue 163's algebraic core).
The remaining `PresheafedSpace.IsOpenImmersion.c_iso` field — that the sheaf `c`-component is an
isomorphism at *every* open in the image `D(f)` — is obtained as follows:

* `isIso_c_app_basicOpen`: the chart's `c`-component on a basic open `D(g) ⊆ D(f)` is an iso, since
  it is conjugate (by the two `sectionsBasicOpenEquiv` and a structure-sheaf restriction) to the
  bijective `chartComponent`.
* `pullbackStructureSheafHom` (`η`): the comparison morphism from the pullback of `O_{Spf R}` along
  the open embedding to `O_{Spf R{1/f}}`, on the source space.
* `isIso_pullbackStructureSheafHom`: `η` is an isomorphism, via `TopCat.Sheaf.isIso_iff_isIso_basis`
  on the basis of preimages of basic opens (`isBasis_preimage`), where each component reduces to
  `isIso_c_app_basicOpen` at `D(f * g)` (`functor_obj_preimage_basicOpen`).
* `isIso_c_app_functor_obj`: `η` being an iso gives that the `c`-component is an iso at every image
  open `mapTop '' U`, the `c_iso` field.

## Main results

* `FormalSpectrum.isOpenImmersion_basicOpenChart`: the chart is a
  `LocallyRingedSpace.IsOpenImmersion`.
* `FormalSpectrum.range_basicOpenChart_base`: its underlying-space range is `basicOpen I f = D(f)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- The chart's sheaf `c`-component on a basic open `D(g) ⊆ D(f)` is an isomorphism in
`CommRingCat`: it is bijective, being conjugate (by the two `sectionsBasicOpenEquiv` isomorphisms
and the structure-sheaf restriction) to the bijective `chartComponent`. -/
theorem isIso_c_app_basicOpen (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    IsIso ((basicOpenChart I f).c.app (op (basicOpen I g))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  -- `chartComponent I f g = A ∘ B ∘ (c.app …).hom ∘ D`, with `A`, `B`, `D` bijective isos.
  have hbij := bijective_chartComponent I f g hI hfg
  rw [chartComponent] at hbij
  -- peel the coercion of the composed ring hom into function composition
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hbij
  -- the three flanking maps are bijective
  have hA := (sectionsBasicOpenEquiv (awayCompletionIdeal I f) (awayCompletionHom I f g)).bijective
  have hD := (sectionsBasicOpenEquiv I g).symm.bijective
  have hB : Function.Bijective ⇑(CommRingCat.Hom.hom
      ((structureSheaf (awayCompletionIdeal I f)).presheaf.map
        (eqToHom (congrArg op (map_preimage_basicOpen I (awayCompletionIdeal I f)
          (awayCompletionHom I f) (le_comap_awayCompletionHom I f) g))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  -- strip `A`, then `B`, then `D` (term-mode: matches up to defeq, dodging the `.presheaf` keyed
  -- rewrite transparency failure)
  have h1 := (hA.of_comp_iff' _).mp hbij
  have h2 := (hB.of_comp_iff' _).mp h1
  -- `⇑(C.comp D)` is defeq `⇑C ∘ ⇑D`, so strip the bijective `D` on the right without a rewrite
  -- (the sheaf-component `C` blocks `rw`/`simp` from seeing through the composite)
  exact (hD.of_comp_iff _).mp h2

/-- The base map of the chart, as a `TopCat` morphism, is an open topological embedding. -/
theorem isOpenEmbedding_mapTop_basicOpen (hI : I.FG) :
    IsOpenEmbedding (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f)) :=
  isOpenEmbedding_basicOpenChartBase I f hI

/-- The range of the chart's base map, in `mapTop` form, is the basic open `D(f)`. -/
theorem range_mapTop_basicOpen (hI : I.FG) :
    Set.range (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f)) = (basicOpen I f : Set (FormalSpectrum I)) :=
  range_basicOpenChartBase I f hI

/-- The open-embedding functor sends the preimage of a basic open `D(g')` to the basic open
`D(f * g') = D(f) ⊓ D(g')` of the target: the image of `base⁻¹ D(g')` is `D(g') ∩ range base`, and
`range base = D(f)`. -/
theorem functor_obj_preimage_basicOpen (hI : I.FG) (g' : R) :
    (isOpenEmbedding_mapTop_basicOpen I f hI).functor.obj
        ((Opens.map (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
          (le_comap_awayCompletionHom I f))).obj (basicOpen I g')) = basicOpen I (f * g') := by
  apply Opens.ext
  rw [IsOpenMap.coe_functor_obj, Opens.map_coe, Set.image_preimage_eq_inter_range,
    range_mapTop_basicOpen I f hI, basicOpen_mul I f g', Opens.coe_inf, Set.inter_comm]

/-- The preimages of basic opens `D(g')` form a basis of the source `Spf R{1/f}`: the base map is
inducing, so it pulls the basic-open basis of the target back to a basis of the source. -/
theorem isBasis_preimage (hI : I.FG) :
    Opens.IsBasis (Set.range (fun g' : R =>
      (Opens.map (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f))).obj (basicOpen I g'))) := by
  have hbasis := IsTopologicalBasis.isInducing
    (isOpenEmbedding_mapTop_basicOpen I f hI).isInducing (isTopologicalBasis_basicOpen I)
  have hset : ((↑) : Opens (FormalSpectrum (awayCompletionIdeal I f)) →
        Set (FormalSpectrum (awayCompletionIdeal I f))) ''
      (Set.range (fun g' : R => (Opens.map (mapTop I (awayCompletionIdeal I f)
        (awayCompletionHom I f) (le_comap_awayCompletionHom I f))).obj (basicOpen I g'))) =
      (Set.preimage ⇑(mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f))) ''
        (Set.range fun g' : R => (↑(basicOpen I g') : Set (FormalSpectrum I))) := by
    rw [← Set.range_comp, ← Set.range_comp]
    rfl
  rw [Opens.IsBasis, hset]
  exact hbasis

theorem range_basicOpenChart_base (hI : I.FG) :
    Set.range (FormalSpectrum.basicOpenChart I f).base
      = (FormalSpectrum.basicOpen I f : Set (FormalSpectrum I)) :=
  range_basicOpenChartBase I f hI

/-- The open-embedding functor followed by the pullback along `mapTop` is the identity on opens of
the source: `mapTop⁻¹ (mapTop '' U) = U` because `mapTop` is injective. -/
theorem map_functor_obj (hI : I.FG)
    (U : Opens (FormalSpectrum (awayCompletionIdeal I f))) :
    (Opens.map (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f))).obj
        ((isOpenEmbedding_mapTop_basicOpen I f hI).functor.obj U) = U :=
  Opens.ext (Set.preimage_image_eq _ (isOpenEmbedding_mapTop_basicOpen I f hI).injective)

/-- The restriction of the target structure sheaf `O_{Spf R}` to the open `D(f)`, transported to the
source space `Spf R{1/f}` along the open embedding `mapTop`. Its underlying presheaf is
`(open-embedding functor)ᵒᵖ ⋙ O_{Spf R}`, i.e. `U ↦ O_{Spf R}(mapTop '' U)`. -/
def pullbackStructureSheaf (hI : I.FG) :
    TopCat.Sheaf CommRingCat (TopCat.of (FormalSpectrum (awayCompletionIdeal I f))) :=
  ((sheafedSpaceObj I).restrict (isOpenEmbedding_mapTop_basicOpen I f hI)).sheaf

/-- The comparison morphism `η : pullbackStructureSheaf ⟶ O_{Spf R{1/f}}` on the source: at an open
`U` it is the chart's `c`-component at `mapTop '' U` followed by the structure-sheaf reindexing
`O_{Spf R{1/f}}(mapTop⁻¹(mapTop '' U)) = O_{Spf R{1/f}}(U)`. -/
def pullbackStructureSheafHom (hI : I.FG) :
    pullbackStructureSheaf I f hI ⟶ structureSheaf (awayCompletionIdeal I f) :=
  ObjectProperty.homMk
    { app := fun U =>
        (mapSheafHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
            (le_comap_awayCompletionHom I f)).hom.app
          (op ((isOpenEmbedding_mapTop_basicOpen I f hI).functor.obj U.unop)) ≫
          (structureSheaf (awayCompletionIdeal I f)).presheaf.map
            (eqToHom (congrArg op (map_functor_obj I f hI U.unop)))
      naturality := fun U U' i => by
        have hnat := (mapSheafHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
            (le_comap_awayCompletionHom I f)).hom.naturality
          ((isOpenEmbedding_mapTop_basicOpen I f hI).functor.op.map i)
        simp only [Category.assoc]
        erw [reassoc_of% hnat]
        congr 1
        -- G-side: every factor is `O_{Spf R{1/f}}.map` of a morphism of opens (the pushforward map
        -- and the `.obj`/`.presheaf` codomain map are defeq to it), so the two composites collapse
        -- to `.map` of morphisms between the same opens, equal by thinness (`Subsingleton.elim`).
        exact (Functor.map_comp _ _ _).symm.trans
          ((congrArg (structureSheaf (awayCompletionIdeal I f)).presheaf.map
            (Subsingleton.elim _ _)).trans (Functor.map_comp _ _ _)) }

/-- The component of `η` at an open `U`: the chart's `c`-component at `mapTop '' U` followed by the
structure-sheaf reindexing. -/
theorem pullbackStructureSheafHom_hom_app (hI : I.FG)
    (U : Opens (FormalSpectrum (awayCompletionIdeal I f))) :
    (pullbackStructureSheafHom I f hI).hom.app (op U) =
      (mapSheafHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
          (le_comap_awayCompletionHom I f)).hom.app
          (op ((isOpenEmbedding_mapTop_basicOpen I f hI).functor.obj U)) ≫
        (structureSheaf (awayCompletionIdeal I f)).presheaf.map
          (eqToHom (congrArg op (map_functor_obj I f hI U))) :=
  rfl

/-- `η` is an isomorphism of sheaves: it is an isomorphism on the basis of preimages of basic opens
`D(g')` (there its component is the chart's `c`-component at `D(f * g')`, an isomorphism by
`isIso_c_app_basicOpen`, post-composed with a reindexing isomorphism), hence an isomorphism by
`TopCat.Sheaf.isIso_iff_isIso_basis`. -/
theorem isIso_pullbackStructureSheafHom (hI : I.FG) :
    IsIso (pullbackStructureSheafHom I f hI) := by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_preimage I f hI) (fun g' => ?_)
  haveI hc : IsIso ((mapSheafHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f)).hom.app
      (op ((isOpenEmbedding_mapTop_basicOpen I f hI).functor.obj
        ((Opens.map (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
          (le_comap_awayCompletionHom I f))).obj (basicOpen I g'))))) := by
    rw [functor_obj_preimage_basicOpen I f hI g']
    exact isIso_c_app_basicOpen I f (f * g') hI (isUnit_algebraMap_away_left f g')
  rw [pullbackStructureSheafHom_hom_app]
  haveI hb : IsIso ((structureSheaf (awayCompletionIdeal I f)).presheaf.map
      (eqToHom (congrArg op (map_functor_obj I f hI
        ((Opens.map (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
          (le_comap_awayCompletionHom I f))).obj (basicOpen I g')))))) := by
    rw [eqToHom_map]; infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hc hb

/-- The chart's `c`-component is an isomorphism at every open in the image of the open embedding
(i.e. at `mapTop '' U` for every source open `U`). This is the `c_iso` field of the open immersion:
it follows from `η` being an isomorphism (hence isomorphic on every component) after cancelling the
reindexing isomorphism. -/
theorem isIso_c_app_functor_obj (hI : I.FG)
    (U : Opens (FormalSpectrum (awayCompletionIdeal I f))) :
    IsIso ((mapSheafHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f)).hom.app
      (op ((isOpenEmbedding_mapTop_basicOpen I f hI).functor.obj U))) := by
  haveI hη := isIso_pullbackStructureSheafHom I f hI
  -- `Sheaf.forget` is fully faithful, so the underlying presheaf morphism `η.hom` is an iso, hence
  -- so is each of its components (`NatIso.isIso_app_of_isIso`).
  haveI hηhom : IsIso (pullbackStructureSheafHom I f hI).hom :=
    inferInstanceAs (IsIso ((TopCat.Sheaf.forget CommRingCat _).map
      (pullbackStructureSheafHom I f hI)))
  haveI hb : IsIso ((structureSheaf (awayCompletionIdeal I f)).presheaf.map
      (eqToHom (congrArg op (map_functor_obj I f hI U)))) := by rw [eqToHom_map]; infer_instance
  haveI happ : IsIso ((mapSheafHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f)).hom.app
        (op ((isOpenEmbedding_mapTop_basicOpen I f hI).functor.obj U)) ≫
      (structureSheaf (awayCompletionIdeal I f)).presheaf.map
        (eqToHom (congrArg op (map_functor_obj I f hI U)))) := by
    rw [← pullbackStructureSheafHom_hom_app I f hI U]
    exact NatIso.isIso_app_of_isIso _ _
  -- cancel the reindexing isomorphism `g` on the right of `f ≫ g` (`= η.hom.app`, an iso)
  exact (@isIso_comp_right_iff _ _ _ _ _ _ _ hb).mp happ

/-- **The affine basic-open chart is an open immersion of locally ringed spaces** (issue 163). For
an adic ring `(R, I)` with `I` finitely generated and `f : R`, the chart `Spf R{1/f} ⟶ Spf R` is a
`LocallyRingedSpace.IsOpenImmersion`: the base map is an open embedding onto `D(f)`
(`isOpenEmbedding_mapTop_basicOpen`), and the sheaf `c`-component is an isomorphism at every image
open (`isIso_c_app_functor_obj`). This is the formal-geometry analogue of
`AlgebraicGeometry.basicOpenIsoSpecAway` (`Spec R_f ≅ D(f) ⊆ Spec R`). -/
theorem isOpenImmersion_basicOpenChart (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f) :=
  ⟨isOpenEmbedding_mapTop_basicOpen I f hI, fun U => isIso_c_app_functor_obj I f hI U⟩

end FormalSpectrum
