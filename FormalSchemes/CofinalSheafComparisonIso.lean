import FormalSchemes.CofinalSheafComparison
import FormalSchemes.SpfGammaSheafComponent
import FormalSchemes.SpfGammaRoundTrip

set_option linter.style.header false

/-!
# The formal spectra of two ideals of definition are isomorphic (EGA I, §10.3, goal 1)

For an adic ring `R` with two ideals of definition `I J : Ideal R` (both `IsAdicRing`, hence both
inducing the same topology) with `I ≤ J`, this file assembles the already-merged ring-level pieces
into the full **isomorphism of locally ringed spaces** `Spf_J R ≅ Spf_I R` (equivalently
`Spf_I R ≅ Spf_J R`), completing goal 1 of the structure-sheaf intertwining in the nested case.

The route reuses the `Spf`-functoriality morphism `FormalSpectrum.locallyRingedSpaceMap` of the
identity ring homomorphism `RingHom.id R` (a continuous map of pairs `(R, I) → (R, J)` since
`I ≤ J`) and shows it is an isomorphism:

* its base map `mapTop` is the homeomorphism `IsAdic.homeomorphFormalSpectrum`
  (`FormalSpectrum.isIso_mapTopId`, `CofinalSheafComparison.lean`);
* its sheaf component `mapSheafHom` is an isomorphism, checked on the basis of basic opens: on
  `D(g)`, conjugated by `sectionsBasicOpenEquiv`, the component is the completed localization of the
  identity (`modelSheafComponent_eq_mapCompletion`), which is the cofinal comparison isomorphism
  `AdicCompletion.cofinalRingEquiv` — a ring isomorphism, since `I · R_g` and `J · R_g` are cofinal.

The key new algebraic input is that the completion map `AdicCompletion.mapCompletion` of a ring
homomorphism acting as the identity coincides with the cofinal comparison
`AdicCompletion.cofinalHom` (`AdicCompletion.mapCompletion_eq_cofinalHom`); this bridges the
*same-exponent* level maps produced by `mapSheafHom` with the *reindexed* level maps of
`cofinalHom`. The sheaf iso follows from `TopCat.Sheaf.isIso_iff_isIso_basis`, and the
locally-ringed-space iso from
`PresheafedSpace.isIso_of_components` reflected back along the forgetful functors.

## Main definitions and results

* `AdicCompletion.mapCompletion_eq_cofinalHom`: `mapCompletion` of an identity-acting ring hom is
  `cofinalHom`.
* `FormalSpectrum.isIso_mapSheafHomId`: the sheaf component of the identity comparison is an iso.
* `FormalSpectrum.cofinalStructureSheafIso`: `O_{Spf_I R} ≅ (mapTop)_* O_{Spf_J R}`.
* `FormalSpectrum.isIso_locallyRingedSpaceMapId`: the comparison is an iso of locally ringed spaces.
* `FormalSpectrum.cofinalSpfIso`: the isomorphism `Spf_I R ≅ Spf_J R` of locally ringed spaces.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AdicCompletion

variable {S : Type u} [CommRing S] {K L : Ideal S}

/-- **`mapCompletion` of an identity-acting ring homomorphism is `cofinalHom`.** If `φ : S →+* S`
acts as the identity on elements (`∀ s, φ s = s`) and `K ^ b ≤ L`, then the completion map
`mapCompletion φ hf hL : AdicCompletion K S →+* AdicCompletion L S` coincides with the cofinal
comparison map `cofinalHom hb`. The continuity hypothesis `hf : K.map φ ≤ L` forces `K ≤ L` (since
`φ` acts as the identity), and the two maps agree on the completion by the tower compatibility
`factorPow_evalₐ`, even though their level maps live at different exponents. -/
theorem mapCompletion_eq_cofinalHom {b : ℕ} (φ : S →+* S) (hφ : ∀ s, φ s = s)
    (hf : K.map φ ≤ L) (hL : L.FG) (hK : K.FG) (hb : K ^ b ≤ L) :
    mapCompletion φ hf hL = cofinalHom hb := by
  have hφid : φ = RingHom.id S := RingHom.ext hφ
  have hmap : K.map φ = K := by rw [hφid, Ideal.map_id]
  have hKL : K ≤ L := hmap ▸ hf
  refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
  have hKLn : K ^ n ≤ L ^ n := Ideal.pow_right_mono hKL n
  have hc : K ^ n ≤ (L ^ n).comap φ := fun s hs => by
    rw [Ideal.mem_comap, hφ]; exact hKLn hs
  rw [evalₐ_mapCompletion φ hf hL hK n hc x, evalₐ_cofinalHom, cofinalLevel_apply]
  -- `quotientMap (L ^ n) φ hc` is the same-exponent factor map (since `φ` acts as identity)
  have hqm : Ideal.quotientMap (L ^ n) φ hc = Ideal.Quotient.factor hKLn := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun s => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.quotientMap_mk,
      Ideal.Quotient.factor_mk, hφ]
  rw [hqm]
  -- exponent bridge: `evalₐ K n x = factorPow (n ≤ (b + 1) * n) (evalₐ K ((b + 1) * n) x)`
  have hle : n ≤ (b + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos b)
  rw [← factorPow_evalₐ K hle x,
    show (Ideal.Quotient.factorPow K hle) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) from rfl,
    Ideal.Quotient.factor_comp_apply]

end AdicCompletion

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
  [IsAdicRing I] [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing J] in
/-- **The identity comparison's sheaf component on `D(g)` is the cofinal comparison map.** For
`I ≤ J`, the model morphism `Spf_J R ⟶ Spf_I R` of the identity ring homomorphism has, on the basic
open `D(g)` and conjugated by `sectionsBasicOpenEquiv`, the component
`AdicCompletion.cofinalHom` between the two cofinal completions `I · R_g`, `J · R_g` of `R_g`. This
combines `modelSheafComponent_eq_mapCompletion` (the component is `mapCompletion` of the localized
identity) with `AdicCompletion.mapCompletion_eq_cofinalHom`. -/
theorem modelSheafComponentId_eq_cofinalHom (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) (g : R) :
    modelSheafComponent I J (RingHom.id R) (le_comap_id_of_le I J hIJ) g =
      AdicCompletion.cofinalHom (b := 1)
        (show (I.map (algebraMap R (Localization.Away g))) ^ 1 ≤
              J.map (algebraMap R (Localization.Away g)) by
          rw [pow_one]; exact Ideal.map_mono hIJ) := by
  rw [modelSheafComponent_eq_mapCompletion I J (RingHom.id R) (le_comap_id_of_le I J hIJ) g hI hJ]
  refine AdicCompletion.mapCompletion_eq_cofinalHom
    (Localization.awayMap (RingHom.id R) g) ?_ _ _ (hI.map _) _
  intro s
  exact IsLocalization.map_id s

/-- **The identity comparison's sheaf component on `D(g)` is an isomorphism.** Conjugated by the two
`sectionsBasicOpenEquiv` isomorphisms (and the structure-sheaf `eqToHom` restriction), the component
is the ring isomorphism `AdicCompletion.cofinalRingEquiv` (via `modelSheafComponentId_eq_cofinalHom`
and the cofinality of `I · R_g`, `J · R_g`), hence is bijective. -/
theorem isIso_mapSheafHomId_app_basicOpen (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) (g : R) :
    IsIso ((mapSheafHom I J (RingHom.id R) (le_comap_id_of_le I J hIJ)).hom.app
      (op (basicOpen I g))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hbij : Function.Bijective
      (modelSheafComponent I J (RingHom.id R) (le_comap_id_of_le I J hIJ) g) := by
    rw [modelSheafComponentId_eq_cofinalHom I J hIJ hI hJ g]
    obtain ⟨a, ha0⟩ :=
      IsAdic.exists_pow_le (IsAdicRing.isAdic (I := I)) (IsAdicRing.isAdic (I := J))
    have ha : (J.map (algebraMap R (Localization.Away g))) ^ a ≤
        I.map (algebraMap R (Localization.Away g)) := by
      rw [← Ideal.map_pow]; exact Ideal.map_mono ha0
    have hb1 : (I.map (algebraMap R (Localization.Away g))) ^ 1 ≤
        J.map (algebraMap R (Localization.Away g)) := by
      rw [pow_one]; exact Ideal.map_mono hIJ
    have hbe := (AdicCompletion.cofinalRingEquiv hb1 ha).bijective
    rwa [show (⇑(AdicCompletion.cofinalRingEquiv hb1 ha)) = ⇑(AdicCompletion.cofinalHom hb1) from
      funext (AdicCompletion.cofinalRingEquiv_apply hb1 ha)] at hbe
  rw [modelSheafComponent] at hbij
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hbij
  have hA := (sectionsBasicOpenEquiv J (RingHom.id R g)).bijective
  have hB : Function.Bijective ⇑(CommRingCat.Hom.hom
      ((structureSheaf J).presheaf.map
        (eqToHom (congrArg op (map_preimage_basicOpen I J (RingHom.id R)
          (le_comap_id_of_le I J hIJ) g))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hD := (sectionsBasicOpenEquiv I g).symm.bijective
  have h1 := (hA.of_comp_iff' _).mp hbij
  have h2 := (hB.of_comp_iff' _).mp h1
  exact (hD.of_comp_iff _).mp h2

/-- **The sheaf component of the identity comparison is an isomorphism.** Since it is an isomorphism
on the basis of basic opens (`isIso_mapSheafHomId_app_basicOpen`), it is an isomorphism of sheaves
by `TopCat.Sheaf.isIso_iff_isIso_basis`. -/
theorem isIso_mapSheafHomId (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) :
    IsIso (mapSheafHom I J (RingHom.id R) (le_comap_id_of_le I J hIJ)) :=
  TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_basicOpen I)
    (fun g => isIso_mapSheafHomId_app_basicOpen I J hIJ hI hJ g)

/-- **The two structure sheaves agree** (EGA I, 10.3): for two ideals of definition `I ≤ J`, the
structure sheaf `O_{Spf_I R}` is isomorphic, over the base homeomorphism `mapTop`, to the
pushforward of `O_{Spf_J R}`. This is the sheaf-level statement that `Spf R` is independent of the
of definition. -/
def cofinalStructureSheafIso (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) :
    structureSheaf I ≅
      (TopCat.Sheaf.pushforward CommRingCat
        (mapTop I J (RingHom.id R) (le_comap_id_of_le I J hIJ))).obj (structureSheaf J) :=
  haveI := isIso_mapSheafHomId I J hIJ hI hJ
  asIso (mapSheafHom I J (RingHom.id R) (le_comap_id_of_le I J hIJ))

/-- **The comparison morphism of locally ringed spaces is an isomorphism.** For two ideals of
definition `I ≤ J`, the `Spf`-functoriality morphism `Spf_J R ⟶ Spf_I R` of the identity ring
homomorphism is an isomorphism: its base map is a homeomorphism (`isIso_mapTopId`) and its sheaf
component is an isomorphism (`isIso_mapSheafHomId`). -/
theorem isIso_locallyRingedSpaceMapId (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) :
    IsIso (locallyRingedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ)) := by
  haveI hbase : IsIso (mapTop I J (RingHom.id R) (le_comap_id_of_le I J hIJ)) :=
    isIso_mapTopId I J hIJ
  haveI hsheaf : IsIso (mapSheafHom I J (RingHom.id R) (le_comap_id_of_le I J hIJ)) :=
    isIso_mapSheafHomId I J hIJ hI hJ
  haveI hc : IsIso ((mapSheafHom I J (RingHom.id R) (le_comap_id_of_le I J hIJ)).hom) :=
    inferInstanceAs (IsIso ((TopCat.Sheaf.forget CommRingCat _).map
      (mapSheafHom I J (RingHom.id R) (le_comap_id_of_le I J hIJ))))
  haveI hpsb : IsIso (presheafedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ)).base :=
    hbase
  haveI hpsc : IsIso (presheafedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ)).c :=
    hc
  haveI hps : IsIso (presheafedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ)) :=
    PresheafedSpace.isIso_of_components _
  haveI hps' : IsIso (SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map
        (locallyRingedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ)))) := hps
  haveI hsh : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map
      (locallyRingedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ))) :=
    isIso_of_reflects_iso _ SheafedSpace.forgetToPresheafedSpace
  exact isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace

/-- **The formal spectra of two ideals of definition are isomorphic** (EGA I, 10.3, goal 1). For an
adic ring `R` with two ideals of definition `I ≤ J`, the affine formal schemes `Spf_I R` and
`Spf_J R` are isomorphic as locally ringed spaces: `Spf R` depends only on the topological ring `R`,
not on the chosen ideal of definition. -/
def cofinalSpfIso (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) :
    locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J :=
  haveI := isIso_locallyRingedSpaceMapId I J hIJ hI hJ
  (asIso (locallyRingedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ))).symm

end FormalSpectrum

end
