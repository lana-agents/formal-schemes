import FormalSchemes.Completion

set_option linter.style.header false

/-!
# The structure sheaf of a formal completion is the completion of the tower (EGA I, 10.8)

For a commutative ring `R` and a finitely generated ideal `I`, the formal completion of
`Spec R` along `V(I)` is `formalCompletion R I hI = Spf R^`, where `R^ = AdicCompletion I R`
(see `FormalSchemes/Completion.lean`). Its structure sheaf is
`structureSheaf (AdicCompletion.idealOfDefinition I)`, the inverse limit of the structure sheaves
of the thickenings `Spec (R^ ⧸ (I·R^) ^ (n + 1))` of the completion.

This file identifies that structure sheaf, over the base homeomorphism
`formalCompletion.homeo`, with the inverse limit `structureSheaf I` of the structure sheaves of
the thickenings `Spec (R ⧸ I ^ (n + 1))` of the **original** ring `R`. This is the statement that
makes `formalCompletion R I hI` a genuine *completion*: `O_{Spf R^} ≅ limₙ O_{Spec R} / I ^ n`
transported along the homeomorphism, rather than merely "`Spf` of the completed ring".

The comparison is `FormalSpectrum.mapSheafHom` for the structure map `algebraMap R R^`
(which needs no adic hypotheses on the source, only `[CommRing R]`): the induced morphism of
structure sheaves `structureSheaf I ⟶ (mapTop)_* structureSheaf (idealOfDefinition I)`. The key
input is that completion does not change the infinitesimal thickenings
(`AdicCompletion.quotientEquivPow`): the level-`n` map of thickenings is the inverse of that
isomorphism, so every level map is a ring isomorphism, hence the comparison is an isomorphism.

## Main definitions and results

* `AdicCompletion.le_comap_idealOfDefinition`: `I ≤ (I·R^).comap (algebraMap R R^)`, so the
  structure map `algebraMap R R^` is a continuous ring homomorphism `(R, I) → (R^, I·R^)`.
* `FormalSpectrum.completionLevelRingHom_eq`: the level-`n` map of thickenings induced by
  `algebraMap R R^` is `(quotientEquivPow I hI (n + 1)).symm` — a ring isomorphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The structure map `algebraMap R R^` carries `I` into the ideal of definition `I·R^` of the
completion; equivalently, `I ≤ (I·R^).comap (algebraMap R R^)`. This is the continuity
hypothesis making `algebraMap R R^` a morphism of pairs `(Spec R, V(I)) → (Spec R^, V(I·R^))`. -/
theorem le_comap_idealOfDefinition :
    I ≤ (idealOfDefinition I).comap (algebraMap R (AdicCompletion I R)) :=
  Ideal.le_comap_map

end AdicCompletion

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)

/-- **The level-`n` map of thickenings of the completion comparison is a ring isomorphism.**
The map of thickenings `R ⧸ I ^ (n + 1) →+* R^ ⧸ (I·R^) ^ (n + 1)` induced by the structure map
`algebraMap R R^` is exactly the inverse of `AdicCompletion.quotientEquivPow` — the statement that
completion does not change the infinitesimal thickenings (EGA I, 10.8). -/
theorem completionLevelRingHom_eq (n : ℕ) :
    levelRingHom I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n =
      ((AdicCompletion.quotientEquivPow I hI (n + 1)).symm : _ →+* _) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have hof : algebraMap R (AdicCompletion I R) r = AdicCompletion.of I R r := by
    rw [AdicCompletion.algebraMap_apply]; rfl
  have key : (AdicCompletion.quotientEquivPow I hI (n + 1))
      (Ideal.Quotient.mk ((AdicCompletion.idealOfDefinition I) ^ (n + 1))
        (algebraMap R (AdicCompletion I R) r)) =
      Ideal.Quotient.mk (I ^ (n + 1)) r := by
    rw [AdicCompletion.quotientEquivPow_mk, hof, AdicCompletion.evalₐ_of]
  simp only [RingHom.coe_comp, Function.comp_apply, levelRingHom_mk, RingHom.coe_coe]
  exact ((RingEquiv.symm_apply_eq _).mpr key.symm).symm

/-- The comparison morphism of structure sheaves for the formal completion of `Spec R` along
`V(I)`: the morphism `structureSheaf I ⟶ (mapTop)_* structureSheaf (I·R^)` induced by the
structure map `algebraMap R R^` via `FormalSpectrum.mapSheafHom` (which needs no adic hypotheses
on the source). Its base map `mapTop` is the homeomorphism `formalCompletion.homeo` in `TopCat`. -/
def completionCompareSheafHom :
    structureSheaf I ⟶
      (TopCat.Sheaf.pushforward CommRingCat
        (mapTop I (AdicCompletion.idealOfDefinition I) (algebraMap R (AdicCompletion I R))
          (AdicCompletion.le_comap_idealOfDefinition I))).obj
        (structureSheaf (AdicCompletion.idealOfDefinition I)) :=
  mapSheafHom I (AdicCompletion.idealOfDefinition I) (algebraMap R (AdicCompletion I R))
    (AdicCompletion.le_comap_idealOfDefinition I)

/-- `StructureSheaf.comap` along a ring homomorphism `f` with a two-sided inverse `g` (over
compatible opens) is an isomorphism in `CommRingCat`; the inverse is `StructureSheaf.comap g`. -/
lemma isIso_ofHom_comap_of_inverse {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (hfg : g.comp f = RingHom.id A) (hgf : f.comp g = RingHom.id B)
    (U : Opens (PrimeSpectrum.Top A)) (V : Opens (PrimeSpectrum.Top B))
    (hV : (V : Set (PrimeSpectrum.Top B)) ⊆
      PrimeSpectrum.comap f ⁻¹' (U : Set (PrimeSpectrum.Top A)))
    (hU : (U : Set (PrimeSpectrum.Top A)) ⊆
      PrimeSpectrum.comap g ⁻¹' (V : Set (PrimeSpectrum.Top B))) :
    IsIso (CommRingCat.ofHom (StructureSheaf.comap f U V hV)) := by
  refine ⟨CommRingCat.ofHom (StructureSheaf.comap g V U hU), ?_, ?_⟩
  · rw [← CommRingCat.ofHom_comp, ← StructureSheaf.comap_comp f g U V U hV hU,
      comap_congr hfg U U _ (fun _ hp => hp)]
    simp
  · rw [← CommRingCat.ofHom_comp, ← StructureSheaf.comap_comp g f V U V hU hV,
      comap_congr hgf V V _ (fun _ hp => hp)]
    simp

include hI in
/-- **The level-`n` map of thickening sheaves of the completion comparison is an
isomorphism.** Its underlying ring map of thickenings is the ring isomorphism
`(quotientEquivPow I hI (n + 1)).symm` (`completionLevelRingHom_eq`), so the induced map on the
structure sheaves of the thickenings is an isomorphism. -/
theorem isIso_completionLevelSheafHom (n : ℕ) :
    IsIso (levelSheafHom I (AdicCompletion.idealOfDefinition I)
      (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n) := by
  -- The underlying ring map `levelRingHom` is the ring isomorphism `(quotientEquivPow).symm`;
  -- its inverse ring hom is `quotientEquivPow`. We record the two-sided inverse relations.
  have hfg : ((AdicCompletion.quotientEquivPow I hI (n + 1)).toRingHom).comp
      (levelRingHom I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n) =
      RingHom.id _ := by
    rw [completionLevelRingHom_eq I hI n]
    ext x
    simp
  have hgf : (levelRingHom I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n).comp
      ((AdicCompletion.quotientEquivPow I hI (n + 1)).toRingHom) = RingHom.id _ := by
    rw [completionLevelRingHom_eq I hI n]
    ext x
    simp
  -- Each component of the underlying presheaf morphism is `comap` of the ring isomorphism
  -- `levelRingHom`, hence an isomorphism.
  haveI happ : ∀ (X : (Opens (FormalSpectrum I))ᵒᵖ),
      IsIso ((levelSheafHom I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R))
        (AdicCompletion.le_comap_idealOfDefinition I) n).hom.app X) := by
    rintro ⟨U⟩
    -- The reverse compatibility of opens: the inverse ring map carries the thickening open of `U`
    -- into the thickening open of the preimage of `U`.
    have hU : (thickeningOpen I n U : Set (PrimeSpectrum (R ⧸ I ^ (n + 1)))) ⊆
        PrimeSpectrum.comap ((AdicCompletion.quotientEquivPow I hI (n + 1)).toRingHom) ⁻¹'
          (thickeningOpen (AdicCompletion.idealOfDefinition I) n
            ((Opens.map (mapTop I (AdicCompletion.idealOfDefinition I)
              (algebraMap R (AdicCompletion I R))
              (AdicCompletion.le_comap_idealOfDefinition I))).obj U) :
            Set (PrimeSpectrum
              (AdicCompletion I R ⧸ (AdicCompletion.idealOfDefinition I) ^ (n + 1)))) := by
      intro p hp
      rw [Set.mem_preimage]
      have hpp : PrimeSpectrum.comap (levelRingHom I (AdicCompletion.idealOfDefinition I)
            (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n)
          (PrimeSpectrum.comap ((AdicCompletion.quotientEquivPow I hI (n + 1)).toRingHom) p) =
          p := by
        rw [← PrimeSpectrum.comap_comp_apply, hfg, PrimeSpectrum.comap_id]
      have key := comap_levelRingHom_toThickening I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n
        (PrimeSpectrum.comap ((AdicCompletion.quotientEquivPow I hI (n + 1)).toRingHom) p)
      rw [hpp] at key
      have hp' : (thickeningTopIso I n).inv p ∈ U := hp
      rw [key] at hp'
      exact hp'
    exact isIso_ofHom_comap_of_inverse
      (levelRingHom I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n)
      ((AdicCompletion.quotientEquivPow I hI (n + 1)).toRingHom) hfg hgf
      (thickeningOpen I n U)
      (thickeningOpen (AdicCompletion.idealOfDefinition I) n
        ((Opens.map (mapTop I (AdicCompletion.idealOfDefinition I)
          (algebraMap R (AdicCompletion I R))
          (AdicCompletion.le_comap_idealOfDefinition I))).obj U))
      (thickeningOpen_map_le I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I) n U) hU
  -- The underlying presheaf morphism is an iso; reflect back along the fully faithful
  -- forgetful functor `TopCat.Sheaf.forget`.
  haveI hhom : IsIso (levelSheafHom I (AdicCompletion.idealOfDefinition I)
      (algebraMap R (AdicCompletion I R))
      (AdicCompletion.le_comap_idealOfDefinition I) n).hom :=
    NatIso.isIso_of_isIso_app _
  haveI : IsIso ((TopCat.Sheaf.forget CommRingCat _).map
      (levelSheafHom I (AdicCompletion.idealOfDefinition I)
        (algebraMap R (AdicCompletion I R))
        (AdicCompletion.le_comap_idealOfDefinition I) n)) :=
    inferInstanceAs (IsIso (levelSheafHom I (AdicCompletion.idealOfDefinition I)
      (algebraMap R (AdicCompletion I R))
      (AdicCompletion.le_comap_idealOfDefinition I) n).hom)
  exact isIso_of_reflects_iso _ (TopCat.Sheaf.forget CommRingCat _)

include hI in
/-- The completion comparison morphism is an isomorphism: it is `limMap` of a natural
isomorphism (each level map is an isomorphism by `isIso_completionLevelSheafHom`) followed by the
inverse of the `preservesLimitIso` isomorphism. -/
theorem isIso_completionCompareSheafHom :
    IsIso (completionCompareSheafHom I) := by
  haveI hnat : IsIso (levelNatTrans I (AdicCompletion.idealOfDefinition I)
      (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨m⟩
    rw [levelNatTrans_app]
    exact isIso_completionLevelSheafHom I hI m
  rw [completionCompareSheafHom, mapSheafHom]
  haveI hlim : IsIso (limMap (levelNatTrans I (AdicCompletion.idealOfDefinition I)
      (algebraMap R (AdicCompletion I R)) (AdicCompletion.le_comap_idealOfDefinition I))) :=
    isIso_limMap _
  exact IsIso.comp_isIso' hlim (Iso.isIso_inv _)

/-- **The structure sheaf of a formal completion is the completion of the tower** (EGA I, 10.8):
the structure sheaf `O_{Spf R^}` of the formal completion of `Spec R` along `V(I)`, transported
along the base homeomorphism `formalCompletion.homeo`, is isomorphic to the inverse limit
`structureSheaf I = limₙ O_{Spec R} / I ^ n` of the structure sheaves of the thickenings of the
original ring `R`. This is what makes `formalCompletion R I hI` a genuine *completion*. -/
def completionStructureSheafIso :
    structureSheaf I ≅
      (TopCat.Sheaf.pushforward CommRingCat
        (mapTop I (AdicCompletion.idealOfDefinition I) (algebraMap R (AdicCompletion I R))
          (AdicCompletion.le_comap_idealOfDefinition I))).obj
        (structureSheaf (AdicCompletion.idealOfDefinition I)) :=
  haveI := isIso_completionCompareSheafHom I hI
  asIso (completionCompareSheafHom I)

end FormalSpectrum

end
