import FormalSchemes.SpfGammaSheafComponentArb

set_option linter.style.header false

/-!
# The naturality square pinning an arbitrary morphism's basic-open sheaf component to global data

For adic rings `(R, I)` and `(S, J)` and an **arbitrary** morphism of formal spectra
`f : Spf S ⟶ Spf R`, the sheaf `c`-component of `f` on a basic open `D(g)`, conjugated by
`FormalSpectrum.sectionsBasicOpenEquiv` on both sides (`FormalSpectrum.arbSheafComponent`), is a
ring homomorphism `R{1/g} →+* S{1/φ g}` with `φ = FormalSpectrum.globalSectionsMap I J f`.

This file records the **locality-free naturality square** that any full identification of
`arbSheafComponent` must consume: precomposed with the completed-localization structure map
`R → R{1/g}` (`awayCompletionHom`), `arbSheafComponent I J f g` agrees with `φ` postcomposed with
the target structure map `S → S{1/φ g}`. In other words, `arbSheafComponent` fixes the image of `R`
and there it is determined by the global-sections map. It follows from the naturality of the sheaf
morphism `f.c` along the inclusion `D(g) ⊆ ⊤`, the step-(a) target-open identification
`base_preimage_basicOpen`, and the defining formula of `globalSectionsMap`.

The key preliminary is that the structure-sheaf restriction `Γ(⊤, O_{Spf R}) ⟶ Γ(D(g), O_{Spf R})`,
read through `globalSectionsEquiv` on the source and `sectionsBasicOpenEquiv` on the target, is
exactly the completed-localization structure map `awayCompletionHom I g : R →+* R{1/g}`.

This is a reusable slice of the still-open hard half of step (b) of the converse of EGA I 10.4.6
(issue 157): it is the locality-free half of the eventual identification of `arbSheafComponent` with
the completed localization `AdicCompletion.mapCompletion (Localization.awayMap φ g)`.

## Main results

* `FormalSpectrum.awayCompletionHom_eq_restrict`: the structure-sheaf restriction `⊤ → D(g)`, read
  through `globalSectionsEquiv`/`sectionsBasicOpenEquiv`, is `awayCompletionHom I g`.
* `FormalSpectrum.arbSheafComponent_comp_awayCompletionHom`: the naturality square
  `arbSheafComponent I J f g ∘ awayCompletionHom I g = awayCompletionHom J (φ g) ∘ φ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Naturality of the level-`k` limit projection past a structure-sheaf restriction.** For any
morphism of opens `α : W ⟶ V`, restricting a section over `V` to `W` and then projecting to level
`k` agrees with projecting to level `k` and then restricting on the thickening sheaf. This is the
general form of `limitπ_map_eqToHom`, obtained from the naturality of the natural transformation
`limit.π (structureSheafFunctor I) ⟨k⟩`. -/
theorem limitπ_map_hom (k : ℕ) {V W : Opens (FormalSpectrum I)} (α : W ⟶ V)
    (σ : (structureSheaf I).presheaf.obj (op V)) :
    ((limit.π (structureSheafFunctor I) ⟨k⟩).hom.app (op W)).hom
        (((structureSheaf I).presheaf.map α.op).hom σ) =
      ((thickeningSheaf I k).presheaf.map α.op).hom
        (((limit.π (structureSheafFunctor I) ⟨k⟩).hom.app (op V)).hom σ) :=
  DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    ((limit.π (structureSheafFunctor I) ⟨k⟩).hom.naturality α.op)) σ

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The thickening-sheaf restriction commutes with the algebra structure map.** For any
morphism of opens `i : V ⟶ U`, restricting the canonical image `algebraMap (R ⧸ Iⁿ⁺¹) Γ(U) x` of a
residue class `x` gives the canonical image `algebraMap (R ⧸ Iⁿ⁺¹) Γ(V) x` over `V`: the
restriction maps of the thickening sheaf are `R ⧸ Iⁿ⁺¹`-algebra homomorphisms. Proved by
identifying the restriction with `StructureSheaf.comap` of the identity ring map. -/
theorem thickeningSheaf_map_algebraMap (n : ℕ) {U V : Opens (FormalSpectrum I)}
    (i : V ⟶ U) (x : R ⧸ I ^ (n + 1)) :
    ((thickeningSheaf I n).presheaf.map i.op).hom
        (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U)) x) =
      algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op V)) x := by
  have hc := comap_algebraMap (RingHom.id (R ⧸ I ^ (n + 1))) (thickeningOpen I n U)
    (thickeningOpen I n V)
    (fun _ hpV => leOfHom ((Opens.map (thickeningTopIso I n).inv).map i) hpV) x
  rw [StructureSheaf.comap_id_eq_map, RingHom.id_apply] at hc
  exact hc

/-- **The structure-sheaf restriction `⊤ → D(g)` is the completed-localization structure map.**
Read through `globalSectionsEquiv` on `Γ(⊤, O_{Spf R})` and `sectionsBasicOpenEquiv` on
`Γ(D(g), O_{Spf R})`, the restriction map of the structure sheaf along the inclusion `D(g) ⊆ ⊤`
is exactly `awayCompletionHom I g : R →+* R{1/g}` (the composite `R → R_g → R{1/g}`). -/
theorem awayCompletionHom_eq_restrict (g : R) :
    awayCompletionHom I g =
      (sectionsBasicOpenEquiv I g).toRingHom.comp
        (((structureSheaf I).presheaf.map
            (homOfLE (le_top (a := basicOpen I g))).op).hom.comp
          (globalSectionsEquiv I).symm.toRingHom) := by
  refine RingHom.ext fun r => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  cases n with
  | zero =>
    haveI : Subsingleton (Localization.Away g ⧸
        (I.map (algebraMap R (Localization.Away g))) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    exact Subsingleton.elim _ _
  | succ k =>
    -- LHS: `awayCompletionHom I g r` is `of` of the localization image, so its level-`k+1`
    -- component is the residue of `algebraMap R R_g r`.
    rw [show awayCompletionHom I g r =
        AdicCompletion.of (I.map (algebraMap R (Localization.Away g))) (Localization.Away g)
          (algebraMap R (Localization.Away g) r) from rfl,
      AdicCompletion.evalₐ_of]
    -- RHS: unfold the conjugated restriction and read it level by level.
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [eval_sectionsBasicOpenEquiv I g k,
      limitπ_map_hom I k (homOfLE (le_top (a := basicOpen I g)))
        ((globalSectionsEquiv I).symm r)]
    -- the level-`k` component of `(globalSectionsEquiv I).symm r` over `⊤` is the residue of `r`
    have hs0 : ((limit.π (structureSheafFunctor I) ⟨k⟩).hom.app
          (op (⊤ : Opens (FormalSpectrum I)))).hom ((globalSectionsEquiv I).symm r) =
        algebraMap (R ⧸ I ^ (k + 1))
          ((thickeningSheaf I k).presheaf.obj (op (⊤ : Opens (FormalSpectrum I))))
          (Ideal.Quotient.mk (I ^ (k + 1)) r) := by
      have h := mk_globalSectionsEquiv I k ((globalSectionsEquiv I).symm r)
      rw [RingEquiv.apply_symm_apply] at h
      rw [← topLevelEquiv_symm_apply]
      exact (RingEquiv.eq_symm_apply (topLevelEquiv I k)).mpr h.symm
    rw [hs0, thickeningSheaf_map_algebraMap, basicOpenLevelEquiv_algebraMap_mk]

/-- **The naturality square pinning `arbSheafComponent` to global data.**
For an arbitrary morphism `f : Spf S ⟶ Spf R`, the conjugated basic-open sheaf component
`arbSheafComponent I J f g`, precomposed with the source structure map `awayCompletionHom I g`,
equals `φ = globalSectionsMap I J f` postcomposed with the target structure map
`awayCompletionHom J (φ g)`. This says the component fixes the image of `R` and there is determined
by the global-sections map — the locality-free input for the full identification. -/
theorem arbSheafComponent_comp_awayCompletionHom
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R) :
    (arbSheafComponent I J f g).comp (awayCompletionHom I g) =
      (awayCompletionHom J (globalSectionsMap I J f g)).comp (globalSectionsMap I J f) := by
  refine RingHom.ext fun r => ?_
  -- `hL1`: Lemma 1 solved for `(sectionsBasicOpenEquiv I g).symm ∘ awayCompletionHom I g`.
  have hL1 : (sectionsBasicOpenEquiv I g).symm (awayCompletionHom I g r) =
      ((structureSheaf I).presheaf.map (homOfLE (le_top (a := basicOpen I g))).op).hom
        ((globalSectionsEquiv I).symm r) := by
    rw [RingHom.congr_fun (awayCompletionHom_eq_restrict I g) r]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
  -- `hnat`: naturality of the sheaf morphism `f.c` along the inclusion `D(g) ⊆ ⊤`.
  have hnat (y : (structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))) :
      (f.c.app (op (basicOpen I g))).hom
          (((structureSheaf I).presheaf.map
            (homOfLE (le_top (a := basicOpen I g))).op).hom y) =
        ((structureSheaf J).presheaf.map
            ((Opens.map f.base).map (homOfLE (le_top (a := basicOpen I g)))).op).hom
          ((f.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom y) :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (f.c.naturality (homOfLE (le_top (a := basicOpen I g))).op)) y
  -- `crux`: the target-open transport `eqToHom` absorbs the pushforward restriction into the
  -- direct restriction `⊤ → D(φ g)`, since restriction maps in a thin category are unique.
  have hmorph : ((Opens.map f.base).map (homOfLE (le_top (a := basicOpen I g)))).op ≫
        eqToHom (congrArg op (base_preimage_basicOpen I J f g)) =
      (homOfLE (le_top (a := basicOpen J (globalSectionsMap I J f g)))).op :=
    Subsingleton.elim _ _
  have cruxcat :
      (structureSheaf J).presheaf.map
            ((Opens.map f.base).map (homOfLE (le_top (a := basicOpen I g)))).op ≫
          (structureSheaf J).presheaf.map
            (eqToHom (congrArg op (base_preimage_basicOpen I J f g))) =
        (structureSheaf J).presheaf.map
          (homOfLE (le_top (a := basicOpen J (globalSectionsMap I J f g)))).op := by
    rw [← Functor.map_comp]
    exact congrArg (fun m => (structureSheaf J).presheaf.map m) hmorph
  have crux (σ : (structureSheaf J).presheaf.obj
        (op ((Opens.map f.base).obj (⊤ : Opens (FormalSpectrum I))))) :
      ((structureSheaf J).presheaf.map
            (eqToHom (congrArg op (base_preimage_basicOpen I J f g)))).hom
          (((structureSheaf J).presheaf.map
              ((Opens.map f.base).map (homOfLE (le_top (a := basicOpen I g)))).op).hom σ) =
        ((structureSheaf J).presheaf.map
            (homOfLE (le_top (a := basicOpen J (globalSectionsMap I J f g)))).op).hom σ :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom cruxcat) σ
  -- Unfold the two composite definitions into nested applications (definitional, `rfl`).
  have harb (x : awayCompletion I g) :
      arbSheafComponent I J f g x =
        sectionsBasicOpenEquiv J (globalSectionsMap I J f g)
          (((structureSheaf J).presheaf.map
              (eqToHom (congrArg op (base_preimage_basicOpen I J f g)))).hom
            ((f.c.app (op (basicOpen I g))).hom
              ((sectionsBasicOpenEquiv I g).symm x))) :=
    rfl
  have haway (y : S) :
      awayCompletionHom J (globalSectionsMap I J f g) y =
        sectionsBasicOpenEquiv J (globalSectionsMap I J f g)
          (((structureSheaf J).presheaf.map
              (homOfLE (le_top (a := basicOpen J (globalSectionsMap I J f g)))).op).hom
            ((globalSectionsEquiv J).symm y)) := by
    rw [RingHom.congr_fun (awayCompletionHom_eq_restrict J (globalSectionsMap I J f g)) y]
    rfl
  -- Assemble: LHS through `harb`, `hL1`, `hnat`, `crux`; RHS through `haway` and the `φ`-formula.
  rw [RingHom.comp_apply, RingHom.comp_apply, harb, hL1, hnat, crux, haway,
    globalSectionsMap_apply I J f r, RingEquiv.symm_apply_apply]

end FormalSpectrum

end
