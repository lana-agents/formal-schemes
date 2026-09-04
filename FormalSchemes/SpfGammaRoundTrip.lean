import FormalSchemes.SpfGammaSheafComponentArbCont
import FormalSchemes.SpfGammaSheafComponent

set_option linter.style.header false

/-!
# The Spf–Γ round-trip (converse of EGA I 10.4.6, step (c))

For adic rings `(R, I)` and `(S, J)`, an arbitrary morphism of formal spectra
`f : Spf S ⟶ Spf R` whose global-sections map `φ = globalSectionsMap I J f` is continuous
(`hφ : I ≤ J.comap φ`) is *reconstructed* from `φ`: the model morphism `Spf φ =
locallyRingedSpaceMap I J φ hφ` equals `f`. Together with `globalSectionsMap_locallyRingedSpaceMap`
(`Γ ∘ Spf = id`) this makes `Spf` and `Γ` mutually inverse on continuous ring homomorphisms
(issue 96): the bijection

```
{ φ : R →+* S // I ≤ J.comap φ } ≃ { f : Spf S ⟶ Spf R // I ≤ J.comap (globalSectionsMap I J f) }.
```

## Main results

* `FormalSpectrum.arbSheafComponent_eq_modelSheafComponent`: the arbitrary-morphism basic-open
  component `arbSheafComponent I J f g` agrees with the reconstructed model component
  `modelSheafComponent I J φ hφ g` (both are the completed localization of `φ`).
* `FormalSpectrum.c_app_eq_on_basicOpen`: the sheaf `c`-components of `f` and of `Spf φ` agree on a
  basic open `D(g)`, after transporting along the base equality `f.base = mapTop`.
* `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`: the full round-trip `Spf φ = f`.
* `FormalSpectrum.spfGammaEquiv`: the resulting bijection (issue 96).

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

/-- **The arbitrary-morphism component equals the reconstructed model component.**
For a morphism `f : Spf S ⟶ Spf R` with continuous global-sections map
(`hφ : I ≤ J.comap (globalSectionsMap I J f)`), the conjugated basic-open component
`arbSheafComponent I J f g` agrees with the reconstructed model morphism's component
`modelSheafComponent I J (globalSectionsMap I J f) hφ g`. Both sides equal the completed
localization `AdicCompletion.mapCompletion (Localization.awayMap (globalSectionsMap I J f) g)`, so
the identity follows from `arbSheafComponent_eq_mapCompletion` and
`modelSheafComponent_eq_mapCompletion`. -/
theorem arbSheafComponent_eq_modelSheafComponent (hI : I.FG) (hJ : J.FG)
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)
    (hφ : I ≤ J.comap (globalSectionsMap I J f)) :
    arbSheafComponent I J f g =
      modelSheafComponent I J (globalSectionsMap I J f) hφ g := by
  rw [arbSheafComponent_eq_mapCompletion I J hI hJ f g hφ,
    modelSheafComponent_eq_mapCompletion I J (globalSectionsMap I J f) hφ g hI hJ]

/-- **The sheaf `c`-components of `f` and of the reconstructed morphism agree on a basic open.**
Cancelling the outer `sectionsBasicOpenEquiv` isomorphisms from
`arbSheafComponent_eq_modelSheafComponent`, the component of `f` on `D(g)`, restricted along
`f.base⁻¹ D(g) = D(φ g)`, equals the reconstructed model morphism's component on `D(g)`, restricted
along `mapTop⁻¹ D(g) = D(φ g)` (`φ = globalSectionsMap I J f`). -/
theorem c_app_eq_on_basicOpen (hI : I.FG) (hJ : J.FG)
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)
    (hφ : I ≤ J.comap (globalSectionsMap I J f)) :
    (((structureSheaf J).presheaf.map
          (eqToHom (congrArg op (base_preimage_basicOpen I J f g)))).hom).comp
        (f.c.app (op (basicOpen I g))).hom =
      (((structureSheaf J).presheaf.map
          (eqToHom (congrArg op
            (map_preimage_basicOpen I J (globalSectionsMap I J f) hφ g)))).hom).comp
        ((mapSheafHom I J (globalSectionsMap I J f) hφ).hom.app (op (basicOpen I g))).hom := by
  refine RingHom.ext fun s => ?_
  have key := RingHom.congr_fun
    (arbSheafComponent_eq_modelSheafComponent I J hI hJ f g hφ)
    (sectionsBasicOpenEquiv I g s)
  -- Unfold each conjugated component at `sectionsBasicOpenEquiv I g s`; the outer
  -- `sectionsBasicOpenEquiv I g` and the inner `.symm` cancel by `symm_apply_apply` (the rest is
  -- definitional composition), leaving the restricted `c`-component applied to `s`.
  have eqA : arbSheafComponent I J f g (sectionsBasicOpenEquiv I g s)
      = sectionsBasicOpenEquiv J (globalSectionsMap I J f g)
          (((structureSheaf J).presheaf.map
              (eqToHom (congrArg op (base_preimage_basicOpen I J f g)))).hom
            ((f.c.app (op (basicOpen I g))).hom s)) :=
    congrArg (fun t => sectionsBasicOpenEquiv J (globalSectionsMap I J f g)
        (((structureSheaf J).presheaf.map
            (eqToHom (congrArg op (base_preimage_basicOpen I J f g)))).hom
          ((f.c.app (op (basicOpen I g))).hom t)))
      ((sectionsBasicOpenEquiv I g).symm_apply_apply s)
  have eqM : modelSheafComponent I J (globalSectionsMap I J f) hφ g (sectionsBasicOpenEquiv I g s)
      = sectionsBasicOpenEquiv J (globalSectionsMap I J f g)
          (((structureSheaf J).presheaf.map
              (eqToHom (congrArg op
                (map_preimage_basicOpen I J (globalSectionsMap I J f) hφ g)))).hom
            (((mapSheafHom I J (globalSectionsMap I J f) hφ).hom.app
              (op (basicOpen I g))).hom s)) :=
    congrArg (fun t => sectionsBasicOpenEquiv J (globalSectionsMap I J f g)
        (((structureSheaf J).presheaf.map
            (eqToHom (congrArg op
              (map_preimage_basicOpen I J (globalSectionsMap I J f) hφ g)))).hom
          (((mapSheafHom I J (globalSectionsMap I J f) hφ).hom.app (op (basicOpen I g))).hom t)))
      ((sectionsBasicOpenEquiv I g).symm_apply_apply s)
  rw [eqA, eqM] at key
  exact (sectionsBasicOpenEquiv J (globalSectionsMap I J f g)).injective key

set_option maxHeartbeats 4000000 in
-- The final assembly matches `f.c` against the reconstructed sheaf hom on every basic open through
-- the defining `ℕᵒᵖ`-limit of the structure sheaves, which the kernel unfolds slowly.
/-- **The Spf–Γ round-trip** (converse of EGA I 10.4.6, step (c)): an arbitrary morphism of formal
spectra `f : Spf S ⟶ Spf R` with continuous global-sections map
(`hφ : I ≤ J.comap (globalSectionsMap I J f)`) is reconstructed from `φ = globalSectionsMap I J f`:
the model morphism `Spf φ = locallyRingedSpaceMap I J φ hφ` equals `f`. Proved by
`LocallyRingedSpace.Hom.ext'` + `PresheafedSpace.ext`: the base maps agree by `base_eq_mapTop`, and
the sheaf `c`-components agree by `TopCat.Sheaf.hom_ext` on the basic-open basis, where on each
`D(g)` the agreement is `c_app_eq_on_basicOpen` (up to the reindexing isomorphisms). -/
theorem locallyRingedSpaceMap_globalSectionsMap (hI : I.FG) (hJ : J.FG)
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (hφ : I ≤ J.comap (globalSectionsMap I J f)) :
    locallyRingedSpaceMap I J (globalSectionsMap I J f) hφ = f := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.ext _ f.toHom (base_eq_mapTop I J f hφ).symm ?_
  rw [CategoryTheory.Functor.whiskerRight_eqToHom_aux]
  refine TopCat.Sheaf.hom_ext (structureSheaf I).presheaf
    ((TopCat.Sheaf.pushforward CommRingCat f.base).obj (structureSheaf J))
    (isBasis_basicOpen I) (fun g => ?_)
  rw [TopCat.Presheaf.comp_app, eqToHom_app]
  -- `rb`, `rm`: the structure-sheaf reindexings along `f.base⁻¹ D(g) = D(φ g)` and
  -- `mapTop⁻¹ D(g) = D(φ g)`; both are isomorphisms (`eqToHom` restrictions).
  set rb := (structureSheaf J).presheaf.map
      (eqToHom (congrArg op (base_preimage_basicOpen I J f g))) with hrb
  set rm := (structureSheaf J).presheaf.map
      (eqToHom (congrArg op (map_preimage_basicOpen I J (globalSectionsMap I J f) hφ g))) with hrm
  -- Reindexed agreement of the two `c`-components on `D(g)`, from `c_app_eq_on_basicOpen`.
  have hc : (f.c.app (op (basicOpen I g))) ≫ rb
      = (locallyRingedSpaceMap I J (globalSectionsMap I J f) hφ).c.app
          (op (basicOpen I g)) ≫ rm := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, hrb, hrm]
    exact c_app_eq_on_basicOpen I J hI hJ f g hφ
  haveI hiso : IsIso rb := by rw [hrb, eqToHom_map]; infer_instance
  -- Cancel the reindexing iso `rb`; both sides collapse to `mapc ≫ rm` (the middle `eqToHom`
  -- restrictions compose to `rm`).
  refine (cancel_mono rb).1 ?_
  refine Eq.trans ?_ hc.symm
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  simp only [hrb, hrm, eqToHom_map]
  exact eqToHom_trans _ _

variable (hI : I.FG) (hJ : J.FG)

/-- **`Spf` and `Γ` are mutually inverse on continuous ring homomorphisms** (issue 96, the payoff of
the converse of EGA I 10.4.6): for finitely generated ideals of definition `I`, `J`, the passage
`φ ↦ Spf φ` is a bijection from continuous ring homomorphisms `R →+* S` (those carrying `I` into
`J.comap φ`) to morphisms of formal spectra `Spf S ⟶ Spf R` with continuous global-sections map.
Its inverse is `f ↦ globalSectionsMap I J f`; the round-trips are
`globalSectionsMap_locallyRingedSpaceMap` (`Γ ∘ Spf = id`) and
`locallyRingedSpaceMap_globalSectionsMap` (`Spf ∘ Γ = id`). -/
def spfGammaEquiv :
    { φ : R →+* S // I ≤ J.comap φ } ≃
      { f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I //
        I ≤ J.comap (globalSectionsMap I J f) } where
  toFun := fun ⟨φ, hφ⟩ =>
    ⟨locallyRingedSpaceMap I J φ hφ, by rw [globalSectionsMap_locallyRingedSpaceMap]; exact hφ⟩
  invFun := fun ⟨f, hf⟩ => ⟨globalSectionsMap I J f, hf⟩
  left_inv := fun ⟨φ, hφ⟩ => Subtype.ext (globalSectionsMap_locallyRingedSpaceMap I J φ hφ)
  right_inv := fun ⟨f, hf⟩ =>
    Subtype.ext (locallyRingedSpaceMap_globalSectionsMap I J hI hJ f hf)

end FormalSpectrum

end
