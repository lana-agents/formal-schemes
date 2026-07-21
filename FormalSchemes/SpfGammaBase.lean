import FormalSchemes.SpfGamma
import FormalSchemes.Thickenings

set_option linter.style.header false

/-!
# The base map of a morphism of formal spectra is forced by global sections

For adic rings `(R, I)` and `(S, J)`, a morphism of locally ringed spaces
`f : Spf S ⟶ Spf R` induces a ring homomorphism `φ = globalSectionsMap I J f : R → S` on global
sections. This file proves that the underlying continuous base map of `f` is completely
determined by `φ`: on the level of the ambient prime spectra,

```
toPrimeSpectrum (f.base y) = PrimeSpectrum.comap φ (toPrimeSpectrum y)
```

for every `y : Spf S` (`FormalSpectrum.base_toPrimeSpectrum_eq`). This is the formal-spectrum
analogue of Mathlib's `AlgebraicGeometry.ΓSpec.toΓSpecFun` — for a morphism of locally ringed
spaces into `Spec`, the image of a point is `y ↦ (stalkMap f y)⁻¹(maximal ideal)` — and is
half of the converse of the `Spf ⊣ Γ` correspondence (EGA I, 10.4.6).

## Strategy

The key computation (`FormalSpectrum.isUnit_germ_top_iff`) characterises, at a point
`x : Spf R`, the prime `x` by invertibility of germs: for `r : R`, the germ at `x` of the global
section corresponding to `r` is a unit in the stalk of `O_{Spf R}` iff `r mod I ∉ x`. This is
proved by projecting to the level-`0` thickening sheaf (`stalkProj`), where invertibility of a
germ is detected by its *value* at the corresponding point of `Spec (R ⧸ I)`
(`isUnit_thickeningGerm_iff_isUnit_value`), and a value in a localization at a prime is a unit iff
the element avoids the prime (`IsLocalization.AtPrime.isUnit_to_map_iff`).

Applying this on both `Spf R` and `Spf S` and connecting the germs through the stalk map of `f`
(which is local, `LocallyRingedSpace.isLocalHomStalkMap`, and identifies `f.c`-images of germs,
`LocallyRingedSpace.stalkMap_germ_apply`) pins down the prime `f.base y` in terms of `φ`.

## A remark on continuity of `φ`

The map `mapTop I J φ hφ` induced by `φ` requires the *strong* hypothesis
`hφ : I ≤ J.comap φ`, i.e. `φ (I) ⊆ J`, in order to form the ring map `R ⧸ I → S ⧸ J`.
This
containment is **not** derivable from `f` alone: locality of the stalk maps only forces
`φ (I) ⊆ √J` (each `φ a`, `a ∈ I`, is topologically nilpotent), which can be strictly
weaker.
For instance, with `R = k[[x]]`, `I = (x)` and `S = (k[ε]/ε²)[[y]]`, `J = (y)`, the local
homomorphism `x ↦ ε` gives a morphism of formal spectra whose `globalSectionsMap` sends
`x ∈ I` to `ε ∉ J`. Accordingly `FormalSpectrum.base_eq_mapTop` takes `hφ` as a hypothesis
rather than deriving it, while the containment-free statement
`FormalSpectrum.base_toPrimeSpectrum_eq` records the fully general fact.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

/-!
### The prime at a point is detected by invertibility of germs of global sections
-/

section GermCriterion

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

set_option maxHeartbeats 1000000 in
-- The proof projects a germ to level `0` and evaluates it, unfolding the section rings of the
-- structure sheaf; this is slow.
/-- **Germs of global sections detect the prime**: the germ at `x : Spf R` of the global section
corresponding to `r : R` is a unit in the stalk of `O_{Spf R}` if and only if `r mod I` does not
lie in the prime `x`. This is the formal-spectrum analogue of
`AlgebraicGeometry.notMem_prime_iff_unit_in_stalk`. -/
theorem isUnit_germ_top_iff (x : FormalSpectrum I) (r : R) :
    IsUnit (((structureSheaf I).presheaf.germ (⊤ : Opens (FormalSpectrum I)) x trivial).hom
        ((globalSectionsEquiv I).symm r)) ↔
      Ideal.Quotient.mk I r ∉ x.asIdeal := by
  have htop : x ∈ (⊤ : Opens (FormalSpectrum I)) := trivial
  set s := (globalSectionsEquiv I).symm r with hs
  -- Step 1: invertibility of the germ is detected at level `0` of the tower.
  have hproj : IsUnit (((structureSheaf I).presheaf.germ
        (⊤ : Opens (FormalSpectrum I)) x htop).hom s) ↔
      IsUnit ((stalkProj I x 0).hom
        (((structureSheaf I).presheaf.germ (⊤ : Opens (FormalSpectrum I)) x htop).hom s)) := by
    constructor
    · exact fun h => h.map _
    · exact fun h => isUnit_of_isUnit_stalkProj I x 0 _ h
  rw [hproj]
  -- Step 2: the level-`0` projection of the germ is the germ of the level-`0` component.
  rw [show (stalkProj I x 0).hom
        (((structureSheaf I).presheaf.germ (⊤ : Opens (FormalSpectrum I)) x htop).hom s) =
      ((thickeningSheaf I 0).presheaf.germ (⊤ : Opens (FormalSpectrum I)) x htop).hom
        (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
          (op (⊤ : Opens (FormalSpectrum I)))).hom s) from
    TopCat.Presheaf.stalkFunctor_map_germ_apply (⊤ : Opens (FormalSpectrum I)) x htop
      (limit.π (structureSheafFunctor I) ⟨0⟩).hom s]
  -- Step 3: invertibility of a germ of the level-`0` sheaf is invertibility of its value.
  haveI hAway : IsLocalization.Away (Ideal.Quotient.mk (I ^ (0 + 1)) (1 : R))
      ((Spec.structureSheaf (R ⧸ I ^ (0 + 1))).presheaf.obj
        (op (thickeningOpen I 0 (⊤ : Opens (FormalSpectrum I))))) := by
    have h := isLocalization_away_basicOpen_sections I 0 (1 : R)
    rw [basicOpen_one] at h
    exact h
  rw [isUnit_thickeningGerm_iff_isUnit_value I 0 x (⊤ : Opens (FormalSpectrum I)) htop
    (Ideal.Quotient.mk (I ^ (0 + 1)) (1 : R))
    (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
      (op (⊤ : Opens (FormalSpectrum I)))).hom s)]
  -- Step 4: the level-`0` component of `s` is the constant section `r mod I`.
  have hpi : ((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
        (op (⊤ : Opens (FormalSpectrum I)))).hom s =
      algebraMap (R ⧸ I ^ (0 + 1))
        ((Spec.structureSheaf (R ⧸ I ^ (0 + 1))).presheaf.obj
          (op (thickeningOpen I 0 (⊤ : Opens (FormalSpectrum I)))))
        (Ideal.Quotient.mk (I ^ (0 + 1)) r) := by
    have hmk := mk_globalSectionsEquiv I 0 s
    rw [show globalSectionsEquiv I s = r from (globalSectionsEquiv I).apply_symm_apply r] at hmk
    have hval : (topLevelEquiv I 0).symm (Ideal.Quotient.mk (I ^ (0 + 1)) r) =
        ((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
          (op (⊤ : Opens (FormalSpectrum I)))).hom s := by
      rw [hmk, RingEquiv.symm_apply_apply]
    rw [topLevelEquiv_symm_apply] at hval
    exact hval.symm
  rw [hpi, StructureSheaf.sectionValue_algebraMap,
    IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime ((thickeningTopIso I 0).hom x).asIdeal)
      ((thickeningTopIso I 0).hom x).asIdeal (Ideal.Quotient.mk (I ^ (0 + 1)) r),
    Ideal.mem_primeCompl_iff]
  -- Step 5: `r mod I^1 ∉ (thickeningTopIso x)` iff `r mod I ∉ x`.
  rw [show ((thickeningTopIso I 0).hom x).asIdeal =
      Ideal.comap (Ideal.Quotient.factor (Ideal.pow_le_self (one_ne_zero) : I ^ 1 ≤ I))
        x.asIdeal from PrimeSpectrum.comap_asIdeal _ _,
    Ideal.mem_comap, Ideal.Quotient.factor_mk]

end GermCriterion

/-!
### The base map is forced by global sections
-/

section BaseMap

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-- **The base map of a morphism of formal spectra is forced by its action on global sections**
(containment-free form): for `φ = globalSectionsMap I J f`, the composite of `f.base` with the
inclusion `Spf R ↪ Spec R` equals `Spec φ` composed with `Spf S ↪ Spec S`. Equivalently, the
prime of `R` under `x ↦ f.base x` is `φ ⁻¹'` of the prime of `S`. -/
theorem base_toPrimeSpectrum_eq (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (y : FormalSpectrum J) :
    toPrimeSpectrum I (f.base y) =
      PrimeSpectrum.comap (globalSectionsMap I J f) (toPrimeSpectrum J y) := by
  apply PrimeSpectrum.ext
  ext a
  rw [toPrimeSpectrum, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, toPrimeSpectrum,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  -- reduces to: `a mod I ∈ f.base y` iff `φ a mod J ∈ y`
  rw [← not_iff_not, ← isUnit_germ_top_iff I (f.base y) a,
    ← isUnit_germ_top_iff J y (globalSectionsMap I J f a)]
  -- connect the two germs through the (local) stalk map of `f`
  have hφeq : f.c.app (op (⊤ : Opens (FormalSpectrum I)))
        ((globalSectionsEquiv I).symm a) =
      (globalSectionsEquiv J).symm (globalSectionsMap I J f a) := by
    rw [globalSectionsMap_apply, RingEquiv.symm_apply_apply]
  have hstalk : ((structureSheaf J).presheaf.germ (⊤ : Opens (FormalSpectrum J)) y trivial).hom
        ((globalSectionsEquiv J).symm (globalSectionsMap I J f a)) =
      (f.stalkMap y).hom
        (((structureSheaf I).presheaf.germ (⊤ : Opens (FormalSpectrum I)) (f.base y) trivial).hom
          ((globalSectionsEquiv I).symm a)) := by
    rw [← hφeq]
    exact (LocallyRingedSpace.stalkMap_germ_apply f (⊤ : Opens (FormalSpectrum I)) y trivial
      ((globalSectionsEquiv I).symm a)).symm
  rw [hstalk]
  exact (isUnit_map_iff (f.stalkMap y).hom _).symm

/-- **The base map is forced by global sections** (packaged as an equality of continuous maps):
given the continuity hypothesis `hφ : I ≤ J.comap φ` for `φ = globalSectionsMap I J f`, the
base
map of `f` is exactly the map `mapTop` induced by `φ`. The hypothesis `hφ` cannot be dropped or
derived from `f` alone; see the module docstring. -/
theorem base_eq_mapTop (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (hφ : I ≤ J.comap (globalSectionsMap I J f)) :
    f.base = mapTop I J (globalSectionsMap I J f) hφ := by
  ext y
  apply (isClosedEmbedding_toPrimeSpectrum I).injective
  rw [base_toPrimeSpectrum_eq I J f y]
  exact (toPrimeSpectrum_map I J (globalSectionsMap I J f) hφ y).symm

end BaseMap

end FormalSpectrum
