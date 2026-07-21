import FormalSchemes.SpfGamma
import FormalSchemes.Thickenings
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

set_option linter.style.header false

/-!
# The affine-target mapping-out universal property of the formal spectrum

Let `(R, I)` be a complete adic ring and `Spf R = FormalSpectrum.locallyRingedSpaceObj I` its
formal spectrum, viewed as a locally ringed space. This file establishes the *affine-target*
half of the mapping-out universal property of `Spf R` (EGA I, 10.6.7–10.6.10, issue 97):
morphisms of locally ringed spaces into an affine scheme are ring homomorphisms out of its ring
of functions,

```
Hom_{LRS}(Spf R, Spec B) ≃ (B →+* R).
```

The construction is a short chain of equivalences built from the Mathlib adjunction
`Γ ⊣ Spec` (`AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction`) and the identification
`Γ(⊤, O_{Spf R}) ≃+* R` of `FormalSchemes/Sections.lean`
(`FormalSpectrum.globalSectionsEquiv`). Concretely, a morphism `Spf R ⟶ Spec B` corresponds by
the adjunction to a ring homomorphism `B → Γ(Spf R)`, and then `globalSectionsEquiv` rewrites the
target as `R`.

Since `R` is a complete adic ring, `R = lim_n R ⧸ Iⁿ`, so this equivalence is the affine avatar
of the ind-scheme description of `Spf R` as the (filtered) colimit of its infinitesimal
thickenings `Spec (R ⧸ Iⁿ⁺¹)` (EGA I, 10.6.3): equivalently

```
Hom(Spf R, Spec B) ≃ lim_n Hom(Spec (R ⧸ Iⁿ⁺¹), Spec B),
```

the cone being precomposition with the thickening morphisms `thickeningMap I n`. The
identification `Hom(Spec (R ⧸ Iⁿ⁺¹), Spec B) ≃ (B →+* R ⧸ Iⁿ⁺¹)` is the ordinary `Γ ⊣ Spec`
adjunction on schemes, and `R ≃ lim_n R ⧸ Iⁿ⁺¹` is completeness of `R`, so the two `lim`s agree.

## Main definitions and results

* `FormalSpectrum.specHomEquiv`: the universal property
  `Hom_{LRS}(Spf R, Spec B) ≃ (B →+* R)`.
* `FormalSpectrum.specHomEquiv_symm_apply`: the inverse sends `φ : B →+* R` to the composite
  `Spf R → Spec Γ(Spf R) → Spec B` (unit of the adjunction followed by `Spec` of `φ`).
* `FormalSpectrum.commRingHomEquiv`: the auxiliary identification of category homomorphisms
  `B ⟶ Γ(Spf R)` with ring homomorphisms `B →+* R` through `globalSectionsEquiv`.

## Remaining follow-up

Left to future work: the general (non-affine target) mapping-out property
`Hom_{LRS}(Spf R, X) ≃ ...` for an arbitrary locally ringed space / scheme `X`; the explicit
categorical repackaging of the right-hand side as a genuine `lim_n Hom(Spec (R ⧸ Iⁿ⁺¹), -)`; and a
`simp`-normal forward computation rule expressing `specHomEquiv` through the sheaf component
`f.c.app (op ⊤)` (mirroring `FormalSpectrum.globalSectionsMap_apply`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-!
### The affine-target universal property

We build the equivalence `Hom_{LRS}(Spf R, Spec B) ≃ (B →+* R)` by chaining:
`Γ ⊣ Spec` adjunction `homEquiv`, the opposite-hom equivalence, and the global-sections
identification `globalSectionsEquiv I : Γ(⊤, O_{Spf R}) ≃+* R`.
-/

/-- The identification of category homomorphisms `B ⟶ Γ(Spf R)` with ring homomorphisms
`B →+* R`, using `globalSectionsEquiv I : Γ(⊤, O_{Spf R}) ≃+* R`. -/
def commRingHomEquiv (B : Type u) [CommRing B] :
    (CommRingCat.of B ⟶ LocallyRingedSpace.Γ.obj (op (locallyRingedSpaceObj I))) ≃ (B →+* R) :=
  (Iso.homCongr (Iso.refl (CommRingCat.of B))
      (globalSectionsEquiv I).toCommRingCatIso).trans
    (ConcreteCategory.homEquiv (X := CommRingCat.of B) (Y := CommRingCat.of R))

/-- **The affine-target mapping-out universal property of `Spf R`** (EGA I, 10.6.7): morphisms of
locally ringed spaces `Spf R ⟶ Spec B` correspond to ring homomorphisms `B →+* R`. -/
def specHomEquiv (B : Type u) [CommRing B] :
    (locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) ≃ (B →+* R) :=
  (Adjunction.homEquiv ΓSpec.locallyRingedSpaceAdjunction (locallyRingedSpaceObj I)
        (op (CommRingCat.of B))).symm.trans
    ((opEquiv (op (LocallyRingedSpace.Γ.obj (op (locallyRingedSpaceObj I))))
          (op (CommRingCat.of B))).trans
      (commRingHomEquiv I B))

/-- The inverse of `specHomEquiv` sends a ring homomorphism `φ : B →+* R` to the composite
`Spf R ⟶ Spec Γ(Spf R) ⟶ Spec B`: the unit of the `Γ ⊣ Spec` adjunction followed by `Spec` of
`φ` (transported along `globalSectionsEquiv`). -/
theorem specHomEquiv_symm_apply (B : Type u) [CommRing B] (φ : B →+* R) :
    (specHomEquiv I B).symm φ =
      identityToΓSpec.app (locallyRingedSpaceObj I) ≫
        Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom ((globalSectionsEquiv I).symm.toRingHom.comp φ)) :=
  rfl

/-- Computation rule for `commRingHomEquiv`: it sends a homomorphism `g : B ⟶ Γ(Spf R)` to the
ring homomorphism `b ↦ globalSectionsEquiv I (g b)`. -/
theorem commRingHomEquiv_apply (B : Type u) [CommRing B]
    (g : CommRingCat.of B ⟶ LocallyRingedSpace.Γ.obj (op (locallyRingedSpaceObj I))) (b : B) :
    commRingHomEquiv I B g b = globalSectionsEquiv I (g.hom b) :=
  rfl

end FormalSpectrum
