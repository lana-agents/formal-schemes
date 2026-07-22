import FormalSchemes.IndScheme
import FormalSchemes.AdicCompletionLimit
import Mathlib.CategoryTheory.Limits.Yoneda

set_option linter.style.header false

/-!
# Morphisms out of a formal spectrum as a limit of quotient-hom sets

Let `(R, I)` be a complete adic ring and `Spf R = FormalSpectrum.locallyRingedSpaceObj I` its
formal spectrum, viewed as a locally ringed space. `FormalSchemes/IndScheme.lean` establishes the
affine-target mapping-out property

```
Hom_{LRS}(Spf R, Spec B) ≃ (B →+* R).
```

This file repackages the right-hand side as an honest categorical *limit*. Since `R` is a complete
adic ring, `R = lim_n R ⧸ Iⁿ` (`AdicCompletion.limitRingEquiv` together with the completeness
isomorphism `AdicCompletion.ofAlgEquiv`), and the `coyoneda` functor `coyoneda.obj (op (Spec B))`
— equivalently `Hom(Spec B, -)` transported to rings, i.e. `B →+* -` — preserves limits. Hence

```
Hom_{LRS}(Spf R, Spec B) ≃ lim_n (B →+* R ⧸ Iⁿ) = lim_n Hom(Spec (R ⧸ Iⁿ), Spec B),
```

the genuine `lim_n Hom(Spec (R ⧸ Iⁿ), Spec B)` form of the ind-scheme description of `Spf R`
requested in EGA I, §10.6 (10.6.7): `Spf R` is the filtered colimit of its infinitesimal
thickenings `Spec (R ⧸ Iⁿ)`, so mapping out of it is the limit over `n` of mapping out of each
thickening.

## Main definitions

* `FormalSpectrum.ringLimitEquiv I : R ≃+* limit (AdicCompletion.quotientTower I)`: completeness of
  `R`, i.e. `R = lim_n R ⧸ Iⁿ` at the level of `CommRingCat`.
* `FormalSpectrum.specHomLimitEquiv I B`: the equivalence
  `Hom_{LRS}(Spf R, Spec B) ≃ lim_n (B →+* R ⧸ Iⁿ)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- **Completeness of a complete adic ring, categorically**: `R` is the limit, in `CommRingCat`,
of its quotient tower `n ↦ R ⧸ Iⁿ`. This is the composite of the completeness isomorphism
`R ≃+* AdicCompletion I R` (`AdicCompletion.ofAlgEquiv`) with the identification of the adic
completion as `lim_n R ⧸ Iⁿ` (`AdicCompletion.limitRingEquiv`). -/
def ringLimitEquiv : R ≃+* (limit (AdicCompletion.quotientTower I) : CommRingCat) :=
  (AdicCompletion.ofAlgEquiv (S := R) I).toRingEquiv.trans (AdicCompletion.limitRingEquiv I)

/-- The iso `CommRingCat.of R ≅ limit (quotientTower I)` in `CommRingCat` underlying
`ringLimitEquiv`, with codomain literally the limit object (not `CommRingCat.of ↥(limit …)`). -/
def ringLimitIso :
    CommRingCat.of R ≅ (limit (AdicCompletion.quotientTower I) : CommRingCat) :=
  (ringLimitEquiv I).toCommRingCatIso

/-- **Morphisms out of `Spf R` as a limit of quotient-hom sets** (EGA I, 10.6.7): a morphism of
locally ringed spaces `Spf R ⟶ Spec B` is the same datum as a compatible family of ring
homomorphisms `(B →+* R ⧸ Iⁿ)ₙ`, i.e. an element of `lim_n Hom(Spec (R ⧸ Iⁿ), Spec B)`. -/
def specHomLimitEquiv (B : Type u) [CommRing B] :
    (locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) ≃
      (limit (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))) : Type u) :=
  (specHomEquiv I B).trans <|
    (ConcreteCategory.homEquiv (X := CommRingCat.of B) (Y := CommRingCat.of R)).symm.trans <|
      (Iso.homCongr (Iso.refl (CommRingCat.of B)) (ringLimitIso I)).trans
        (IsLimit.conePointUniqueUpToIso
          (isLimitOfPreserves (coyoneda.obj (op (CommRingCat.of B)))
            (limit.isLimit (AdicCompletion.quotientTower I)))
          (limit.isLimit
            (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))))).toEquiv

end FormalSpectrum
