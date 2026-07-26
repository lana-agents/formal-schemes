import FormalSchemes.AdicRingCat
import FormalSchemes.SpfGammaRoundTrip

set_option linter.style.header false

/-!
# `Spf` is fully faithful onto the continuous morphisms of formal schemes

This file packages the Spf–Γ bijection `FormalSpectrum.spfGammaEquiv` (the converse half of
EGA I, 10.4.6, issue 96) as a statement about the formal-spectrum functor
`AdicRingCat.spfFunctor : AdicRingCatᵒᵖ ⥤ FormalScheme` (issue 61 / `AdicRingCat.lean`), whose
faithfulness is already recorded there.

For ordinary schemes `Spec` is fully faithful onto *all* scheme morphisms. As the step-(a)
counterexample of issue 156 shows, the formal-spectrum functor is **not** full onto arbitrary
morphisms of formal schemes: an abstract morphism of locally ringed spaces `Spf S ⟶ Spf R` need
not be continuous (its global-sections map need not carry the ideal of definition of the source
into that of the target), because the structure sheaves carry no ambient topology. The precise
EGA I, 10.4.6 statement is therefore *full faithfulness onto the continuity-restricted morphisms*.

## Main results

* `AdicRingCat.spfHomEquiv`: for adic rings `R`, `S` with finitely generated ideals of definition,
  the bijection
  ```
  (R ⟶ S)  ≃  { f : Spf S ⟶ Spf R // globalSectionsMap f is continuous }
  ```
  sending a continuous ring homomorphism `φ` to `Spf φ`. This is full faithfulness of `Spf` onto
  the continuous morphisms, in `Equiv` form.
* `AdicRingCat.spfHomEquiv_apply`: the forward map is `φ ↦ Spf φ` (`spfFunctor.map φ.op`).
* `AdicRingCat.exists_spfFunctor_map_of_continuous`: **fullness onto the continuous morphisms** —
  every morphism of formal schemes `Spf S ⟶ Spf R` whose global-sections map is continuous is
  `spfFunctor.map φ.op` for a (unique, by faithfulness) continuous ring homomorphism `φ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6).
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AdicRingCat

/-- A morphism of formal schemes is the same data as a morphism of the underlying locally ringed
spaces (formal schemes are a full subcategory of locally ringed spaces). -/
def homLRSEquiv (X Y : FormalScheme.{u}) :
    (X ⟶ Y) ≃ (X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace) where
  toFun f := f.toLRSHom
  invFun g := FormalScheme.Hom.mk g
  left_inv _ := rfl
  right_inv _ := rfl

/-- A morphism of adic rings `R ⟶ S` is exactly a continuous ring homomorphism `R →+* S`, i.e. a
ring homomorphism carrying the ideal of definition of the source into that of the target. -/
def homRingHomEquiv (R S : AdicRingCat.{u}) :
    (R ⟶ S) ≃ { φ : R.carrier →+* S.carrier // R.ideal ≤ S.ideal.comap φ } where
  toFun f := ⟨f.toRingHom, f.continuous'⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`Spf` is fully faithful onto the continuous morphisms** (EGA I, 10.4.6). For adic rings `R`,
`S` with finitely generated ideals of definition, continuous ring homomorphisms `R →+* S`
correspond bijectively to those morphisms of formal schemes `Spf S ⟶ Spf R` whose global-sections
map is again continuous, the correspondence being `φ ↦ Spf φ` (see `spfHomEquiv_apply`).

This is the packaged converse half of EGA I, 10.4.6: the underlying bijection is
`FormalSpectrum.spfGammaEquiv`, transported through the wrappers identifying `AdicRingCat`
morphisms with continuous ring homomorphisms (`homRingHomEquiv`) and `FormalScheme` morphisms with
morphisms of locally ringed spaces (`homLRSEquiv`). The continuity hypothesis on the right is
essential — it is *not* automatic for an arbitrary morphism of locally ringed spaces
(issue 156 counterexample). -/
noncomputable def spfHomEquiv (R S : AdicRingCat.{u}) (hR : R.ideal.FG) (hS : S.ideal.FG) :
    (R ⟶ S) ≃
      { f : spfFunctor.obj (op S) ⟶ spfFunctor.obj (op R) //
        R.ideal ≤ S.ideal.comap
          (FormalSpectrum.globalSectionsMap R.ideal S.ideal f.toLRSHom) } :=
  (homRingHomEquiv R S).trans
    ((FormalSpectrum.spfGammaEquiv R.ideal S.ideal hR hS).trans
      ((homLRSEquiv (spfFunctor.obj (op S)) (spfFunctor.obj (op R))).symm.subtypeEquiv
        (fun _ => Iff.rfl)))

@[simp]
theorem spfHomEquiv_apply (R S : AdicRingCat.{u}) (hR : R.ideal.FG) (hS : S.ideal.FG)
    (f : R ⟶ S) :
    ((spfHomEquiv R S hR hS f : spfFunctor.obj (op S) ⟶ spfFunctor.obj (op R))) =
      spfFunctor.map f.op :=
  rfl

/-- **Fullness of `Spf` onto the continuous morphisms** (EGA I, 10.4.6). Every morphism of formal
schemes `f : Spf S ⟶ Spf R` whose global-sections map carries the ideal of definition of `R` into
that of `S` is `Spf φ` for some continuous ring homomorphism `φ : R →+* S`. By faithfulness of
`spfFunctor` (`AdicRingCat.instFaithfulSpfFunctor`) this `φ` is unique. -/
theorem exists_spfFunctor_map_of_continuous (R S : AdicRingCat.{u}) (hR : R.ideal.FG)
    (hS : S.ideal.FG) (f : spfFunctor.obj (op S) ⟶ spfFunctor.obj (op R))
    (hf : R.ideal ≤ S.ideal.comap (FormalSpectrum.globalSectionsMap R.ideal S.ideal f.toLRSHom)) :
    ∃ φ : R ⟶ S, spfFunctor.map φ.op = f := by
  refine ⟨(spfHomEquiv R S hR hS).symm ⟨f, hf⟩, ?_⟩
  have h := congrArg Subtype.val ((spfHomEquiv R S hR hS).apply_symm_apply ⟨f, hf⟩)
  rw [spfHomEquiv_apply] at h
  exact h

end AdicRingCat
