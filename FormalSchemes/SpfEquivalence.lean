import FormalSchemes.AdicOnSections
import FormalSchemes.SpfFullyFaithful
import FormalSchemes.SpfGammaFunctorial

set_option linter.style.header false

/-!
# `Spf` as an equivalence onto affine formal schemes (EGA I, 10.4.6)

`FormalSchemes/AdicRingCat.lean` records the formal-spectrum functor
`AdicRingCat.spfFunctor : AdicRingCatᵒᵖ ⥤ FormalScheme` and its faithfulness, and
`FormalSchemes/SpfFullyFaithful.lean` (issue 96) records the underlying bijection
`AdicRingCat.spfHomEquiv` between continuous ring homomorphisms `R →+* S` and those morphisms of
formal schemes `Spf S ⟶ Spf R` whose global-sections map is again continuous. This file assembles
those two into the categorical form of EGA I, 10.4.6: `Spf` is an **anti-equivalence** between
adic rings with finitely generated ideal of definition and *affine formal schemes*.

## Why the target category is built by hand

`spfFunctor` is **not** full onto `FormalScheme`: an abstract morphism of locally ringed spaces
`Spf S ⟶ Spf R` need not be continuous, i.e. its global-sections map need not carry the ideal of
definition of the target into that of the source (the counterexample of issue 156). So the honest
statement restricts the morphisms, and the restriction is *not* a property of a morphism of
`FormalScheme` alone: continuity reads `R.ideal ≤ S.ideal.comap (globalSectionsMap …)`, which
mentions the two objects' **ideals of definition** — data an object of `FormalScheme` does not
carry.

Consequently `AffineFormalSchemeCat` below has adic rings (with a finitely generated ideal of
definition, as `spfHomEquiv` requires on both sides) as objects, and the *continuous* morphisms
between their formal spectra as morphisms. This is EGA's category of affine formal schemes, and it
is what turns full faithfulness of `Spf` into an equivalence: the functor is the identity on
objects, so essential surjectivity is free and all the content sits in the hom-sets, where it is
exactly `spfHomEquiv`.

## Main definitions and results

* `AdicRingCat.IsFG` / `AdicRingCatFG`: the full subcategory of adic rings whose ideal of
  definition is finitely generated.
* `AffineFormalSchemeCat`: the category of affine formal schemes and continuous morphisms.
* `spfEquivFunctor : AdicRingCatFGᵒᵖ ⥤ AffineFormalSchemeCat`: the formal spectrum, corestricted.
* `spfEquivFunctorFullyFaithful`: the `Functor.FullyFaithful` datum, from `spfHomEquiv` — the
  packaging named as a follow-up in the scope note of `AdicRingCat.lean`.
* `spfEquivalence : AdicRingCatFGᵒᵖ ≌ AffineFormalSchemeCat`: **EGA I, 10.4.6**.
* `AdicRingCat.isIso_of_isIso_spf`: `Spf` reflects isomorphisms — a continuous ring homomorphism
  whose `Spf` admits a *continuous* two-sided inverse is itself an isomorphism of adic rings.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AdicRingCat

/-- The property, of an adic ring, that its ideal of definition is finitely generated. This is the
standing hypothesis of the Spf–Γ bijection `AdicRingCat.spfHomEquiv`. -/
def IsFG : ObjectProperty AdicRingCat.{u} := fun R => R.ideal.FG

/-- **`Spf φ` is continuous on global sections.** The morphism of formal schemes induced by a
morphism of adic rings `φ : R ⟶ S` has continuous global-sections map — indeed that map is `φ`
itself, by `FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`. -/
theorem le_comap_globalSectionsMap_spfFunctor_map {R S : AdicRingCat.{u}} (φ : R ⟶ S) :
    R.ideal ≤ S.ideal.comap
      (FormalSpectrum.globalSectionsMap R.ideal S.ideal (spfFunctor.map φ.op).toLRSHom) := by
  have h : FormalSpectrum.globalSectionsMap R.ideal S.ideal (spfFunctor.map φ.op).toLRSHom =
      φ.toRingHom :=
    FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap R.ideal S.ideal φ.toRingHom
      φ.continuous'
  rw [h]
  exact φ.continuous'

end AdicRingCat

/-- The full subcategory of adic rings whose ideal of definition is finitely generated. -/
abbrev AdicRingCatFG := AdicRingCat.IsFG.FullSubcategory

/-- An **affine formal scheme**: an adic ring `(R, I)` with `I` finitely generated, thought of as
the affine formal scheme `Spf R` *together with* its ideal of definition. The ideal has to be
carried along: the continuity condition cutting out the right morphisms mentions it, so it cannot
be recovered from the underlying formal scheme. -/
structure AffineFormalSchemeCat where
  /-- The adic ring whose formal spectrum this is. -/
  ring : AdicRingCat.{u}
  /-- Its ideal of definition is finitely generated. -/
  fg : ring.ideal.FG

namespace AffineFormalSchemeCat

/-- The underlying formal scheme `Spf R` of an affine formal scheme. -/
abbrev toFormalScheme (X : AffineFormalSchemeCat.{u}) : FormalScheme.{u} :=
  AdicRingCat.spfFunctor.obj (op X.ring)

/-- A **morphism of affine formal schemes** is a morphism `Spf X ⟶ Spf Y` of formal schemes whose
global-sections map `Γ(Spf Y) → Γ(Spf X)` is continuous, i.e. carries the ideal of definition of
`Y` into that of `X`. This continuity is not automatic (issue 156). -/
@[ext]
structure Hom (X Y : AffineFormalSchemeCat.{u}) where
  /-- The underlying morphism of formal schemes. -/
  toHom : X.toFormalScheme ⟶ Y.toFormalScheme
  /-- Continuity of the global-sections map. -/
  continuous' : Y.ring.ideal ≤ X.ring.ideal.comap
    (FormalSpectrum.globalSectionsMap Y.ring.ideal X.ring.ideal toHom.toLRSHom)

/-- The identity morphism of an affine formal scheme; continuous because its global-sections map
is the identity (`FormalSpectrum.globalSectionsMap_id`). -/
def Hom.id (X : AffineFormalSchemeCat.{u}) : Hom X X where
  toHom := 𝟙 X.toFormalScheme
  continuous' := by
    have h : FormalSpectrum.globalSectionsMap X.ring.ideal X.ring.ideal
        (FormalScheme.Hom.toLRSHom (𝟙 X.toFormalScheme)) = RingHom.id X.ring.carrier :=
      FormalSpectrum.globalSectionsMap_id X.ring.ideal
    rw [h, Ideal.comap_id]

/-- Composition of morphisms of affine formal schemes; continuous by
`FormalSpectrum.le_comap_globalSectionsMap_comp`. -/
def Hom.comp {X Y Z : AffineFormalSchemeCat.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toHom := f.toHom ≫ g.toHom
  continuous' :=
    FormalSpectrum.le_comap_globalSectionsMap_comp Z.ring.ideal Y.ring.ideal X.ring.ideal
      g.toHom.toLRSHom f.toHom.toLRSHom g.continuous' f.continuous'

instance : Category AffineFormalSchemeCat.{u} where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

@[simp]
theorem id_toHom (X : AffineFormalSchemeCat.{u}) :
    (𝟙 X : Hom X X).toHom = 𝟙 X.toFormalScheme :=
  rfl

@[simp]
theorem comp_toHom {X Y Z : AffineFormalSchemeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toHom = f.toHom ≫ g.toHom :=
  rfl

end AffineFormalSchemeCat

/-- The **formal spectrum, corestricted to the affine formal schemes**: on objects it is the
identity (an adic ring *is* the datum of an affine formal scheme), and on morphisms it sends a
continuous ring homomorphism `φ` to `Spf φ`, which is continuous on global sections by
`AdicRingCat.le_comap_globalSectionsMap_spfFunctor_map`. -/
def spfEquivFunctor : AdicRingCatFG.{u}ᵒᵖ ⥤ AffineFormalSchemeCat.{u} where
  obj X := ⟨(unop X).obj, (unop X).property⟩
  map {_ _} φ :=
    { toHom := AdicRingCat.spfFunctor.map (φ.unop.hom).op
      continuous' := AdicRingCat.le_comap_globalSectionsMap_spfFunctor_map φ.unop.hom }
  map_id X :=
    AffineFormalSchemeCat.Hom.ext (AdicRingCat.spfFunctor.map_id (op (unop X).obj))
  map_comp {_ _ _} φ ψ :=
    AffineFormalSchemeCat.Hom.ext
      (AdicRingCat.spfFunctor.map_comp (φ.unop.hom).op (ψ.unop.hom).op)

/-- **Full faithfulness of `Spf` onto the continuous morphisms** (EGA I, 10.4.6), as a
`Functor.FullyFaithful` datum. The underlying bijection is `AdicRingCat.spfHomEquiv`; this is the
packaging left as a follow-up in the scope note of `FormalSchemes/AdicRingCat.lean`. -/
def spfEquivFunctorFullyFaithful : spfEquivFunctor.{u}.FullyFaithful where
  preimage {X Y} f :=
    (ObjectProperty.homMk
      ((AdicRingCat.spfHomEquiv (unop Y).obj (unop X).obj (unop Y).property
        (unop X).property).symm ⟨f.toHom, f.continuous'⟩)).op
  map_preimage {X Y} f := by
    refine AffineFormalSchemeCat.Hom.ext ?_
    have h := congrArg Subtype.val
      ((AdicRingCat.spfHomEquiv (unop Y).obj (unop X).obj (unop Y).property
        (unop X).property).apply_symm_apply ⟨f.toHom, f.continuous'⟩)
    rw [AdicRingCat.spfHomEquiv_apply] at h
    exact h
  preimage_map {X Y} φ := by
    refine Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ ?_)
    change (AdicRingCat.spfHomEquiv (unop Y).obj (unop X).obj (unop Y).property
        (unop X).property).symm ⟨AdicRingCat.spfFunctor.map (φ.unop.hom).op,
          AdicRingCat.le_comap_globalSectionsMap_spfFunctor_map φ.unop.hom⟩ = φ.unop.hom
    rw [Equiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [AdicRingCat.spfHomEquiv_apply]

instance : spfEquivFunctor.{u}.Full := spfEquivFunctorFullyFaithful.full

instance : spfEquivFunctor.{u}.Faithful := spfEquivFunctorFullyFaithful.faithful

/-- `spfEquivFunctor` is the identity on objects, hence essentially surjective. -/
instance : spfEquivFunctor.{u}.EssSurj where
  mem_essImage Y := ⟨op ⟨Y.ring, Y.fg⟩, ⟨Iso.refl _⟩⟩

instance : spfEquivFunctor.{u}.IsEquivalence where

/-- **EGA I, 10.4.6.** The category of adic rings with finitely generated ideal of definition is
anti-equivalent, via the formal spectrum, to the category of affine formal schemes and continuous
morphisms. -/
def spfEquivalence : AdicRingCatFG.{u}ᵒᵖ ≌ AffineFormalSchemeCat.{u} :=
  spfEquivFunctor.asEquivalence

namespace AdicRingCat

/-- **`Spf` reflects isomorphisms.** If `φ : R ⟶ S` is a morphism of adic rings with finitely
generated ideals of definition and the induced morphism `Spf φ : Spf S ⟶ Spf R` admits a two-sided
inverse `ψ` which is again *continuous* on global sections, then `φ` is an isomorphism of adic
rings.

The continuity hypothesis on `ψ` cannot be dropped: `Spf` is not full onto arbitrary morphisms of
formal schemes (issue 156). -/
theorem isIso_of_isIso_spf {R S : AdicRingCat.{u}} (hR : R.ideal.FG) (hS : S.ideal.FG)
    (φ : R ⟶ S) (ψ : spfFunctor.obj (op R) ⟶ spfFunctor.obj (op S))
    (hψ : S.ideal ≤ R.ideal.comap
      (FormalSpectrum.globalSectionsMap S.ideal R.ideal ψ.toLRSHom))
    (h₁ : spfFunctor.map φ.op ≫ ψ = 𝟙 (spfFunctor.obj (op S)))
    (h₂ : ψ ≫ spfFunctor.map φ.op = 𝟙 (spfFunctor.obj (op R))) :
    IsIso φ := by
  set χ : S ⟶ R := (spfHomEquiv S R hS hR).symm ⟨ψ, hψ⟩
  have hmap : spfFunctor.map χ.op = ψ := by
    have h := congrArg Subtype.val ((spfHomEquiv S R hS hR).apply_symm_apply ⟨ψ, hψ⟩)
    rw [spfHomEquiv_apply] at h
    exact h
  refine ⟨χ, ?_, ?_⟩
  · refine Quiver.Hom.op_inj (spfFunctor.map_injective ?_)
    change spfFunctor.map (χ.op ≫ φ.op) = spfFunctor.map (𝟙 (op R))
    rw [spfFunctor.map_comp, hmap, h₂, spfFunctor.map_id]
  · refine Quiver.Hom.op_inj (spfFunctor.map_injective ?_)
    change spfFunctor.map (φ.op ≫ χ.op) = spfFunctor.map (𝟙 (op S))
    rw [spfFunctor.map_comp, hmap, h₁, spfFunctor.map_id]

end AdicRingCat

end
