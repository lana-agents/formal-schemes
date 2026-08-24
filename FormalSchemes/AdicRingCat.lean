import FormalSchemes.SpfFunctorial
import FormalSchemes.SpfGamma
import FormalSchemes.FormalScheme

set_option linter.style.header false

/-!
# The category of adic rings and the functor `Spf`

This file packages the *formal spectrum* construction as a contravariant functor, mirroring
Mathlib's `AlgebraicGeometry.Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme` for ordinary schemes. It is
the categorical form of the second goal of the universal property of `Spf` (EGA I, 10.4.6): the
correspondence between morphisms into a formal spectrum and continuous ring homomorphisms.

## Main definitions

* `AdicRingCat`: the category whose objects are adic rings `(R, I)` (a commutative ring `R` with
  a linear topology, complete and Hausdorff for the `I`-adic topology of a distinguished ideal of
  definition `I`) and whose morphisms are the **continuous ring homomorphisms** — ring
  homomorphisms `φ : R →+* S` carrying the ideal of definition of the source into that of the
  target (`I ≤ J.comap φ`, equivalently `I·S ≤ J`). This is the class of morphisms EGA I, §10.4
  works with.
* `AdicRingCat.spfFunctor : AdicRingCatᵒᵖ ⥤ FormalScheme`: the (contravariant) **formal
  spectrum functor** `R ↦ Spf R`, sending a continuous ring homomorphism `φ : R →+* S` to the
  induced morphism of formal schemes `Spf S ⟶ Spf R` (`FormalSpectrum.locallyRingedSpaceMap`).
  Functoriality is the merged `locallyRingedSpaceMap_id` / `locallyRingedSpaceMap_comp`
  (EGA I, 10.2).

## Main results

* `AdicRingCat.instFaithfulSpfFunctor`: `spfFunctor` is **faithful** — a continuous ring
  homomorphism is recovered from the induced morphism of formal schemes by taking global sections
  (`FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`, the `Γ ∘ Spf = id` half).

## Scope: why this functor is not *fully* faithful

For ordinary schemes `Spec` is fully faithful onto *all* scheme morphisms. The formal-spectrum
functor is **not** full onto arbitrary morphisms of formal schemes: an abstract morphism of
locally ringed spaces `Spf S ⟶ Spf R` need not be *continuous* (its global-sections map need not
carry the ideal of definition into that of the target), because the structure sheaves here carry
no ambient topology. The precise bijection — the full EGA I, 10.4.6 statement — is
`FormalSpectrum.spfGammaEquiv`, stated over the continuity-restricted subtypes on *both* sides;
`AdicRingCat.spfHomEquiv` (`FormalSchemes.SpfFullyFaithful`) is that bijection transported to this
file's `spfFunctor`. That bijection *is* packaged as a `CategoryTheory.Functor.FullyFaithful`
datum, by `spfEquivFunctorFullyFaithful`, and as the equivalence `spfEquivalence`
(both `FormalSchemes.SpfEquivalence`) — but **not** over a subcategory of `FormalScheme` cut out by
the continuity property, and that is not an omission: continuity of `f : Spf S ⟶ Spf R` reads
`I ≤ J.comap (globalSectionsMap I J f)`, which mentions the ideals of definition of *both* rings,
data that an object of `FormalScheme` does not carry. It is stated instead over `AdicRingCatFG`,
whose objects are adic rings with a finitely generated ideal of definition (the finite generation
coming from `spfHomEquiv`), and `AffineFormalSchemeCat`, whose morphisms carry the continuity
witness as a field. This file records the functor and its faithfulness.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2, §10.4.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

/-- An **adic ring** `(R, I)`: a commutative ring `R` carrying a linear topology that is complete
and Hausdorff for the `I`-adic topology of a distinguished ideal of definition `I`. These are the
objects out of whose formal spectra formal schemes are glued. -/
structure AdicRingCat where
  /-- The underlying commutative ring. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [topologicalSpace : TopologicalSpace carrier]
  /-- The distinguished ideal of definition. -/
  ideal : Ideal carrier
  [isAdicRing : IsAdicRing ideal]

namespace AdicRingCat

attribute [instance] commRing topologicalSpace isAdicRing

instance : CoeSort AdicRingCat (Type u) where
  coe R := R.carrier

/-- Build an adic ring object from a ring, a topology, and an ideal of definition. -/
abbrev of (R : Type u) [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I] :
    AdicRingCat where
  carrier := R
  ideal := I

/-- A **morphism of adic rings** is a continuous ring homomorphism: a ring homomorphism carrying
the ideal of definition of the source into that of the target. -/
@[ext]
structure Hom (R S : AdicRingCat.{u}) where
  /-- The underlying ring homomorphism. -/
  toRingHom : R.carrier →+* S.carrier
  /-- Continuity: the ideal of definition of the source lands in that of the target. -/
  continuous' : R.ideal ≤ S.ideal.comap toRingHom

/-- The identity continuous ring homomorphism. -/
def Hom.id (R : AdicRingCat.{u}) : Hom R R where
  toRingHom := RingHom.id R.carrier
  continuous' := by rw [Ideal.comap_id]

/-- Composition of continuous ring homomorphisms. -/
def Hom.comp {R S T : AdicRingCat.{u}} (f : Hom R S) (g : Hom S T) : Hom R T where
  toRingHom := g.toRingHom.comp f.toRingHom
  continuous' := by
    rw [← Ideal.comap_comap]
    exact le_trans f.continuous' (Ideal.comap_mono g.continuous')

instance : Category AdicRingCat.{u} where
  Hom R S := Hom R S
  id R := Hom.id R
  comp f g := Hom.comp f g

@[simp]
theorem id_toRingHom (R : AdicRingCat.{u}) :
    (𝟙 R : Hom R R).toRingHom = RingHom.id R.carrier :=
  rfl

@[simp]
theorem comp_toRingHom {R S T : AdicRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).toRingHom = g.toRingHom.comp f.toRingHom :=
  rfl

/-!
### The formal spectrum functor
-/

/-- The **formal spectrum functor** `Spf : AdicRingCatᵒᵖ ⥤ FormalScheme` (EGA I, 10.2): an adic
ring `R` with ideal of definition `I` is sent to the affine formal scheme `Spf R`, and a
continuous ring homomorphism `φ : R →+* S` to the induced morphism `Spf S ⟶ Spf R`. It is the
formal-geometry analogue of `AlgebraicGeometry.Scheme.Spec`. -/
noncomputable def spfFunctor : AdicRingCat.{u}ᵒᵖ ⥤ FormalScheme.{u} where
  obj R := FormalScheme.Spf (unop R).ideal
  map {R S} f :=
    FormalScheme.Hom.mk
      (FormalSpectrum.locallyRingedSpaceMap (unop S).ideal (unop R).ideal
        f.unop.toRingHom f.unop.continuous')
  map_id R := by
    apply FormalScheme.Hom.ext'
    exact FormalSpectrum.locallyRingedSpaceMap_id (unop R).ideal
  map_comp {R S T} f g := by
    apply FormalScheme.Hom.ext'
    exact FormalSpectrum.locallyRingedSpaceMap_comp (unop T).ideal (unop S).ideal (unop R).ideal
      g.unop.toRingHom f.unop.toRingHom g.unop.continuous' f.unop.continuous' _

/-- `spfFunctor` is **faithful**: a continuous ring homomorphism is recovered from the induced
morphism of formal schemes by passing to global sections, i.e. `Γ ∘ Spf = id`
(`FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`). This is the faithfulness half of the
universal property of `Spf` (EGA I, 10.4.6). -/
instance : spfFunctor.{u}.Faithful where
  map_injective {R S} {f g} h := by
    refine Quiver.Hom.unop_inj (AdicRingCat.Hom.ext ?_)
    have hlrs :
        FormalSpectrum.locallyRingedSpaceMap (unop S).ideal (unop R).ideal
            f.unop.toRingHom f.unop.continuous' =
          FormalSpectrum.locallyRingedSpaceMap (unop S).ideal (unop R).ideal
            g.unop.toRingHom g.unop.continuous' :=
      congrArg FormalScheme.Hom.toLRSHom h
    calc
      f.unop.toRingHom
          = FormalSpectrum.globalSectionsMap (unop S).ideal (unop R).ideal
              (FormalSpectrum.locallyRingedSpaceMap (unop S).ideal (unop R).ideal
                f.unop.toRingHom f.unop.continuous') :=
            (FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap _ _ _ _).symm
      _ = FormalSpectrum.globalSectionsMap (unop S).ideal (unop R).ideal
              (FormalSpectrum.locallyRingedSpaceMap (unop S).ideal (unop R).ideal
                g.unop.toRingHom g.unop.continuous') := by rw [hlrs]
      _ = g.unop.toRingHom :=
            FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap _ _ _ _

end AdicRingCat
