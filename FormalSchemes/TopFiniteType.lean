import FormalSchemes.AdicQuotient
import FormalSchemes.SpfMap

set_option linter.style.header false

/-!
# Algebras topologically of finite type

An adic `R`-algebra is **topologically of finite type** (tf-type) if it is a quotient of a
restricted power series ring `R{X₁, …, Xₙ}` carrying the quotient filtration (Bosch,
*Lectures on Formal and Rigid Geometry*, §7.3; EGA I, 10.13). These are the coordinate rings
of the affine formal schemes in which the Tate-curve constructions live.

This file provides the affine-algebra layer:

* `IsTopologicallyFiniteType R I A L`: `A` is a quotient of some `R{X₁, …, Xₙ}` by an
  `R`-algebra surjection carrying the ideal of definition onto `L`;
* `IsTopologicallyFiniteType.isAdicRing`: if moreover the kernel of the presentation is
  adically closed (automatic in the noetherian setting; a hypothesis here), `A` is a complete
  adic ring with ideal of definition `L`, so `Spf A` is an affine formal scheme;
* `IsTopologicallyFiniteType.structMap`: the structural morphism `Spf A ⟶ Spf R` of locally
  ringed spaces.

Closure of tf-type algebras under quotients and base change, and the global notion (formal
schemes admitting tf-type affine covers over `Spf R`), are left to follow-up work together
with the gluing machinery.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open Ideal

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (A : Type u) [CommRing A] [Algebra R A] (L : Ideal A)

/-- An `R`-algebra `A` with distinguished ideal `L` is **topologically of finite type** over
`(R, I)` if there is a surjective `R`-algebra homomorphism from some restricted power series
ring `R{X₁, …, Xₙ}` onto `A` carrying the ideal of definition onto `L`. -/
def IsTopologicallyFiniteType : Prop :=
  ∃ (n : ℕ) (ψ : RestrictedPowerSeries R I n →ₐ[R] A),
    Function.Surjective ψ ∧
      (RestrictedPowerSeries.idealOfDefinition R I n).map ψ.toRingHom = L

namespace IsTopologicallyFiniteType

variable {R I A L}

/-- A presentation of a tf-type algebra exhibits `I·A = L`. -/
theorem map_eq_of_presentation {n : ℕ} {ψ : RestrictedPowerSeries R I n →ₐ[R] A}
    (hL : (RestrictedPowerSeries.idealOfDefinition R I n).map ψ.toRingHom = L) :
    I.map (algebraMap R A) = L := by
  rw [← hL, RestrictedPowerSeries.idealOfDefinition_eq_map, Ideal.map_map]
  congr 1
  exact (ψ.comp_algebraMap).symm

/-- A tf-type algebra whose presentation has adically closed kernel is a complete adic ring
with ideal of definition `L`: quotients of complete adic rings by closed ideals are complete
adic rings. In the noetherian setting the closedness hypothesis is automatic (Artin–Rees);
tracking it explicitly keeps the statement general. -/
theorem isAdicRing (hI : I.FG) {n : ℕ} {ψ : RestrictedPowerSeries R I n →ₐ[R] A}
    (hs : Function.Surjective ψ)
    (hL : (RestrictedPowerSeries.idealOfDefinition R I n).map ψ.toRingHom = L)
    (hker : ψ.toRingHom.AdicKerClosed (RestrictedPowerSeries.idealOfDefinition R I n)) :
    letI : TopologicalSpace A := L.adicTopology
    IsAdicRing L := by
  subst hL
  letI : Algebra (RestrictedPowerSeries R I n) A := ψ.toRingHom.toAlgebra
  haveI : IsAdicComplete (RestrictedPowerSeries.idealOfDefinition R I n)
      (RestrictedPowerSeries R I n) :=
    (RestrictedPowerSeries.isAdicRing R I n hI).toIsAdicComplete
  exact IsAdicRing.of_surjective_of_kerClosed
    (RestrictedPowerSeries.idealOfDefinition R I n) hs hker

/-- The structural morphism `Spf A ⟶ Spf R` of a tf-type adic `R`-algebra, as a morphism of
locally ringed spaces. -/
def structMap [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace A] [IsAdicRing L]
    (hIL : I.map (algebraMap R A) = L) :
    FormalSpectrum.locallyRingedSpaceObj L ⟶ FormalSpectrum.locallyRingedSpaceObj I :=
  FormalSpectrum.locallyRingedSpaceMap I L (algebraMap R A)
    (Ideal.map_le_iff_le_comap.mp hIL.le)

end IsTopologicallyFiniteType
