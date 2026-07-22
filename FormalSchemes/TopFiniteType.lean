import FormalSchemes.AdicQuotient
import FormalSchemes.RestrictedPowerSeriesNoetherian
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
* `IsTopologicallyFiniteType.isAdicRing_of_noetherian`: the same conclusion with **no**
  closedness hypothesis over a Noetherian base `R` (Krull intersection,
  `RingHom.adicKerClosed_of_noetherian`). This is the case Bosch works in: over a Noetherian
  base the restricted power series rings `R{X₁, …, Xₙ}` are Noetherian
  (`RestrictedPowerSeries.instIsNoetherianRing`, issue 98), so every tf-type algebra is
  automatically a complete adic ring;
* `IsTopologicallyFiniteType.structMap`: the structural morphism `Spf A ⟶ Spf R` of locally
  ringed spaces.

## Relation to issue 62 (`FormalSchemes.AdicMorphism`)

`FormalSchemes.AdicMorphism` develops the *morphism-level* theory — adic morphisms
(`IsAdicHom`, EGA I 10.12) and closed formal subschemes as adic quotients by an adically closed
ideal (`IsAdicHom.of_map`). This file is the complementary *object-level* layer: it fixes the
affine `R`-algebras (quotients of `R{X}`) whose formal spectra are the concrete tf-type formal
schemes over `Spf R` that the Tate construction consumes. The structural morphism `structMap`
built here is an adic morphism in the sense of `AdicMorphism` (its ideal of definition `L` is
`I·A` by `map_eq`), tying the two viewpoints together.

Closure of tf-type algebras under base change, and the global notion (formal schemes admitting
tf-type affine covers over `Spf R`), are left to follow-up work together with the gluing
machinery.

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

/-- A tf-type algebra over a **Noetherian** base `R` is a complete adic ring with ideal of
definition `L`, with no closedness hypothesis: over a Noetherian base the presenting ring
`R{X₁, …, Xₙ}` is Noetherian (`RestrictedPowerSeries.instIsNoetherianRing`, issue 98), so the
kernel of any presentation is automatically adically closed (Krull intersection,
`RingHom.adicKerClosed_of_noetherian`). This is the ambient case of the theory. -/
theorem isAdicRing_of_noetherian (hI : I.FG) {n : ℕ}
    [IsNoetherianRing R]
    {ψ : RestrictedPowerSeries R I n →ₐ[R] A} (hs : Function.Surjective ψ)
    (hL : (RestrictedPowerSeries.idealOfDefinition R I n).map ψ.toRingHom = L) :
    letI : TopologicalSpace A := L.adicTopology
    IsAdicRing L := by
  letI : Algebra (RestrictedPowerSeries R I n) A := ψ.toRingHom.toAlgebra
  haveI : IsAdicComplete (RestrictedPowerSeries.idealOfDefinition R I n)
      (RestrictedPowerSeries R I n) :=
    (RestrictedPowerSeries.isAdicRing R I n hI).toIsAdicComplete
  exact isAdicRing hI hs hL
    (RingHom.adicKerClosed_of_noetherian (RestrictedPowerSeries.idealOfDefinition R I n) hs)

/-- Topologically-of-finite-type algebras are closed under further quotients: a surjective
`R`-algebra image of a tf-type algebra, with the image filtration, is tf-type. -/
theorem of_surjective {A' : Type u} [CommRing A'] [Algebra R A'] {L' : Ideal A'}
    (h : IsTopologicallyFiniteType R I A L) (π : A →ₐ[R] A')
    (hπ : Function.Surjective π) (hL' : L.map π.toRingHom = L') :
    IsTopologicallyFiniteType R I A' L' := by
  obtain ⟨n, ψ, hs, hL⟩ := h
  refine ⟨n, π.comp ψ, hπ.comp hs, ?_⟩
  have hcomp : (π.comp ψ).toRingHom = π.toRingHom.comp ψ.toRingHom := rfl
  rw [hcomp, ← Ideal.map_map, hL, hL']

/-- A tf-type algebra is, in particular, an algebra over the base with `L` generated by the
ideal of definition: `I·A = L` (restatement of `map_eq_of_presentation` from the predicate). -/
theorem map_eq (h : IsTopologicallyFiniteType R I A L) : I.map (algebraMap R A) = L := by
  obtain ⟨n, ψ, _, hL⟩ := h
  exact map_eq_of_presentation hL

/-- The structural morphism `Spf A ⟶ Spf R` of a tf-type adic `R`-algebra, as a morphism of
locally ringed spaces. -/
def structMap [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace A] [IsAdicRing L]
    (hIL : I.map (algebraMap R A) = L) :
    FormalSpectrum.locallyRingedSpaceObj L ⟶ FormalSpectrum.locallyRingedSpaceObj I :=
  FormalSpectrum.locallyRingedSpaceMap I L (algebraMap R A)
    (Ideal.map_le_iff_le_comap.mp hIL.le)

end IsTopologicallyFiniteType
