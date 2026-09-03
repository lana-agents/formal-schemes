import FormalSchemes.BaseChange
import FormalSchemes.TopFiniteType

set_option linter.style.header false

/-!
# Topologically of finite type is a condition on the special fibre

Let `(R, I)` be an adic ring with `I` finitely generated and let `A` be an `R`-algebra which is
adically complete for `L = I·A`. This file proves that

> `A` is topologically of finite type over `(R, I)` **if and only if** the ordinary ring
> `A ⧸ L` is a finitely generated `R ⧸ I`-algebra.

That is `isTopologicallyFiniteType_iff_finiteType_residueRingHom`, and the map in question is the
tree's own `FormalSpectrum.residueRingHom` (`FormalSchemes.SpfMap`) at the structure map
`algebraMap R A` — the level-one thickening of the structural morphism `Spf L ⟶ Spf I`, i.e. the
morphism of special fibres.

## Why this is the useful shape

`IsTopologicallyFiniteType` (`FormalSchemes.TopFiniteType`) is stated as the existence of a
surjection from a restricted power series ring, and every consequence of it on this tree so far
has been proved by manufacturing such a surjection by hand — `awayEval` for the basic-open case
(`FormalSchemes.AwayTopFiniteType`) is four hundred lines of it. The characterisation above
replaces that with a statement about an *ordinary* finitely generated algebra, and ordinary
finite type has a developed theory that transfers wholesale. In particular it is a local property
of ring maps (`RingHom.finiteType_ofLocalizationSpanTarget`), which is what
`FormalSchemes.TopFiniteTypeAffineLocal` uses to prove that topological finite type is
affine-local — the statement three module docstrings on this tree recorded as missing
(`FormalSchemes.TopFiniteTypeHom`, `FormalSchemes.RelativeTopFiniteTypeTrans` and
`FormalSchemes.TwoChartBasicOpen`, all three amended alongside these two files).

The predicate and its API are root-level, where `FormalSchemes.TopFiniteType` declares the
predicate, and so are the declarations below. The split that used to leave
`IsTopologicallyFiniteType.map_eq` and `IsTopologicallyFiniteType.trans` at the root while sending
`IsTopologicallyFiniteType.awayCompletion` and `IsTopologicallyFiniteType.self` into
`AlgebraicGeometry` was historical rather than principled, and is gone.

## The two directions

Neither direction is formal, and they cost different hypotheses.

* **Forward** (`IsTopologicallyFiniteType.finiteType_residueRingHom`): reduce a presentation mod
  `L`. The content is that every restricted power series agrees with an honest polynomial modulo
  the ideal of definition — `AdicCompletion.exists_sub_algebraMap_mem_idealOfDefinition`, which is
  `AdicCompletion.ker_evalₐ` at level one read on elements (both `FormalSchemes.Completion`).
  **No completeness of `A` is used**, and neither is `L = I·A`; only `I ≤ L.comap (algebraMap R A)`,
  to have a map of special fibres at all.
* **Backward** (`IsTopologicallyFiniteType.of_finiteType_residueRingHom`): lift generators of
  `A ⧸ L` to `A` arbitrarily and evaluate (`RestrictedPowerSeries.evalAlgHom`,
  `FormalSchemes.BaseChange`). The resulting presentation is surjective mod `L` by construction,
  and surjective outright by successive approximation — Mathlib's
  `surjective_of_mk_map_comp_surjective`, isolated here as
  `surjective_of_quotient_surjective`. **This is where completeness of `A` is spent, and it is the
  only place.** It is not a technical convenience: a non-complete `A` is a quotient of no
  `R{X₁, …, Xₙ}` whatever, the same point `IsTopologicallyFiniteType.self`
  (`FormalSchemes.AwayTopFiniteType`) records.

The identity `(I·R{X}).map ψ = L` demanded by the predicate is, by contrast, free: it is `I·R{X}`
pushed forward along an `R`-algebra map, so it is `I·A`, and no surjectivity is needed for it.

`quotient_apply_algebraMap_eq_eval₂` is the one computation both directions share — a presentation
restricted to the polynomials, read modulo `L`, is evaluation over `R ⧸ I`. Both sides are ring
homomorphisms out of `R[X₁, …, Xₙ]`, so `MvPolynomial.ringHom_ext` reduces it to the constants and
the coordinates.

## What is *not* here

Nothing about `Spf`, opens, or morphisms: this file is pure commutative algebra and imports no
geometry beyond what `FormalSchemes.TopFiniteType` already needs. The geometric consequence —
affine-locality, and how far it goes towards conservativity of
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` — is
`FormalSchemes.TopFiniteTypeAffineLocal`.

## Main results

* `AlgebraicGeometry.quotient_apply_algebraMap_eq_eval₂`: a presentation, read on the special
  fibre.
* `IsTopologicallyFiniteType.finiteType_residueRingHom` and
  `IsTopologicallyFiniteType.of_finiteType_residueRingHom`: the two directions.
* `AlgebraicGeometry.surjective_of_quotient_surjective`: surjectivity of a presentation is a
  condition on the special fibre.
* `AlgebraicGeometry.isTopologicallyFiniteType_iff_finiteType_residueRingHom`: **the
  characterisation.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
* [The Stacks Project, Tag 0AL9](https://stacks.math.columbia.edu/tag/0AL9)
-/
noncomputable section

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}
variable {n : ℕ}

/-- **A presentation, read on the special fibre.** A tf-type presentation
`ψ : R{X₁, …, Xₙ} →ₐ[R] A` restricted to the polynomials `R[X₁, …, Xₙ] ⊆ R{X₁, …, Xₙ}` becomes,
modulo `L`, evaluation of a polynomial over `R ⧸ I` at the residues of the images
`ψ (Xᵢ)`, along the special fibre map `FormalSpectrum.residueRingHom`
(`FormalSchemes.SpfMap`).

Both sides are ring homomorphisms `R[X₁, …, Xₙ] → A ⧸ L`, so `MvPolynomial.ringHom_ext` reduces
the identity to the constants and the coordinates. It is the only computation the two directions
of `isTopologicallyFiniteType_iff_finiteType_residueRingHom` share, and each uses it once. -/
theorem quotient_apply_algebraMap_eq_eval₂ (hIL : I ≤ L.comap (algebraMap R A))
    (ψ : RestrictedPowerSeries R I n →ₐ[R] A) (p : MvPolynomial (Fin n) R) :
    Ideal.Quotient.mk L
        (ψ (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n) p)) =
      MvPolynomial.eval₂ (FormalSpectrum.residueRingHom I L (algebraMap R A) hIL)
        (fun i => Ideal.Quotient.mk L
          (ψ (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)
            (MvPolynomial.X i))))
        (MvPolynomial.map (Ideal.Quotient.mk I) p) := by
  have key : (Ideal.Quotient.mk L).comp (ψ.toRingHom.comp
        (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n))) =
      (MvPolynomial.eval₂Hom (FormalSpectrum.residueRingHom I L (algebraMap R A) hIL)
        (fun i => Ideal.Quotient.mk L
          (ψ (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)
            (MvPolynomial.X i))))).comp
        (MvPolynomial.map (Ideal.Quotient.mk I)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      rw [show FormalSpectrum.residueRingHom I L (algebraMap R A) hIL (Ideal.Quotient.mk I r) =
          Ideal.Quotient.mk L (algebraMap R A r) from Ideal.quotientMap_mk,
        ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun key p

/-- **The easy direction: a tf-type algebra has finite-type special fibre.** A presentation
`R{X₁, …, Xₙ} ↠ A` carrying the ideal of definition onto `L` descends to a surjection
`(R ⧸ I)[X₁, …, Xₙ] ↠ A ⧸ L`, because every restricted power series agrees with a polynomial
modulo the ideal of definition
(`AdicCompletion.exists_sub_algebraMap_mem_idealOfDefinition`) and the ideal of definition lands
in `L`.

Only the surjectivity of the presentation and the identity `(I·R{X}).map ψ = L` are used; the
adic topology of `A` plays no role, which is why this direction needs no completeness
hypothesis. -/
theorem _root_.IsTopologicallyFiniteType.finiteType_residueRingHom (hI : I.FG)
    (hIL : I ≤ L.comap (algebraMap R A)) (hA : IsTopologicallyFiniteType R I A L) :
    (FormalSpectrum.residueRingHom I L (algebraMap R A) hIL).FiniteType := by
  obtain ⟨n, ψ, hψ, hL⟩ := hA
  letI : Algebra (R ⧸ I) (A ⧸ L) :=
    (FormalSpectrum.residueRingHom I L (algebraMap R A) hIL).toAlgebra
  refine Algebra.FiniteType.of_surjective
    (MvPolynomial.aeval (R := R ⧸ I) (S₁ := A ⧸ L)
      (fun i => Ideal.Quotient.mk L
        (ψ (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)
          (MvPolynomial.X i))))) ?_
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := hψ a
  obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_algebraMap_mem_idealOfDefinition
    (I.map (algebraMap R (MvPolynomial (Fin n) R))) (hI.map _) x
  refine ⟨MvPolynomial.map (Ideal.Quotient.mk I) p, ?_⟩
  have hstep : Ideal.Quotient.mk L (ψ x) =
      Ideal.Quotient.mk L
        (ψ (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n) p)) := by
    rw [Ideal.Quotient.eq, ← map_sub]
    have hmem : ψ.toRingHom (x - algebraMap (MvPolynomial (Fin n) R)
        (RestrictedPowerSeries R I n) p) ∈
        (RestrictedPowerSeries.idealOfDefinition R I n).map ψ.toRingHom :=
      Ideal.mem_map_of_mem _ hp
    rwa [hL] at hmem
  rw [hstep, quotient_apply_algebraMap_eq_eval₂ hIL ψ p, MvPolynomial.aeval_def]
  rfl

/-- **Surjectivity of a presentation is a condition on the special fibre.** For a complete `A`,
a presentation surjective modulo `L` is surjective, by successive approximation
(`surjective_of_mk_map_comp_surjective`).

This is where completeness of `A` enters, and it is the only place. -/
theorem surjective_of_quotient_surjective (hI : I.FG) [IsAdicComplete L A]
    {ψ : RestrictedPowerSeries R I n →ₐ[R] A}
    (hmapL : (RestrictedPowerSeries.idealOfDefinition R I n).map ψ.toRingHom = L)
    (hs : Function.Surjective ((Ideal.Quotient.mk L).comp ψ.toRingHom)) :
    Function.Surjective ψ := by
  haveI : IsPrecomplete (RestrictedPowerSeries.idealOfDefinition R I n)
      (RestrictedPowerSeries R I n) :=
    (RestrictedPowerSeries.isAdicRing R I n hI).toIsAdicComplete.toIsPrecomplete
  subst hmapL
  exact surjective_of_mk_map_comp_surjective
    (I := RestrictedPowerSeries.idealOfDefinition R I n) ψ.toRingHom hs

/-- **The substantial direction: a finite-type special fibre lifts.** If `A` is `L`-adically
complete with `L = I·A` and `A ⧸ L` is a finitely generated `R ⧸ I`-algebra, then `A` is
topologically of finite type over `(R, I)`.

Generators of `A ⧸ L` are lifted to `A` arbitrarily and evaluated
(`RestrictedPowerSeries.evalAlgHom`, `FormalSchemes.BaseChange`); the resulting presentation is
surjective modulo `L` by construction, hence surjective by
`surjective_of_quotient_surjective`. That the ideal of definition maps onto `L` is automatic and
uses none of this: it is `I·R{X}` pushed along an `R`-algebra map to `I·A`.

Completeness of `A` is not a technical convenience — a non-complete `A` is a quotient of no
`R{X₁, …, Xₙ}` at all (compare `IsTopologicallyFiniteType.self`,
`FormalSchemes.AwayTopFiniteType`). -/
theorem _root_.IsTopologicallyFiniteType.of_finiteType_residueRingHom (hI : I.FG)
    [IsAdicComplete L A] (h : I.map (algebraMap R A) = L)
    (hIL : I ≤ L.comap (algebraMap R A))
    (hft : (FormalSpectrum.residueRingHom I L (algebraMap R A) hIL).FiniteType) :
    IsTopologicallyFiniteType R I A L := by
  letI : Algebra (R ⧸ I) (A ⧸ L) :=
    (FormalSpectrum.residueRingHom I L (algebraMap R A) hIL).toAlgebra
  obtain ⟨m, Φ, hΦ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  choose s hs using fun i : Fin m => Ideal.Quotient.mk_surjective (Φ (MvPolynomial.X i))
  set ψ := RestrictedPowerSeries.evalAlgHom (R := R) (I := I) L h.le s with hψdef
  have hmapL : (RestrictedPowerSeries.idealOfDefinition R I m).map ψ.toRingHom = L := by
    have hc : ψ.toRingHom.comp (algebraMap R (RestrictedPowerSeries R I m)) =
        algebraMap R A := ψ.comp_algebraMap
    rw [RestrictedPowerSeries.idealOfDefinition_eq_map, Ideal.map_map, hc]
    exact h
  have hcoord : ∀ i : Fin m, ψ (algebraMap (MvPolynomial (Fin m) R)
      (RestrictedPowerSeries R I m) (MvPolynomial.X i)) = s i := by
    intro i
    change RestrictedPowerSeries.evalHom R I m L h.le s
      (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin m) R)))
        (MvPolynomial (Fin m) R) (MvPolynomial.X i)) = s i
    rw [RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X]
  have hg : (fun i => Ideal.Quotient.mk L (ψ (algebraMap (MvPolynomial (Fin m) R)
        (RestrictedPowerSeries R I m) (MvPolynomial.X i)))) =
      fun i => Φ (MvPolynomial.X i) := funext fun i => by rw [hcoord i, hs i]
  have hquot : Function.Surjective ((Ideal.Quotient.mk L).comp ψ.toRingHom) := by
    intro ybar
    obtain ⟨q, rfl⟩ := hΦ ybar
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q
    refine ⟨algebraMap (MvPolynomial (Fin m) R) (RestrictedPowerSeries R I m) p, ?_⟩
    change Ideal.Quotient.mk L (ψ (algebraMap (MvPolynomial (Fin m) R)
      (RestrictedPowerSeries R I m) p)) = _
    rw [quotient_apply_algebraMap_eq_eval₂ hIL ψ p, hg]
    conv_rhs => rw [MvPolynomial.aeval_unique Φ]
    rfl
  exact ⟨m, ψ, surjective_of_quotient_surjective hI hmapL hquot, hmapL⟩

/-- **Topological finite type is a condition on the special fibre.** For an `L`-adically complete
`A` whose ideal of definition is the extension `I·A`, being topologically of finite type over
`(R, I)` is exactly finite generation of the ordinary `R ⧸ I`-algebra `A ⧸ L`.

This is the statement that makes topological finite type *affine-local*: the right-hand side is
a property of an ordinary ring map, for which locality is
`RingHom.finiteType_ofLocalizationSpanTarget`. -/
theorem isTopologicallyFiniteType_iff_finiteType_residueRingHom (hI : I.FG) [IsAdicComplete L A]
    (h : I.map (algebraMap R A) = L) (hIL : I ≤ L.comap (algebraMap R A)) :
    IsTopologicallyFiniteType R I A L ↔
      (FormalSpectrum.residueRingHom I L (algebraMap R A) hIL).FiniteType :=
  ⟨fun hA => IsTopologicallyFiniteType.finiteType_residueRingHom hI hIL hA,
    fun hft => IsTopologicallyFiniteType.of_finiteType_residueRingHom hI h hIL hft⟩

end AlgebraicGeometry
