import FormalSchemes.AwayTopFiniteType

set_option linter.style.header false

/-!
# Transitivity of `IsTopologicallyFiniteType`, and arity-additivity of the formal polydisc

A tf-type algebra over a tf-type algebra is tf-type (Bosch, *Lectures on Formal and Rigid
Geometry*, §7.3; EGA I, 10.13). Unfolding the definition, the statement is a chain

```
R{X₁, …, X_{n+m}}  ↠  R{X₁, …, Xₙ}{Y₁, …, Y_m}  ↠  A{Y₁, …, Y_m}  ↠  B
```

whose last arrow is a presentation of `B` over `A` and whose first two were the missing
ingredients: nothing on this tree mentioned the iterated polydisc, and nothing related the
`(n+m)`-variable polydisc to it.

## What is built here, and why in this shape

The two missing arrows are built **as a single evaluation homomorphism**, which is what makes the
file short. Given a presentation `ψ : R{X₁, …, Xₙ} ↠ A` carrying the ideal of definition onto `L`,
`presentationHom` is the evaluation of `R{X₁, …, X_{n+m}}` at the `n + m` elements

* `ψ(Xᵢ)` pushed into `A{Y₁, …, Y_m}`, for `i < n`;
* the coordinates `Y_j`, for the remaining `m`;

so it *is* the composite of the first two arrows, with the intermediate ring never named. Its
surjectivity is `surjective_of_mk_map_comp_surjective` — a continuous map into a
complete adic ring which is surjective modulo the ideal of definition is surjective — and modulo
the ideal of definition every element is represented by a polynomial in `A[Y₁, …, Y_m]`, which lies
in the range because the range is a subring containing the image of `A` (here `ψ`'s surjectivity
enters, through `presentationHom_castAddHom`) and every `Y_j`.

Arity-additivity is then the special case `A = R{X₁, …, Xₙ}`, `ψ = id`
(`arityAddHom`, `arityAddHom_surjective`), and transitivity is `restrictedPowerSeries` — the
polydisc over a tf-type algebra is tf-type — followed by `IsTopologicallyFiniteType.of_surjective`.

## Main definitions

* `RestrictedPowerSeries.castAddHom`: the inclusion `R{X₁, …, Xₙ} →ₐ[R] R{X₁, …, X_{n+m}}` of the
  first `n` coordinates.
* `RestrictedPowerSeries.presentationHom`: the map `R{X₁, …, X_{n+m}} →ₐ[R] A{Y₁, …, Y_m}` above.
* `RestrictedPowerSeries.arityAddHom`: its special case
  `R{X₁, …, X_{n+m}} →ₐ[R] R{X₁, …, Xₙ}{Y₁, …, Y_m}`.

## Main results

* `RestrictedPowerSeries.presentationHom_surjective`.
* `RestrictedPowerSeries.arityAddHom_surjective` and
  `RestrictedPowerSeries.map_idealOfDefinition_arityAddHom`: **arity-additivity of the formal
  polydisc**, `R{X₁, …, X_{n+m}} ↠ R{X₁, …, Xₙ}{Y₁, …, Y_m}`.
* `IsTopologicallyFiniteType.restrictedPowerSeries`: the polydisc over a tf-type algebra is
  tf-type.
* `IsTopologicallyFiniteType.trans`: **transitivity**.

## What wants transitivity, and what turns out not to

Nothing on this tree consumes `trans` yet, and it is worth recording why rather than inventing a
consumer. The natural candidate is issue 807's
`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion` (a basic-open chart of a tf-type
formal affine is tf-type): iterating it looks like a job for transitivity, but it is already stated
over the base `(R, I)` rather than over `(A, L)`, so it iterates on its own. What transitivity does
give is a second proof of it — `trans` applied to `awayCompletion_base` at `(A, L)` — but only
under the extra hypothesis `[IsAdicComplete L A]`, which `awayCompletion_base` needs and
`awayCompletion` does not. That is strictly weaker, so it is not landed here and 807's direct proof
stands.

The declaration that will want `trans` is the composition law for the *morphism-level* finite-type
notion (`FormalSchemes.RelativeTopFiniteType`), which does not exist yet; it is issue 62's own
remaining item and is deliberately out of scope for this file.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open Ideal AlgebraicGeometry

universe u

namespace RestrictedPowerSeries

variable {R : Type u} [CommRing R] {I : Ideal R} {n : ℕ}

/-! ### Evaluation at a coordinate -/

theorem evalHom_rpsCoord {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S]
    [IsAdicComplete L S] (hIL : I.map (algebraMap R S) ≤ L) (s : Fin n → S) (i : Fin n) :
    evalHom R I n L hIL s (rpsCoord R I n i) = s i := by
  rw [rpsCoord, evalHom_of, MvPolynomial.aeval_X]

theorem evalAlgHom_rpsCoord {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S]
    [IsAdicComplete L S] (hIL : I.map (algebraMap R S) ≤ L) (s : Fin n → S) (i : Fin n) :
    evalAlgHom L hIL s (rpsCoord R I n i) = s i :=
  evalHom_rpsCoord L hIL s i

/-! ### The ideal of definition of a polydisc over an intermediate base -/

/-- **The ideal of definition of a polydisc in a tower.** If the distinguished ideal `K` of an
`R`-algebra `S` is the extension of `I`, then the ideal of definition of `S{Y₁, …, Y_m}` is the
extension of `I` as well. -/
theorem map_algebraMap_eq_idealOfDefinition {S : Type u} [CommRing S] [Algebra R S]
    (K : Ideal S) (m : ℕ) (hK : K = I.map (algebraMap R S)) :
    I.map (algebraMap R (RestrictedPowerSeries S K m)) = idealOfDefinition S K m := by
  rw [idealOfDefinition_eq_map S K m,
    IsScalarTower.algebraMap_eq R S (RestrictedPowerSeries S K m), ← Ideal.map_map, ← hK]

section Presentation

variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A} (m : ℕ)
variable (hI : I.FG) (ψ : RestrictedPowerSeries R I n →ₐ[R] A)
variable (hL : (idealOfDefinition R I n).map ψ.toRingHom = L)

include hI hL in
/-- The distinguished ideal of a tf-type algebra is finitely generated. -/
theorem fg_of_presentation : L.FG := hL ▸ ((hI.map _).map _).map _

include hI hL in
theorem isAdicComplete_of_presentation :
    IsAdicComplete (idealOfDefinition A L m) (RestrictedPowerSeries A L m) :=
  (RestrictedPowerSeries.isAdicRing A L m (fg_of_presentation hI ψ hL)).toIsAdicComplete

omit hI in
include hL in
theorem map_algebraMap_eq_of_presentation :
    I.map (algebraMap R (RestrictedPowerSeries A L m)) = idealOfDefinition A L m :=
  map_algebraMap_eq_idealOfDefinition L m
    (IsTopologicallyFiniteType.map_eq_of_presentation hL).symm

/-! ### The presentation homomorphism -/

/-- The `n + m` evaluation targets: the images under `ψ` of the first `n` coordinates, pushed into
`A{Y₁, …, Y_m}`, followed by the `m` coordinates `Y_j`. -/
def presentationCoords : Fin (n + m) → RestrictedPowerSeries A L m :=
  Fin.addCases
    (fun i => algebraMap A (RestrictedPowerSeries A L m) (ψ (rpsCoord R I n i)))
    (fun j => rpsCoord A L m j)

@[simp]
theorem presentationCoords_castAdd (i : Fin n) :
    presentationCoords m ψ (Fin.castAdd m i) =
      algebraMap A (RestrictedPowerSeries A L m) (ψ (rpsCoord R I n i)) :=
  Fin.addCases_left i

@[simp]
theorem presentationCoords_natAdd (j : Fin m) :
    presentationCoords m ψ (Fin.natAdd n j) = rpsCoord A L m j :=
  Fin.addCases_right j

include hI hL in
/-- **The presentation homomorphism** `R{X₁, …, X_{n+m}} →ₐ[R] A{Y₁, …, Y_m}` attached to a
presentation `ψ` of `A`: evaluation at `ψ(X₁), …, ψ(Xₙ), Y₁, …, Y_m`. It is the composite of
arity-additivity with the base change of the polydisc along `ψ`, with the intermediate ring
`R{X₁, …, Xₙ}{Y₁, …, Y_m}` never named. -/
def presentationHom : RestrictedPowerSeries R I (n + m) →ₐ[R] RestrictedPowerSeries A L m :=
  haveI := isAdicComplete_of_presentation m hI ψ hL
  evalAlgHom (idealOfDefinition A L m) (map_algebraMap_eq_of_presentation m ψ hL).le
    (presentationCoords m ψ)

include hI hL in
theorem presentationHom_rpsCoord (k : Fin (n + m)) :
    presentationHom m hI ψ hL (rpsCoord R I (n + m) k) = presentationCoords m ψ k :=
  haveI := isAdicComplete_of_presentation m hI ψ hL
  evalAlgHom_rpsCoord _ _ _ k

include hI hL in
theorem presentationHom_mem_pow (k : ℕ) {x : RestrictedPowerSeries R I (n + m)}
    (hx : x ∈ (idealOfDefinition R I (n + m)) ^ k) :
    presentationHom m hI ψ hL x ∈ (idealOfDefinition A L m) ^ k :=
  haveI := isAdicComplete_of_presentation m hI ψ hL
  evalHom_mem_pow (idealOfDefinition A L m)
    (map_algebraMap_eq_of_presentation m ψ hL).le (presentationCoords m ψ) hI k hx

/-! ### The inclusion of the first `n` coordinates -/

/-- **The inclusion of the first `n` coordinates** `R{X₁, …, Xₙ} →ₐ[R] R{X₁, …, X_{n+m}}`. The
`m = 1` case is `AlgebraicGeometry.coordIncl` (issue 807); unifying the two would need
`FormalSchemes.AwayTopFiniteType` to import this file rather than the other way round, so they are
left separate. -/
def castAddHom (hI : I.FG) :
    RestrictedPowerSeries R I n →ₐ[R] RestrictedPowerSeries R I (n + m) :=
  haveI := (RestrictedPowerSeries.isAdicRing R I (n + m) hI).toIsAdicComplete
  evalAlgHom (idealOfDefinition R I (n + m)) (idealOfDefinition_eq_map R I (n + m)).ge
    (fun i => rpsCoord R I (n + m) (Fin.castAdd m i))

theorem castAddHom_rpsCoord (hI : I.FG) (i : Fin n) :
    castAddHom (I := I) m hI (rpsCoord R I n i) = rpsCoord R I (n + m) (Fin.castAdd m i) :=
  haveI := (RestrictedPowerSeries.isAdicRing R I (n + m) hI).toIsAdicComplete
  evalAlgHom_rpsCoord _ _ _ i

theorem castAddHom_mem_pow (hI : I.FG) (k : ℕ) {x : RestrictedPowerSeries R I n}
    (hx : x ∈ (idealOfDefinition R I n) ^ k) :
    castAddHom (I := I) m hI x ∈ (idealOfDefinition R I (n + m)) ^ k :=
  haveI := (RestrictedPowerSeries.isAdicRing R I (n + m) hI).toIsAdicComplete
  evalHom_mem_pow (idealOfDefinition R I (n + m)) (idealOfDefinition_eq_map R I (n + m)).ge
    (fun i => rpsCoord R I (n + m) (Fin.castAdd m i)) hI k hx

include hI hL in
/-- **On the first `n` coordinates the presentation homomorphism is `ψ` followed by the structure
map.** Both sides are continuous ring homomorphisms out of `R{X₁, …, Xₙ}` agreeing on the constants
and on the coordinates, so the uniqueness half of the polydisc's universal property
(`RestrictedPowerSeries.hom_ext`) identifies them. -/
theorem presentationHom_comp_castAddHom :
    (presentationHom m hI ψ hL).toRingHom.comp (castAddHom m hI).toRingHom =
      (algebraMap A (RestrictedPowerSeries A L m)).comp ψ.toRingHom := by
  haveI := isAdicComplete_of_presentation m hI ψ hL
  have hLpow : ∀ (k : ℕ) (x : RestrictedPowerSeries R I n),
      x ∈ (idealOfDefinition R I n) ^ k →
        algebraMap A (RestrictedPowerSeries A L m) (ψ x) ∈ (idealOfDefinition A L m) ^ k := by
    intro k x hx
    have h1 : ψ x ∈ L ^ k := by
      have := Ideal.mem_map_of_mem ψ.toRingHom hx
      rwa [Ideal.map_pow, hL] at this
    have h2 := Ideal.mem_map_of_mem (algebraMap A (RestrictedPowerSeries A L m)) h1
    rwa [Ideal.map_pow, ← idealOfDefinition_eq_map] at h2
  refine hom_ext (L := idealOfDefinition A L m) hI (fun k x hx => ?_) (fun k x hx => ?_)
    (fun r => ?_) (fun i => ?_)
  · exact presentationHom_mem_pow m hI ψ hL k (castAddHom_mem_pow m hI k hx)
  · exact hLpow k x hx
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R A (RestrictedPowerSeries A L m)]
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    change presentationHom m hI ψ hL (castAddHom m hI (rpsCoord R I n i)) = _
    rw [castAddHom_rpsCoord, presentationHom_rpsCoord, presentationCoords_castAdd]

include hI hL in
theorem presentationHom_castAddHom (x : RestrictedPowerSeries R I n) :
    presentationHom m hI ψ hL (castAddHom m hI x) =
      algebraMap A (RestrictedPowerSeries A L m) (ψ x) :=
  DFunLike.congr_fun (presentationHom_comp_castAddHom m hI ψ hL) x

/-! ### The ideal of definition, and surjectivity -/

include hI hL in
/-- The presentation homomorphism carries the ideal of definition onto the ideal of definition. It
does not depend on the evaluation tuple — only on the map being an `R`-algebra homomorphism. -/
theorem map_idealOfDefinition_presentationHom :
    (idealOfDefinition R I (n + m)).map (presentationHom m hI ψ hL).toRingHom =
      idealOfDefinition A L m := by
  rw [idealOfDefinition_eq_map, Ideal.map_map]
  rw [show (presentationHom m hI ψ hL).toRingHom.comp
      (algebraMap R (RestrictedPowerSeries R I (n + m))) =
      algebraMap R (RestrictedPowerSeries A L m) from (presentationHom m hI ψ hL).comp_algebraMap]
  exact map_algebraMap_eq_of_presentation m ψ hL

include hI hL in
/-- **The polynomial ring `A[Y₁, …, Y_m]` lands in the range of the presentation homomorphism.**
The range is a subring; it contains the structure map of every `a : A` (because `ψ` is surjective
and the first `n` coordinates map onto `A`) and every coordinate `Y_j`, and `A[Y₁, …, Y_m]` is
generated by those. -/
theorem algebraMap_mem_range_presentationHom (hψ : Function.Surjective ψ)
    (p : MvPolynomial (Fin m) A) :
    algebraMap (MvPolynomial (Fin m) A) (RestrictedPowerSeries A L m) p ∈
      (presentationHom m hI ψ hL).toRingHom.range := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨x, rfl⟩ := hψ a
    refine ⟨castAddHom m hI x, ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [presentationHom_castAddHom, algebraMap_MvPolynomial_apply, of_C_eq_algebraMap]
  | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
  | mul_X p j hp =>
    rw [map_mul]
    refine Subring.mul_mem _ hp ⟨rpsCoord R I (n + m) (Fin.natAdd n j), ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [presentationHom_rpsCoord, presentationCoords_natAdd, algebraMap_MvPolynomial_apply]

include hI hL in
/-- **Surjectivity of the presentation homomorphism.** By
`AdicCompletion.surjective_of_mk_map_comp_surjective` it suffices to be surjective modulo the ideal
of definition, and there every element is represented by a polynomial in `A[Y₁, …, Y_m]`, which
lies in the range by `algebraMap_mem_range_presentationHom`. -/
theorem presentationHom_surjective (hψ : Function.Surjective ψ) :
    Function.Surjective (presentationHom m hI ψ hL) := by
  haveI hsrc : IsAdicComplete (idealOfDefinition R I (n + m))
      (RestrictedPowerSeries R I (n + m)) :=
    (RestrictedPowerSeries.isAdicRing R I (n + m) hI).toIsAdicComplete
  haveI htgt : IsAdicComplete (idealOfDefinition A L m) (RestrictedPowerSeries A L m) :=
    isAdicComplete_of_presentation m hI ψ hL
  have hJ := map_idealOfDefinition_presentationHom m hI ψ hL
  haveI hhaus : IsHausdorff
      ((idealOfDefinition R I (n + m)).map (presentationHom m hI ψ hL).toRingHom)
      (RestrictedPowerSeries A L m) := by rw [hJ]; infer_instance
  refine surjective_of_mk_map_comp_surjective
    (I := idealOfDefinition R I (n + m)) (f := (presentationHom m hI ψ hL).toRingHom) ?_
  intro ybar
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (L.map (algebraMap A (MvPolynomial (Fin m) A))) 1 y)
  obtain ⟨t, ht⟩ := RingHom.mem_range.mp (algebraMap_mem_range_presentationHom m hI ψ hL hψ w)
  refine ⟨t, ?_⟩
  have hofw : algebraMap (MvPolynomial (Fin m) A) (RestrictedPowerSeries A L m) w =
      AdicCompletion.of (L.map (algebraMap A (MvPolynomial (Fin m) A)))
        (MvPolynomial (Fin m) A) w := algebraMap_MvPolynomial_apply A L m w
  have hev : AdicCompletion.evalₐ (L.map (algebraMap A (MvPolynomial (Fin m) A))) 1
      (y - AdicCompletion.of (L.map (algebraMap A (MvPolynomial (Fin m) A)))
        (MvPolynomial (Fin m) A) w) = 0 := by
    rw [map_sub, sub_eq_zero, AdicCompletion.evalₐ_of, hw]
  have hker : y - AdicCompletion.of (L.map (algebraMap A (MvPolynomial (Fin m) A)))
      (MvPolynomial (Fin m) A) w ∈ idealOfDefinition A L m := by
    have hmem : y - AdicCompletion.of (L.map (algebraMap A (MvPolynomial (Fin m) A)))
        (MvPolynomial (Fin m) A) w ∈
        RingHom.ker (AdicCompletion.evalₐ
          (L.map (algebraMap A (MvPolynomial (Fin m) A))) 1).toRingHom :=
      RingHom.mem_ker.mpr hev
    rwa [AdicCompletion.ker_evalₐ _ ((fg_of_presentation hI ψ hL).map _) 1, pow_one] at hmem
  rw [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hJ, ht, hofw]
  have hneg := neg_mem hker
  rwa [neg_sub] at hneg

end Presentation

/-! ### Arity-additivity of the formal polydisc -/

section ArityAdd

variable (R : Type u) [CommRing R] (I : Ideal R) (n m : ℕ) (hI : I.FG)

theorem map_id_idealOfDefinition :
    (idealOfDefinition R I n).map (AlgHom.id R (RestrictedPowerSeries R I n)).toRingHom =
      idealOfDefinition R I n :=
  Ideal.map_id _

/-- **Arity-additivity of the formal polydisc**: the map
`R{X₁, …, X_{n+m}} →ₐ[R] R{X₁, …, Xₙ}{Y₁, …, Y_m}` sending the first `n` coordinates to the
coordinates of the inner polydisc and the last `m` to the outer ones. -/
def arityAddHom : RestrictedPowerSeries R I (n + m) →ₐ[R]
    RestrictedPowerSeries (RestrictedPowerSeries R I n) (idealOfDefinition R I n) m :=
  presentationHom m hI (AlgHom.id R (RestrictedPowerSeries R I n))
    (map_id_idealOfDefinition R I n)

/-- **Arity-additivity, surjectivity**: `R{X₁, …, X_{n+m}} ↠ R{X₁, …, Xₙ}{Y₁, …, Y_m}`. This is
the ingredient transitivity of `IsTopologicallyFiniteType` was missing. -/
theorem arityAddHom_surjective : Function.Surjective (arityAddHom R I n m hI) :=
  presentationHom_surjective m hI _ _ Function.surjective_id

/-- **Arity-additivity, ideals**: the surjection carries the ideal of definition of the
`(n+m)`-variable polydisc onto that of the iterated one. -/
theorem map_idealOfDefinition_arityAddHom :
    (idealOfDefinition R I (n + m)).map (arityAddHom R I n m hI).toRingHom =
      idealOfDefinition (RestrictedPowerSeries R I n) (idealOfDefinition R I n) m :=
  map_idealOfDefinition_presentationHom m hI _ _

end ArityAdd

end RestrictedPowerSeries

namespace IsTopologicallyFiniteType

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}

open RestrictedPowerSeries in
/-- **The polydisc over a tf-type algebra is tf-type**: if `A` is topologically of finite type over
`(R, I)`, so is `A{Y₁, …, Y_m}`, presented by `R{X₁, …, X_{n+m}}`. -/
theorem restrictedPowerSeries (hI : I.FG) (h : IsTopologicallyFiniteType R I A L) (m : ℕ) :
    IsTopologicallyFiniteType R I (RestrictedPowerSeries A L m) (idealOfDefinition A L m) := by
  obtain ⟨n, ψ, hψ, hL⟩ := h
  exact ⟨n + m, presentationHom m hI ψ hL, presentationHom_surjective m hI ψ hL hψ,
    map_idealOfDefinition_presentationHom m hI ψ hL⟩

variable {B : Type u} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] {M : Ideal B}

/-- **Transitivity of `IsTopologicallyFiniteType`**: if `A` is topologically of finite type over
`(R, I)` and `B` is topologically of finite type over `(A, L)`, then `B` is topologically of finite
type over `(R, I)`. A presentation of `B` by `m` variables over `A` and one of `A` by `n` variables
over `R` compose to a presentation of `B` by `n + m` variables over `R`. -/
theorem trans (hI : I.FG) (hA : IsTopologicallyFiniteType R I A L)
    (hB : IsTopologicallyFiniteType A L B M) : IsTopologicallyFiniteType R I B M := by
  obtain ⟨m, χ, hχ, hM⟩ := hB
  exact of_surjective (restrictedPowerSeries hI hA m) (χ.restrictScalars R) hχ hM

end IsTopologicallyFiniteType
