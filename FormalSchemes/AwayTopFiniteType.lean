import FormalSchemes.AwayCompletionSurjective
import FormalSchemes.BaseChange
import FormalSchemes.TopFiniteType

set_option linter.style.header false
set_option linter.style.setOption false
-- `awayEval_comp_coordIncl` compares two ring homomorphisms out of `R{X₁, …, Xₙ}` whose
-- targets are nested completions of a localization; the `isDefEq` checks that unfold
-- `awayCompletion`/`RestrictedPowerSeries` through `AdicCompletion` are what costs the
-- heartbeats. 400000 and 800000 both time out; 1600000 leaves headroom.
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-!
# A basic-open chart of a tf-type formal affine is tf-type (EGA I §10.13)

Let `(R, I)` be an adic base with `I` finitely generated and let `A` be an `R`-algebra which is
**topologically of finite type** over `(R, I)` with ideal of definition `L` — that is, a quotient
of a restricted power series ring `R{X₁, …, Xₙ}` carrying the ideal of definition onto `L`
(`IsTopologicallyFiniteType`). For `g : A` the basic-open chart of `Spf A` at
`g` is `Spf` of the completed localization

```
A{1/g}^ = FormalSpectrum.awayCompletion L g = AdicCompletion (L·A_g) A_g .
```

This file proves that `A{1/g}^` is again topologically of finite type over `(R, I)`, with **one
extra variable**: informally `A{1/g}^ = A{T}^/(T·g − 1)`, so a presentation of `A` by `n`
variables gives a presentation of `A{1/g}^` by `n + 1`.

## Main results

* `AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion`: the theorem above.
* `AlgebraicGeometry.IsTopologicallyFiniteType.self`: a complete adic ring is tf-type over itself
  (the zero-variable presentation).
* `AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_base`: the specialisation to
  `A = R`, `L = I`, which is the shape `FormalSpectrum.basicOpenChart` charts on `Spf R` appear in.
  It needs `[IsAdicComplete I R]`, inherited from `self`.
* `Ideal.map_algebraMap_of_tower`: transitivity of ideal extension along a tower, stated for the
  reason in the next-but-one section. The `awayCompletion`-specific consequences that used to sit
  beside it — `awayCompletionIdeal_eq_map_algebraMap` and `map_algebraMap_awayCompletion` — moved
  to `FormalSchemes.BasicOpenChart` in issue 895; this file now consumes them from there. Nothing
  in the tree currently uses `map_algebraMap_of_tower` itself, which was left in place rather than
  deleted because it is a general `Ideal` fact independent of this file's subject.

## Route

No polynomial presentation `A[T]/(T·g − 1)` is built and completed. Instead:

1. A presentation `ψ : R{X₁, …, Xₙ} ↠ A` is turned into an evaluation homomorphism
   `χ : R{X₁, …, Xₙ₊₁} → A{1/g}^` (`RestrictedPowerSeries.evalAlgHom`) sending `Xᵢ ↦ ψ(Xᵢ)` for
   `i ≤ n` and the extra variable `Xₙ₊₁ ↦ g⁻¹`.
2. Its **surjectivity is one application** of
   `FormalSpectrum.surjective_of_algebraMap_mem_range'` (issue 793): a continuous map into
   `AdicCompletion E A_g` is surjective as soon as its image contains `A` and `g⁻¹`. The `hbase`
   half is `χ ∘ ι = algebraMap A (A{1/g}^) ∘ ψ` for the coordinate inclusion
   `ι : R{X₁, …, Xₙ} → R{X₁, …, Xₙ₊₁}`, proved by the polydisc's uniqueness principle
   `RestrictedPowerSeries.hom_ext`; the `hinv` half is `χ(Xₙ₊₁) = g⁻¹` by construction.
3. The ideal condition `(idealOfDefinition R I (n+1))·χ = L·A{1/g}^` is independent of `χ`: since
   `χ` is an `R`-algebra map it reduces to `I·A{1/g}^ = awayCompletionIdeal L g`, which is
   `FormalSpectrum.map_algebraMap_awayCompletion` (`FormalSchemes.BasicOpenChart`).

## The ideal convention, stated once

`FormalSpectrum.awayCompletion K g` completes at `K.map (algebraMap C C_g)` — the extension of an
ideal of the ring **being localized**. This file uses that convention throughout, with `C = A` and
`K = L`. It is *not* definitionally the extension of an ideal of the base `R`, even though
`I·A = L` makes the two equal (`Ideal.map f I` unfolds to `Ideal.span (f '' I)`, so no unifier
bridges them). `FormalSpectrum.map_algebraMap_awayCompletion` (`FormalSchemes.BasicOpenChart`) is
the bridge, and it is used explicitly wherever the two spellings meet — see
`FormalSchemes/TateFibreOverlapTransition.lean` for the same wall.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open AlgebraicGeometry FormalSpectrum RestrictedPowerSeries

universe u

/-- **Transitivity of ideal extension along a scalar tower.** If `J·B = K` then `J·S = K·S`.

Stated with `S` an independent type variable on purpose: the intended `S` is
`FormalSpectrum.awayCompletion K g`, whose *type* mentions the extended ideal, so a `rw` with
`Ideal.map_map` inside it fails on a non-type-correct motive. Applying a lemma proved at an
abstract `S` sidesteps that entirely. -/
theorem Ideal.map_algebraMap_of_tower {R B S : Type u} [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra B S] [Algebra R S] [IsScalarTower R B S]
    (J : Ideal R) (K : Ideal B) (hJ : J.map (algebraMap R B) = K) :
    J.map (algebraMap R S) = K.map (algebraMap B S) := by
  subst hJ
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A} (g : A)

/-- The `i`-th coordinate of the restricted power series ring, as an element of `R{X₁, …, Xₙ}`. -/
abbrev rpsCoord (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) (i : Fin n) :
    RestrictedPowerSeries R I n :=
  AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R))) (MvPolynomial (Fin n) R)
    (MvPolynomial.X i)

/-! ### The ideal of definition of the completed localization -/

/-- `L·A_g` is finitely generated when `I` is, given `I·A = L`. -/
theorem awayLocIdeal_fg (hI : I.FG) (h : I.map (algebraMap R A) = L) :
    (L.map (algebraMap A (Localization.Away g))).FG := by
  subst h
  rw [Ideal.map_map]
  exact hI.map _

/-- `A{1/g}^` is complete for its ideal of definition. -/
theorem awayCompletion_isAdicComplete (hI : I.FG) (h : I.map (algebraMap R A) = L) :
    IsAdicComplete (awayCompletionIdeal L g) (awayCompletion L g) :=
  AdicCompletion.isAdicComplete_map _ (awayLocIdeal_fg g hI h)


/-! ### The two evaluation homomorphisms -/

variable {n : ℕ}

/-- **The coordinate inclusion** `R{X₁, …, Xₙ} → R{X₁, …, Xₙ₊₁}`, sending `Xᵢ` to `Xᵢ`. It is the
evaluation homomorphism of the polydisc at the first `n` coordinates of the bigger one. -/
def coordIncl (hI : I.FG) :
    RestrictedPowerSeries R I n →ₐ[R] RestrictedPowerSeries R I (n + 1) :=
  haveI := (RestrictedPowerSeries.isAdicRing R I (n + 1) hI).toIsAdicComplete
  RestrictedPowerSeries.evalAlgHom (idealOfDefinition R I (n + 1))
    (idealOfDefinition_eq_map R I (n + 1)).ge (fun i => rpsCoord R I (n + 1) i.castSucc)

theorem coordIncl_coord (hI : I.FG) (i : Fin n) :
    coordIncl (I := I) hI (rpsCoord R I n i) = rpsCoord R I (n + 1) i.castSucc := by
  haveI := (RestrictedPowerSeries.isAdicRing R I (n + 1) hI).toIsAdicComplete
  change RestrictedPowerSeries.evalHom R I n (idealOfDefinition R I (n + 1))
    (idealOfDefinition_eq_map R I (n + 1)).ge _ _ = _
  rw [RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X]

/-- The evaluation tuple defining `χ`: the images of a presentation's coordinates, and `g⁻¹`. -/
def awaySeq (ψ : RestrictedPowerSeries R I n →ₐ[R] A) :
    Fin (n + 1) → awayCompletion L g :=
  Fin.snoc (fun i => algebraMap A (awayCompletion L g) (ψ (rpsCoord R I n i)))
    (algebraMap (Localization.Away g) (awayCompletion L g) (IsLocalization.Away.invSelf g))

/-- **The presenting homomorphism** `χ : R{X₁, …, Xₙ₊₁} → A{1/g}^` of the completed localization:
evaluation at `ψ(X₁), …, ψ(Xₙ), g⁻¹`. -/
def awayEval (hI : I.FG) (h : I.map (algebraMap R A) = L)
    (ψ : RestrictedPowerSeries R I n →ₐ[R] A) :
    RestrictedPowerSeries R I (n + 1) →ₐ[R] awayCompletion L g :=
  haveI := awayCompletion_isAdicComplete g hI h
  RestrictedPowerSeries.evalAlgHom (awayCompletionIdeal L g)
    (map_algebraMap_awayCompletion g h).le (awaySeq g ψ)

theorem awayEval_coord (hI : I.FG) (h : I.map (algebraMap R A) = L)
    (ψ : RestrictedPowerSeries R I n →ₐ[R] A) (i : Fin n) :
    awayEval g hI h ψ (rpsCoord R I (n + 1) i.castSucc) =
      algebraMap A (awayCompletion L g) (ψ (rpsCoord R I n i)) := by
  haveI := awayCompletion_isAdicComplete g hI h
  change RestrictedPowerSeries.evalHom R I (n + 1) (awayCompletionIdeal L g)
    (map_algebraMap_awayCompletion g h).le _ _ = _
  rw [RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X]
  exact Fin.snoc_castSucc _ _ i

theorem awayEval_last (hI : I.FG) (h : I.map (algebraMap R A) = L)
    (ψ : RestrictedPowerSeries R I n →ₐ[R] A) :
    awayEval g hI h ψ (rpsCoord R I (n + 1) (Fin.last n)) =
      algebraMap (Localization.Away g) (awayCompletion L g) (IsLocalization.Away.invSelf g) := by
  haveI := awayCompletion_isAdicComplete g hI h
  change RestrictedPowerSeries.evalHom R I (n + 1) (awayCompletionIdeal L g)
    (map_algebraMap_awayCompletion g h).le _ _ = _
  rw [RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X]
  exact Fin.snoc_last _ _



/-- The ideal condition of the presentation: `χ` carries the ideal of definition of the polydisc
onto that of `A{1/g}^`. It does not depend on the evaluation tuple — only on `χ` being an
`R`-algebra map — so it reduces to `map_algebraMap_awayCompletion`. -/
theorem map_idealOfDefinition_awayEval (hI : I.FG) (h : I.map (algebraMap R A) = L)
    (ψ : RestrictedPowerSeries R I n →ₐ[R] A) :
    (idealOfDefinition R I (n + 1)).map (awayEval g hI h ψ).toRingHom =
      awayCompletionIdeal L g := by
  rw [idealOfDefinition_eq_map, Ideal.map_map]
  have hc : (awayEval g hI h ψ).toRingHom.comp
      (algebraMap R (RestrictedPowerSeries R I (n + 1))) =
      algebraMap R (FormalSpectrum.awayCompletion L g) := (awayEval g hI h ψ).comp_algebraMap
  rw [hc]
  exact map_algebraMap_awayCompletion g h

/-! ### `χ ∘ ι` is the completion map composed with the presentation -/

/-- **The key compatibility**: on the first `n` coordinates, `χ` is the presentation `ψ` followed
by `A → A{1/g}^`. Both sides are continuous ring homomorphisms out of the polydisc agreeing on the
constants and on the coordinates, so the uniqueness half of the polydisc's universal property
(`RestrictedPowerSeries.hom_ext`) identifies them. -/
theorem awayEval_comp_coordIncl (hI : I.FG) (h : I.map (algebraMap R A) = L)
    (ψ : RestrictedPowerSeries R I n →ₐ[R] A)
    (hL : (idealOfDefinition R I n).map ψ.toRingHom = L) :
    (awayEval g hI h ψ).toRingHom.comp (coordIncl (I := I) (n := n) hI).toRingHom =
      (algebraMap A (awayCompletion L g)).comp ψ.toRingHom := by
  haveI := awayCompletion_isAdicComplete g hI h
  haveI := (RestrictedPowerSeries.isAdicRing R I (n + 1) hI).toIsAdicComplete
  refine RestrictedPowerSeries.hom_ext (awayCompletionIdeal L g) hI (fun m x hx => ?_)
    (fun m x hx => ?_) (fun r => ?_) (fun i => ?_)
  · -- `ι` then `χ`, each continuous by `evalHom_mem_pow`
    have h₁ : coordIncl (I := I) (n := n) hI x ∈ (idealOfDefinition R I (n + 1)) ^ m :=
      RestrictedPowerSeries.evalHom_mem_pow (idealOfDefinition R I (n + 1))
        (idealOfDefinition_eq_map R I (n + 1)).ge _ hI m hx
    exact RestrictedPowerSeries.evalHom_mem_pow (awayCompletionIdeal L g)
      (map_algebraMap_awayCompletion g h).le _ hI m h₁
  · -- `ψ` carries `(I·R{X})^m` into `L^m`, and `A → A{1/g}^` carries `L^m` into the ideal of
    -- definition to the `m`-th power
    have hψx : ψ.toRingHom x ∈ L ^ m := by
      have := Ideal.mem_map_of_mem ψ.toRingHom hx
      rwa [Ideal.map_pow, hL] at this
    have := Ideal.mem_map_of_mem (algebraMap A (awayCompletion L g)) hψx
    rwa [Ideal.map_pow, awayCompletionIdeal_eq_map_algebraMap] at this
  · -- both sides are `R`-algebra maps
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  · -- on coordinates, by construction
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) (MvPolynomial.X i)) = rpsCoord R I n i from rfl,
      coordIncl_coord hI i, awayEval_coord g hI h ψ i]

/-! ### The theorem -/

/-- **A basic-open chart of a topologically-finite-type formal affine is topologically of finite
type** (EGA I §10.13): if `A` is tf-type over `(R, I)` with ideal of definition `L`, then so is the
completed localization `A{1/g}^`, with one extra variable. -/
theorem IsTopologicallyFiniteType.awayCompletion (hI : I.FG)
    (hA : IsTopologicallyFiniteType R I A L) :
    IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion L g)
      (awayCompletionIdeal L g) := by
  obtain ⟨n, ψ, hψ, hL⟩ := hA
  have h : I.map (algebraMap R A) = L := IsTopologicallyFiniteType.map_eq_of_presentation hL
  haveI := awayCompletion_isAdicComplete g hI h
  haveI : IsPrecomplete (idealOfDefinition R I (n + 1)) (RestrictedPowerSeries R I (n + 1)) :=
    (RestrictedPowerSeries.isAdicRing R I (n + 1) hI).toIsAdicComplete.toIsPrecomplete
  refine ⟨n + 1, awayEval g hI h ψ, ?_, ?_⟩
  · -- surjectivity, by the away-completion criterion of issue 793
    refine FormalSpectrum.surjective_of_algebraMap_mem_range' g
      (L.map (algebraMap A (Localization.Away g))) (awayLocIdeal_fg g hI h)
      (idealOfDefinition R I (n + 1)) (awayEval g hI h ψ).toRingHom ?_ (fun c => ?_) ?_
    · exact map_idealOfDefinition_awayEval g hI h ψ
    · obtain ⟨x, rfl⟩ := hψ c
      refine ⟨coordIncl (I := I) (n := n) hI x, ?_⟩
      rw [← IsScalarTower.algebraMap_apply A (Localization.Away g)
        (FormalSpectrum.awayCompletion L g)]
      exact RingHom.congr_fun (awayEval_comp_coordIncl g hI h ψ hL) x
    · exact ⟨rpsCoord R I (n + 1) (Fin.last n), awayEval_last g hI h ψ⟩
  · exact map_idealOfDefinition_awayEval g hI h ψ


/-- **A complete adic ring is topologically of finite type over itself**, via the zero-variable
presentation: `R{} = AdicCompletion (I·R[∅]) R[∅]` evaluates onto `R` at the empty tuple, and that
evaluation is surjective because it is the identity on constants.

Arguably this belongs beside `RestrictedPowerSeries.isTopologicallyFiniteType` in
`FormalSchemes.TopFiniteTypeBaseChange`; it lives here because it is only needed for the corollary
below and this issue was scoped to be purely additive. Note the completeness hypothesis is
genuinely necessary — with `I` non-nilpotent and `R` not `I`-adically complete, `R` is *not* a
quotient of any `R{X₁, …, Xₙ}`. -/
theorem IsTopologicallyFiniteType.self [IsAdicComplete I R] :
    IsTopologicallyFiniteType R I R I := by
  have hIL : I.map (algebraMap R R) ≤ I := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  refine ⟨0, RestrictedPowerSeries.evalAlgHom I hIL (fun i => i.elim0),
    fun r => ⟨algebraMap R (RestrictedPowerSeries R I 0) r, ?_⟩, ?_⟩
  · exact RestrictedPowerSeries.evalHom_algebraMap I hIL (fun i => i.elim0) r
  · rw [idealOfDefinition_eq_map, Ideal.map_map]
    have hc : (RestrictedPowerSeries.evalAlgHom (R := R) (I := I) (n := 0) I hIL
        (fun i => i.elim0)).toRingHom.comp (algebraMap R (RestrictedPowerSeries R I 0)) =
        algebraMap R R :=
      (RestrictedPowerSeries.evalAlgHom I hIL (fun i => i.elim0)).comp_algebraMap
    rw [hc, Algebra.algebraMap_self, Ideal.map_id]

/-- **A basic-open chart of the base itself is topologically of finite type**: `R{1/f}^` is tf-type
over `(R, I)`. The specialisation `A = R`, `L = I` of
`IsTopologicallyFiniteType.awayCompletion`, and the shape in which the charts of
`FormalSpectrum.basicOpenChart` on `Spf R` occur. -/
theorem IsTopologicallyFiniteType.awayCompletion_base [IsAdicComplete I R] (hI : I.FG) (f : R) :
    IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion I f)
      (awayCompletionIdeal I f) :=
  IsTopologicallyFiniteType.awayCompletion (A := R) (L := I) f hI
    (IsTopologicallyFiniteType.self)

end AlgebraicGeometry

end
