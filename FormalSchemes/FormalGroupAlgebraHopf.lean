import FormalSchemes.FormalTorus
import FormalSchemes.CompletedTensor
import FormalSchemes.CompletedTensorAssoc

set_option linter.style.header false

/-!
# The Hopf-algebra structure on the general formal group algebra

Over an adic ring `R` with finitely generated ideal of definition `I`, and a discrete abelian
group `M`, the **formal group algebra** `R⟨M⟩` (the `I`-adic completion of the group algebra
`R[M]`, see `FormalSchemes/FormalTorus.lean`) carries the tensor-level Hopf-algebra / group-object
structure making its formal spectrum `D(M) = Spf R⟨M⟩` a group object. This file develops that
structure, generalizing the `Ĝm` development of `FormalSchemes/FormalGm.lean` (the case `M = ℤ`,
namespace `RestrictedLaurentSeries`) to an arbitrary `M`; specializing to `M = ℤʳ = (Fin r →₀ ℤ)`
it covers the formal tori `Ĝm^r` (Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105, §8).

Where `FormalGm.lean` evaluates at a single group-like unit (`unitEval` at `tensorX`), the general
case evaluates at a **character** `χ : Multiplicative M →* Sˣ` via `FormalGroupAlgebra.charEval`.
The genuinely new construction is the *group-like character* `comulChar : Multiplicative M →*
(R⟨M⟩ ⊗̂_R R⟨M⟩)ˣ`, `g ↦ inl [g] · inr [g]`, whose associated point is the comultiplication:

* `comul`/`comulAlgHom` : the comultiplication, `[g] ↦ [g] ⊗ [g]`;
* `counit`/`counitAlgHom` : the counit (character `1`), `[g] ↦ 1`;
* `antipode`/`antipodeAlgHom` : the antipode (inverse character), `[g] ↦ [-g]`;
* `mulAlgHom` : the multiplication fold `R⟨M⟩ ⊗̂_R R⟨M⟩ → R⟨M⟩`.

The five Hopf-algebra axioms are proved at the tensor level by comparing continuous points via
`FormalGroupAlgebra.point_ext` (agreement on every group-like generator `[g]`):
`counit_law_left`, `counit_law_right`, `comul_coassoc`, `antipode_law_left`, `antipode_law_right`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §8.
-/

noncomputable section

open Ideal

universe u

namespace FormalGroupAlgebra

variable (R : Type u) [CommRing R] (I : Ideal R) (M : Type) [AddCommGroup M]

section Group

variable (hI : I.FG)

/-- The completed tensor square `R⟨M⟩ ⊗̂_R R⟨M⟩`, the target of the comultiplication of the formal
group algebra. -/
abbrev tensorSquare : Type u :=
  CompletedTensorProduct R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)

/-- The **group-like character** into the units of `R⟨M⟩` itself: the character `g ↦ [g]`, obtained
as the character attached to the identity point of `D(M)`. Its value at `g` is `[g] = X R I M g`. -/
def groupLikeChar : Multiplicative M →* (FormalGroupAlgebra R I M)ˣ :=
  pointChar R I M (AlgHom.id R (FormalGroupAlgebra R I M))

theorem groupLikeChar_val (g : Multiplicative M) :
    (groupLikeChar R I M g : FormalGroupAlgebra R I M) = X R I M g.toAdd := by
  rw [groupLikeChar, pointChar_val, AlgHom.id_apply]

/-- The **group-like character of the comultiplication** `χ_Δ : Multiplicative M →*
(R⟨M⟩ ⊗̂_R R⟨M⟩)ˣ`, `g ↦ inl [g] · inr [g]` — the genuinely new construction of this file: its
associated point (via `charEval`) is the comultiplication of `D(M)`. -/
def comulChar : Multiplicative M →* (tensorSquare R I M)ˣ :=
  ((Units.map (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)).toRingHom.toMonoidHom).comp (groupLikeChar R I M)) *
    ((Units.map (CompletedTensorProduct.inr R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)).toRingHom.toMonoidHom).comp (groupLikeChar R I M))

theorem comulChar_val (g : Multiplicative M) :
    (comulChar R I M g : tensorSquare R I M) =
      CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)
          (X R I M g.toAdd) *
        CompletedTensorProduct.inr R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)
          (X R I M g.toAdd) := by
  rw [comulChar, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Units.coe_map, Units.coe_map, groupLikeChar_val]
  rfl

/-- **The comultiplication of the formal group algebra**: the continuous `R`-algebra map
`R⟨M⟩ → R⟨M⟩ ⊗̂_R R⟨M⟩` sending the group-like `[g]` to `[g] ⊗ [g]` (Bosch, §8). -/
def comul :
    letI := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI
    FormalGroupAlgebra R I M →+* tensorSquare R I M :=
  letI hR := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
    (FormalGroupAlgebra R I M) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (tensorSquare R I M) := hR.toIsAdicComplete
  charEval R I M
    (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M))
    (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
    (comulChar R I M)

/-- The comultiplication sends the group-like `[g]` to `[g] ⊗ [g]`. -/
theorem comul_X (g : M) :
    letI := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI
    comul R I M hI (X R I M g) =
      CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)
          (X R I M g) *
        CompletedTensorProduct.inr R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)
          (X R I M g) := by
  letI hR := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
    (FormalGroupAlgebra R I M) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (tensorSquare R I M) := hR.toIsAdicComplete
  have h := charEval_X R I M
    (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M))
    (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
    (comulChar R I M) g
  rw [comulChar_val, toAdd_ofAdd] at h
  exact h

/-- **The counit**: the continuous `R`-algebra map `R⟨M⟩ → R` sending every group-like `[g]` to
`1` (the character `1`) — the identity section of `D(M)`. -/
def counit [TopologicalSpace R] [IsAdicRing I] : FormalGroupAlgebra R I M →+* R :=
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  charEval R I M I (le_of_eq (Ideal.map_id I)) 1

theorem counit_X [TopologicalSpace R] [IsAdicRing I] (g : M) : counit R I M (X R I M g) = 1 := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  have h := charEval_X R I M I (le_of_eq (Ideal.map_id I)) (1 : Multiplicative M →* Rˣ) g
  rw [MonoidHom.one_apply, Units.val_one] at h
  exact h

/-- **The antipode**: the continuous `R`-algebra map `R⟨M⟩ → R⟨M⟩` sending `[g]` to `[-g]` (the
inverse of the group-like character) — the inversion of `D(M)`. -/
def antipode (hI : I.FG) :
    letI := isAdicRing R I M hI
    FormalGroupAlgebra R I M →+* FormalGroupAlgebra R I M :=
  letI hR := isAdicRing R I M hI
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    hR.toIsAdicComplete
  charEval R I M (idealOfDefinition R I M)
    (le_of_eq (idealOfDefinition_eq_map R I M).symm) (groupLikeChar R I M)⁻¹

/-- **The antipode inverts the group-like elements**: `antipode [g] = [-g]`. -/
theorem antipode_X (g : M) :
    letI := isAdicRing R I M hI
    antipode R I M hI (X R I M g) = X R I M (-g) := by
  letI := isAdicRing R I M hI
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  set w : (FormalGroupAlgebra R I M)ˣ := groupLikeChar R I M (Multiplicative.ofAdd g) with hw
  have hval : (w : FormalGroupAlgebra R I M) = X R I M g := by
    rw [hw, groupLikeChar_val, toAdd_ofAdd]
  have hAnti : antipode R I M hI (X R I M g) = Units.val w⁻¹ := by
    have h := charEval_X R I M (idealOfDefinition R I M)
      (le_of_eq (idealOfDefinition_eq_map R I M).symm) (groupLikeChar R I M)⁻¹ g
    exact h
  rw [hAnti]
  have hinv : Units.val w⁻¹ * X R I M g = 1 := by
    have h := w.inv_mul
    rwa [hval] at h
  calc Units.val w⁻¹
      = Units.val w⁻¹ * (X R I M g * X R I M (-g)) := by rw [X_mul_X_neg, mul_one]
    _ = (Units.val w⁻¹ * X R I M g) * X R I M (-g) := by rw [mul_assoc]
    _ = X R I M (-g) := by rw [hinv, one_mul]

/-!
### The bundled `R`-algebra homomorphisms

The comultiplication, counit and antipode as `AlgHom`s, needed to feed them into
`CompletedTensorProduct.map`, together with the multiplication fold `∇`.
-/

/-- The counit, bundled as an `R`-algebra homomorphism `R⟨M⟩ →ₐ[R] R` (`[g] ↦ 1`). -/
def counitAlgHom [TopologicalSpace R] [IsAdicRing I] : FormalGroupAlgebra R I M →ₐ[R] R :=
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  charEvalAlgHom R I M I (le_of_eq (Ideal.map_id I)) 1

theorem counitAlgHom_X [TopologicalSpace R] [IsAdicRing I] (g : M) :
    counitAlgHom R I M (X R I M g) = 1 := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  have h := charEvalAlgHom_X R I M I (le_of_eq (Ideal.map_id I)) (1 : Multiplicative M →* Rˣ) g
  rw [MonoidHom.one_apply, Units.val_one] at h
  exact h

/-- The comultiplication, bundled as an `R`-algebra homomorphism (`[g] ↦ [g] ⊗ [g]`). -/
def comulAlgHom :
    letI := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI
    FormalGroupAlgebra R I M →ₐ[R] tensorSquare R I M :=
  letI hR := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
    (FormalGroupAlgebra R I M) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (tensorSquare R I M) := hR.toIsAdicComplete
  charEvalAlgHom R I M
    (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M))
    (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
    (comulChar R I M)

theorem comulAlgHom_X (g : M) :
    letI := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI
    comulAlgHom R I M hI (X R I M g) =
      CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)
          (X R I M g) *
        CompletedTensorProduct.inr R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)
          (X R I M g) := by
  letI hR := CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
    (FormalGroupAlgebra R I M) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (tensorSquare R I M) := hR.toIsAdicComplete
  exact comul_X R I M hI g

/-- The antipode, bundled as an `R`-algebra homomorphism `R⟨M⟩ →ₐ[R] R⟨M⟩` (`[g] ↦ [-g]`). -/
def antipodeAlgHom :
    letI := isAdicRing R I M hI
    FormalGroupAlgebra R I M →ₐ[R] FormalGroupAlgebra R I M :=
  letI hR := isAdicRing R I M hI
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    hR.toIsAdicComplete
  charEvalAlgHom R I M (idealOfDefinition R I M)
    (le_of_eq (idealOfDefinition_eq_map R I M).symm) (groupLikeChar R I M)⁻¹

theorem antipodeAlgHom_X (g : M) :
    letI := isAdicRing R I M hI
    antipodeAlgHom R I M hI (X R I M g) = X R I M (-g) := by
  letI := isAdicRing R I M hI
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  set w : (FormalGroupAlgebra R I M)ˣ := groupLikeChar R I M (Multiplicative.ofAdd g) with hw
  have hval : (w : FormalGroupAlgebra R I M) = X R I M g := by
    rw [hw, groupLikeChar_val, toAdd_ofAdd]
  have hAnti : antipodeAlgHom R I M hI (X R I M g) = Units.val w⁻¹ := by
    have h := charEvalAlgHom_X R I M (idealOfDefinition R I M)
      (le_of_eq (idealOfDefinition_eq_map R I M).symm) (groupLikeChar R I M)⁻¹ g
    exact h
  rw [hAnti]
  have hinv : Units.val w⁻¹ * X R I M g = 1 := by
    have h := w.inv_mul
    rwa [hval] at h
  calc Units.val w⁻¹
      = Units.val w⁻¹ * (X R I M g * X R I M (-g)) := by rw [X_mul_X_neg, mul_one]
    _ = (Units.val w⁻¹ * X R I M g) * X R I M (-g) := by rw [mul_assoc]
    _ = X R I M (-g) := by rw [hinv, one_mul]

/-- **The multiplication of `R⟨M⟩` as a completed-tensor fold** `∇ : R⟨M⟩ ⊗̂_R R⟨M⟩ →ₐ[R] R⟨M⟩`,
folding both factors by the identity (`inl a ↦ a`, `inr b ↦ b`, hence `a ⊗ b ↦ a · b`); the
target of the convolution product in the antipode axioms. -/
def mulAlgHom : tensorSquare R I M →ₐ[R] FormalGroupAlgebra R I M :=
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  CompletedTensorProduct.liftAlgHom (idealOfDefinition R I M)
    (le_of_eq (idealOfDefinition_eq_map R I M).symm)
    (AlgHom.id R (FormalGroupAlgebra R I M))
    (AlgHom.id R (FormalGroupAlgebra R I M))

@[simp]
theorem mulAlgHom_inl (a : FormalGroupAlgebra R I M) :
    mulAlgHom R I M hI (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) a) = a := by
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  exact CompletedTensorProduct.liftAlgHom_inl (idealOfDefinition R I M)
    (le_of_eq (idealOfDefinition_eq_map R I M).symm)
    (AlgHom.id R (FormalGroupAlgebra R I M))
    (AlgHom.id R (FormalGroupAlgebra R I M)) a

@[simp]
theorem mulAlgHom_inr (b : FormalGroupAlgebra R I M) :
    mulAlgHom R I M hI (CompletedTensorProduct.inr R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) b) = b := by
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  exact CompletedTensorProduct.liftAlgHom_inr (idealOfDefinition R I M)
    (le_of_eq (idealOfDefinition_eq_map R I M).symm)
    (AlgHom.id R (FormalGroupAlgebra R I M))
    (AlgHom.id R (FormalGroupAlgebra R I M)) b

/-- The multiplication `∇` maps the powers of the ideal of definition of the tensor square into
those of `R⟨M⟩` — continuity of `∇`. -/
theorem mulAlgHom_mem_pow (m : ℕ) {x : tensorSquare R I M}
    (hx : x ∈ (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M)) ^ m) :
    mulAlgHom R I M hI x ∈ (idealOfDefinition R I M) ^ m := by
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  exact CompletedTensorProduct.liftAlgHom_mem_pow (idealOfDefinition R I M)
    (le_of_eq (idealOfDefinition_eq_map R I M).symm)
    (AlgHom.id R (FormalGroupAlgebra R I M))
    (AlgHom.id R (FormalGroupAlgebra R I M)) hI m hx

/-!
### The counit axioms
-/

/-- The composite `ε ⊗̂ id` applying the counit to the first tensor factor, bundled as an
`R`-algebra homomorphism `R⟨M⟩ ⊗̂_R R⟨M⟩ →ₐ[R] R ⊗̂_R R⟨M⟩`. -/
def counitMapAlgHom [TopologicalSpace R] [IsAdicRing I] :
    tensorSquare R I M →ₐ[R]
      CompletedTensorProduct R I R (FormalGroupAlgebra R I M) where
  toRingHom := CompletedTensorProduct.map hI (counitAlgHom R I M)
    (AlgHom.id R (FormalGroupAlgebra R I M))
  commutes' r := by
    have h : CompletedTensorProduct.map hI (counitAlgHom R I M)
        (AlgHom.id R (FormalGroupAlgebra R I M))
        (algebraMap R (tensorSquare R I M) r) =
          algebraMap R (CompletedTensorProduct R I R (FormalGroupAlgebra R I M)) r := by
      rw [← (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M)).commutes r, CompletedTensorProduct.map_inl,
        (counitAlgHom R I M).commutes]
      exact (CompletedTensorProduct.inl R I R (FormalGroupAlgebra R I M)).commutes r
    exact h

theorem counitMapAlgHom_apply [TopologicalSpace R] [IsAdicRing I] (x : tensorSquare R I M) :
    counitMapAlgHom R I M hI x =
      CompletedTensorProduct.map hI (counitAlgHom R I M)
        (AlgHom.id R (FormalGroupAlgebra R I M)) x :=
  rfl

/-- **The crux of the left counit axiom**: `(ε ⊗̂ id) ∘ Δ = inr`. Both send `[g] ↦ inr [g]`. -/
theorem counitMap_comp_comul [TopologicalSpace R] [IsAdicRing I] :
    (CompletedTensorProduct.map hI (counitAlgHom R I M)
        (AlgHom.id R (FormalGroupAlgebra R I M))).comp (comul R I M hI) =
      (CompletedTensorProduct.inr R I R (FormalGroupAlgebra R I M)).toRingHom := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I R (FormalGroupAlgebra R I M))
      (CompletedTensorProduct R I R (FormalGroupAlgebra R I M)) :=
    (CompletedTensorProduct.isAdicRing R I R (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M))
      (CompletedTensorProduct R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I M
      (CompletedTensorProduct.idealOfDefinition R I R (FormalGroupAlgebra R I M))
      ((counitMapAlgHom R I M hI).comp (comulAlgHom R I M hI)) := by
    intro m x hx
    rw [AlgHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI (counitAlgHom R I M)
      (AlgHom.id R (FormalGroupAlgebra R I M)) m
      (isContinuousPoint_charEvalAlgHom R I M
        (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M))
        (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
        hI (comulChar R I M) m x hx)
  have hG : IsContinuousPoint R I M
      (CompletedTensorProduct.idealOfDefinition R I R (FormalGroupAlgebra R I M))
      (CompletedTensorProduct.inr R I R (FormalGroupAlgebra R I M)) := by
    intro m x hx
    rw [← FormalGroupAlgebra.mem_idealOfDefinition_pow_iff, idealOfDefinition_eq_map] at hx
    exact CompletedTensorProduct.inr_mem_pow m hx
  have hX : ∀ g : M, (counitMapAlgHom R I M hI).comp (comulAlgHom R I M hI) (X R I M g) =
      CompletedTensorProduct.inr R I R (FormalGroupAlgebra R I M) (X R I M g) := fun g => by
    rw [AlgHom.comp_apply, comulAlgHom_X, counitMapAlgHom_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, counitAlgHom_X,
      map_one, AlgHom.id_apply, one_mul]
  have key := point_ext R I M
    (CompletedTensorProduct.idealOfDefinition R I R (FormalGroupAlgebra R I M)) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

/-- **The left counit axiom of `D(M)`**: `unitEquiv ∘ (ε ⊗̂ id) ∘ Δ = id`. -/
theorem counit_law_left [TopologicalSpace R] [IsAdicRing I] :
    letI : IsAdicComplete (I.map (algebraMap R (FormalGroupAlgebra R I M)))
        (FormalGroupAlgebra R I M) := by
      rw [← idealOfDefinition_eq_map]
      exact (isAdicRing R I M hI).toIsAdicComplete
    (CompletedTensorProduct.unitEquiv hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (counitAlgHom R I M)
          (AlgHom.id R (FormalGroupAlgebra R I M))).comp (comul R I M hI)) =
      RingHom.id (FormalGroupAlgebra R I M) := by
  letI : IsAdicComplete (I.map (algebraMap R (FormalGroupAlgebra R I M)))
      (FormalGroupAlgebra R I M) := by
    rw [← idealOfDefinition_eq_map]
    exact (isAdicRing R I M hI).toIsAdicComplete
  rw [counitMap_comp_comul R I M hI]
  exact RingHom.ext fun a => CompletedTensorProduct.unitEquiv_inr hI a

/-- The composite `id ⊗̂ ε` applying the counit to the second tensor factor, bundled as an
`R`-algebra homomorphism `R⟨M⟩ ⊗̂_R R⟨M⟩ →ₐ[R] R⟨M⟩ ⊗̂_R R`. -/
def counitMapAlgHomRight [TopologicalSpace R] [IsAdicRing I] :
    tensorSquare R I M →ₐ[R]
      CompletedTensorProduct R I (FormalGroupAlgebra R I M) R where
  toRingHom := CompletedTensorProduct.map hI
    (AlgHom.id R (FormalGroupAlgebra R I M)) (counitAlgHom R I M)
  commutes' r := by
    have h : CompletedTensorProduct.map hI
        (AlgHom.id R (FormalGroupAlgebra R I M)) (counitAlgHom R I M)
        (algebraMap R (tensorSquare R I M) r) =
          algebraMap R (CompletedTensorProduct R I (FormalGroupAlgebra R I M) R) r := by
      rw [← (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M)).commutes r, CompletedTensorProduct.map_inl,
        (AlgHom.id R (FormalGroupAlgebra R I M)).commutes]
      exact (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) R).commutes r
    exact h

theorem counitMapAlgHomRight_apply [TopologicalSpace R] [IsAdicRing I] (x : tensorSquare R I M) :
    counitMapAlgHomRight R I M hI x =
      CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
        (counitAlgHom R I M) x :=
  rfl

/-- **The crux of the right counit axiom**: `(id ⊗̂ ε) ∘ Δ = inl`. Both send `[g] ↦ inl [g]`. -/
theorem counitMapRight_comp_comul [TopologicalSpace R] [IsAdicRing I] :
    (CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
        (counitAlgHom R I M)).comp (comul R I M hI) =
      (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) R).toRingHom := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M) R)
      (CompletedTensorProduct R I (FormalGroupAlgebra R I M) R) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M) R hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M))
      (CompletedTensorProduct R I (FormalGroupAlgebra R I M) (FormalGroupAlgebra R I M)) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I M
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M) R)
      ((counitMapAlgHomRight R I M hI).comp (comulAlgHom R I M hI)) := by
    intro m x hx
    rw [AlgHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI (AlgHom.id R (FormalGroupAlgebra R I M))
      (counitAlgHom R I M) m
      (isContinuousPoint_charEvalAlgHom R I M
        (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M))
        (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
        hI (comulChar R I M) m x hx)
  have hG : IsContinuousPoint R I M
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M) R)
      (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) R) := by
    intro m x hx
    rw [← FormalGroupAlgebra.mem_idealOfDefinition_pow_iff, idealOfDefinition_eq_map] at hx
    exact CompletedTensorProduct.inl_mem_pow m hx
  have hX : ∀ g : M, (counitMapAlgHomRight R I M hI).comp (comulAlgHom R I M hI) (X R I M g) =
      CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) R (X R I M g) := fun g => by
    rw [AlgHom.comp_apply, comulAlgHom_X, counitMapAlgHomRight_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, counitAlgHom_X,
      map_one, AlgHom.id_apply, mul_one]
  have key := point_ext R I M
    (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M) R) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

/-- **The right counit axiom of `D(M)`**: `rightUnitEquiv ∘ (id ⊗̂ ε) ∘ Δ = id`. -/
theorem counit_law_right [TopologicalSpace R] [IsAdicRing I] :
    letI : IsAdicComplete (I.map (algebraMap R (FormalGroupAlgebra R I M)))
        (FormalGroupAlgebra R I M) := by
      rw [← idealOfDefinition_eq_map]
      exact (isAdicRing R I M hI).toIsAdicComplete
    (CompletedTensorProduct.rightUnitEquiv hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
          (counitAlgHom R I M)).comp (comul R I M hI)) =
      RingHom.id (FormalGroupAlgebra R I M) := by
  letI : IsAdicComplete (I.map (algebraMap R (FormalGroupAlgebra R I M)))
      (FormalGroupAlgebra R I M) := by
    rw [← idealOfDefinition_eq_map]
    exact (isAdicRing R I M hI).toIsAdicComplete
  rw [counitMapRight_comp_comul R I M hI]
  exact RingHom.ext fun a => CompletedTensorProduct.rightUnitEquiv_inl hI a

/-!
### Coassociativity
-/

/-- The comultiplication tensored with the identity on the second factor, `Δ ⊗̂ id`. -/
def comulMapLeftAlgHom :
    tensorSquare R I M →ₐ[R]
      CompletedTensorProduct R I (tensorSquare R I M) (FormalGroupAlgebra R I M) :=
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (tensorSquare R I M)
        (FormalGroupAlgebra R I M))
      (CompletedTensorProduct R I (tensorSquare R I M) (FormalGroupAlgebra R I M)) :=
    (CompletedTensorProduct.isAdicRing R I (tensorSquare R I M)
      (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  CompletedTensorProduct.liftAlgHom
    (CompletedTensorProduct.idealOfDefinition R I (tensorSquare R I M) (FormalGroupAlgebra R I M))
    (le_of_eq CompletedTensorProduct.idealOfDefinition_eq_map.symm)
    ((CompletedTensorProduct.inl R I (tensorSquare R I M) (FormalGroupAlgebra R I M)).comp
      (comulAlgHom R I M hI))
    ((CompletedTensorProduct.inr R I (tensorSquare R I M) (FormalGroupAlgebra R I M)).comp
      (AlgHom.id R (FormalGroupAlgebra R I M)))

theorem comulMapLeftAlgHom_apply (x : tensorSquare R I M) :
    comulMapLeftAlgHom R I M hI x =
      CompletedTensorProduct.map hI (comulAlgHom R I M hI)
        (AlgHom.id R (FormalGroupAlgebra R I M)) x :=
  rfl

/-- The identity on the first factor tensored with the comultiplication, `id ⊗̂ Δ`. -/
def comulMapRightAlgHom :
    tensorSquare R I M →ₐ[R]
      CompletedTensorProduct R I (FormalGroupAlgebra R I M) (tensorSquare R I M) :=
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (tensorSquare R I M))
      (CompletedTensorProduct R I (FormalGroupAlgebra R I M) (tensorSquare R I M)) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (tensorSquare R I M) hI).toIsAdicComplete
  CompletedTensorProduct.liftAlgHom
    (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M) (tensorSquare R I M))
    (le_of_eq CompletedTensorProduct.idealOfDefinition_eq_map.symm)
    ((CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M) (tensorSquare R I M)).comp
      (AlgHom.id R (FormalGroupAlgebra R I M)))
    ((CompletedTensorProduct.inr R I (FormalGroupAlgebra R I M) (tensorSquare R I M)).comp
      (comulAlgHom R I M hI))

theorem comulMapRightAlgHom_apply (x : tensorSquare R I M) :
    comulMapRightAlgHom R I M hI x =
      CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
        (comulAlgHom R I M hI) x :=
  rfl

set_option maxHeartbeats 1000000 in
-- The composite runs through the triply-nested completed tensor products
-- `(R⟨M⟩ ⊗̂ R⟨M⟩) ⊗̂ R⟨M⟩`, whose `whnf`/`isDefEq` exceeds the default budget.
/-- **Coassociativity of the comultiplication of `D(M)`**: routing `(Δ ⊗̂ id) ∘ Δ` through the
associator agrees with `(id ⊗̂ Δ) ∘ Δ`. Both send `[g] ↦ [g] ⊗ [g] ⊗ [g]`. -/
theorem comul_coassoc :
    (CompletedTensorProduct.assocHom hI).comp
        ((CompletedTensorProduct.map hI (comulAlgHom R I M hI)
          (AlgHom.id R (FormalGroupAlgebra R I M))).comp (comul R I M hI)) =
      (CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
        (comulAlgHom R I M hI)).comp (comul R I M hI) := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (tensorSquare R I M) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (tensorSquare R I M)
        (FormalGroupAlgebra R I M))
      (CompletedTensorProduct R I (tensorSquare R I M) (FormalGroupAlgebra R I M)) :=
    (CompletedTensorProduct.isAdicRing R I (tensorSquare R I M)
      (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (tensorSquare R I M))
      (CompletedTensorProduct R I (FormalGroupAlgebra R I M) (tensorSquare R I M)) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (tensorSquare R I M) hI).toIsAdicComplete
  set L := CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
    (tensorSquare R I M)
  have hcomul : IsContinuousPoint R I M
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (comulAlgHom R I M hI) := fun m x hx =>
    isContinuousPoint_charEvalAlgHom R I M
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M))
      (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
      hI (comulChar R I M) m x hx
  have hF : IsContinuousPoint R I M L
      ((CompletedTensorProduct.assocAlgHom hI).comp
        ((comulMapLeftAlgHom R I M hI).comp (comulAlgHom R I M hI))) := by
    intro m x hx
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    exact CompletedTensorProduct.assocHom_mem_pow hI m
      (CompletedTensorProduct.map_mem_pow hI (comulAlgHom R I M hI)
        (AlgHom.id R (FormalGroupAlgebra R I M)) m (hcomul m x hx))
  have hG : IsContinuousPoint R I M L
      ((comulMapRightAlgHom R I M hI).comp (comulAlgHom R I M hI)) := by
    intro m x hx
    rw [AlgHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI (AlgHom.id R (FormalGroupAlgebra R I M))
      (comulAlgHom R I M hI) m (hcomul m x hx)
  have hX : ∀ g : M, (CompletedTensorProduct.assocAlgHom hI).comp
        ((comulMapLeftAlgHom R I M hI).comp (comulAlgHom R I M hI)) (X R I M g) =
      (comulMapRightAlgHom R I M hI).comp (comulAlgHom R I M hI) (X R I M g) := fun g => by
    simp only [AlgHom.comp_apply, comulAlgHom_X, comulMapLeftAlgHom_apply,
      comulMapRightAlgHom_apply, map_mul, CompletedTensorProduct.map_inl,
      CompletedTensorProduct.map_inr, AlgHom.id_apply,
      CompletedTensorProduct.assocAlgHom_apply, CompletedTensorProduct.assocHom_inl_inl,
      CompletedTensorProduct.assocHom_inl_inr, CompletedTensorProduct.assocHom_inr, mul_assoc]
  have key := point_ext R I M L hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

/-!
### The antipode axioms
-/

/-- The antipode applied to the first tensor factor, `S ⊗̂ id`. -/
def antipodeMapAlgHom : tensorSquare R I M →ₐ[R] tensorSquare R I M where
  toRingHom := CompletedTensorProduct.map hI (antipodeAlgHom R I M hI)
    (AlgHom.id R (FormalGroupAlgebra R I M))
  commutes' r := by
    have h : CompletedTensorProduct.map hI (antipodeAlgHom R I M hI)
        (AlgHom.id R (FormalGroupAlgebra R I M))
        (algebraMap R (tensorSquare R I M) r) = algebraMap R (tensorSquare R I M) r := by
      rw [← (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M)).commutes r, CompletedTensorProduct.map_inl,
        (antipodeAlgHom R I M hI).commutes]
    exact h

theorem antipodeMapAlgHom_apply (x : tensorSquare R I M) :
    antipodeMapAlgHom R I M hI x =
      CompletedTensorProduct.map hI (antipodeAlgHom R I M hI)
        (AlgHom.id R (FormalGroupAlgebra R I M)) x :=
  rfl

/-- The antipode applied to the second tensor factor, `id ⊗̂ S`. -/
def antipodeMapAlgHomRight : tensorSquare R I M →ₐ[R] tensorSquare R I M where
  toRingHom := CompletedTensorProduct.map hI
    (AlgHom.id R (FormalGroupAlgebra R I M)) (antipodeAlgHom R I M hI)
  commutes' r := by
    have h : CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
        (antipodeAlgHom R I M hI)
        (algebraMap R (tensorSquare R I M) r) = algebraMap R (tensorSquare R I M) r := by
      rw [← (CompletedTensorProduct.inl R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M)).commutes r, CompletedTensorProduct.map_inl,
        (AlgHom.id R (FormalGroupAlgebra R I M)).commutes]
    exact h

theorem antipodeMapAlgHomRight_apply (x : tensorSquare R I M) :
    antipodeMapAlgHomRight R I M hI x =
      CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
        (antipodeAlgHom R I M hI) x :=
  rfl

/-- Continuity of the trivial endomorphism `η ∘ ε` used in both antipode laws. -/
theorem isContinuousPoint_algebraMap_comp_counit (hI : I.FG) [TopologicalSpace R] [IsAdicRing I] :
    IsContinuousPoint R I M (idealOfDefinition R I M)
      ((Algebra.ofId R (FormalGroupAlgebra R I M)).comp (counitAlgHom R I M)) := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  intro m x hx
  rw [AlgHom.comp_apply]
  have hc : counitAlgHom R I M x ∈ I ^ m :=
    isContinuousPoint_charEvalAlgHom R I M I (le_of_eq (Ideal.map_id I)) hI 1 m x hx
  rw [idealOfDefinition_eq_map]
  have hmem : (algebraMap R (FormalGroupAlgebra R I M)) (counitAlgHom R I M x) ∈
      (I ^ m).map (algebraMap R (FormalGroupAlgebra R I M)) :=
    Ideal.mem_map_of_mem _ hc
  rwa [Ideal.map_pow] at hmem

set_option maxHeartbeats 800000 in
-- The `point_ext` comparison unfolds the convolution through the nested completed tensor square
-- `R⟨M⟩ ⊗̂ R⟨M⟩`, whose `whnf`/`isDefEq` exceeds the default heartbeat budget.
/-- **The (left) antipode axiom of `D(M)`**: `∇ ∘ (S ⊗̂ id) ∘ Δ = η ∘ ε`, expressing
`[-g] · [g] = 1`. -/
theorem antipode_law_left [TopologicalSpace R] [IsAdicRing I] :
    (mulAlgHom R I M hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (antipodeAlgHom R I M hI)
          (AlgHom.id R (FormalGroupAlgebra R I M))).comp (comul R I M hI)) =
      (algebraMap R (FormalGroupAlgebra R I M)).comp (counit R I M) := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (tensorSquare R I M) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I M (idealOfDefinition R I M)
      ((mulAlgHom R I M hI).comp
        ((antipodeMapAlgHom R I M hI).comp (comulAlgHom R I M hI))) := by
    intro m x hx
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    refine mulAlgHom_mem_pow R I M hI m ?_
    rw [antipodeMapAlgHom_apply]
    exact CompletedTensorProduct.map_mem_pow hI (antipodeAlgHom R I M hI)
      (AlgHom.id R (FormalGroupAlgebra R I M)) m
      (isContinuousPoint_charEvalAlgHom R I M
        (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M))
        (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
        hI (comulChar R I M) m x hx)
  have hG := isContinuousPoint_algebraMap_comp_counit R I M hI
  have hX : ∀ g : M, (mulAlgHom R I M hI).comp
        ((antipodeMapAlgHom R I M hI).comp (comulAlgHom R I M hI)) (X R I M g) =
      (Algebra.ofId R (FormalGroupAlgebra R I M)).comp (counitAlgHom R I M) (X R I M g) :=
    fun g => by
    simp only [AlgHom.comp_apply, comulAlgHom_X, antipodeMapAlgHom_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, antipodeAlgHom_X,
      AlgHom.id_apply, mulAlgHom_inl, mulAlgHom_inr, counitAlgHom_X, map_one]
    rw [mul_comm (X R I M (-g)) (X R I M g), X_mul_X_neg]
  have key := point_ext R I M (idealOfDefinition R I M) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

set_option maxHeartbeats 800000 in
-- The `point_ext` comparison unfolds the convolution through the nested completed tensor square
-- `R⟨M⟩ ⊗̂ R⟨M⟩`, whose `whnf`/`isDefEq` exceeds the default heartbeat budget.
/-- **The (right) antipode axiom of `D(M)`**: `∇ ∘ (id ⊗̂ S) ∘ Δ = η ∘ ε`, mirroring
`antipode_law_left`. -/
theorem antipode_law_right [TopologicalSpace R] [IsAdicRing I] :
    (mulAlgHom R I M hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (AlgHom.id R (FormalGroupAlgebra R I M))
          (antipodeAlgHom R I M hI)).comp (comul R I M hI)) =
      (algebraMap R (FormalGroupAlgebra R I M)).comp (counit R I M) := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  haveI : IsAdicComplete (idealOfDefinition R I M) (FormalGroupAlgebra R I M) :=
    (isAdicRing R I M hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
        (FormalGroupAlgebra R I M)) (tensorSquare R I M) :=
    (CompletedTensorProduct.isAdicRing R I (FormalGroupAlgebra R I M)
      (FormalGroupAlgebra R I M) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I M (idealOfDefinition R I M)
      ((mulAlgHom R I M hI).comp
        ((antipodeMapAlgHomRight R I M hI).comp (comulAlgHom R I M hI))) := by
    intro m x hx
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    refine mulAlgHom_mem_pow R I M hI m ?_
    rw [antipodeMapAlgHomRight_apply]
    exact CompletedTensorProduct.map_mem_pow hI (AlgHom.id R (FormalGroupAlgebra R I M))
      (antipodeAlgHom R I M hI) m
      (isContinuousPoint_charEvalAlgHom R I M
        (CompletedTensorProduct.idealOfDefinition R I (FormalGroupAlgebra R I M)
          (FormalGroupAlgebra R I M))
        (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
        hI (comulChar R I M) m x hx)
  have hG := isContinuousPoint_algebraMap_comp_counit R I M hI
  have hX : ∀ g : M, (mulAlgHom R I M hI).comp
        ((antipodeMapAlgHomRight R I M hI).comp (comulAlgHom R I M hI)) (X R I M g) =
      (Algebra.ofId R (FormalGroupAlgebra R I M)).comp (counitAlgHom R I M) (X R I M g) :=
    fun g => by
    simp only [AlgHom.comp_apply, comulAlgHom_X, antipodeMapAlgHomRight_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, antipodeAlgHom_X,
      AlgHom.id_apply, mulAlgHom_inl, mulAlgHom_inr, counitAlgHom_X, map_one]
    rw [X_mul_X_neg]
  have key := point_ext R I M (idealOfDefinition R I M) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

end Group

end FormalGroupAlgebra

end
