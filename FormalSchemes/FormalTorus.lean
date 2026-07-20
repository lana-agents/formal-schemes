import FormalSchemes.RestrictedPowerSeries
import FormalSchemes.AdicExtend
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Data.Int.Cast.Lemmas

set_option linter.style.header false

/-!
# Formal group algebras, the formal multiplicative group and formal tori

Over an adic ring `R` with ideal of definition `I`, and a discrete abelian group `M`, the
**formal group algebra** `R⟨M⟩` is the `I`-adic completion of the group algebra `R[M]`. Its
formal spectrum is the *formal diagonalizable group* `D(M)` with character group `M`. Two special
cases are the ones the Tate construction cares about (Bosch, *Lectures on Formal and Rigid
Geometry*, §8):

* `M = ℤ` gives the **formal multiplicative group** `Ĝm = Spf R{X, X⁻¹}` (cf.
  `FormalSchemes/FormalGm.lean`, which develops this case with its full Hopf-algebra structure);
* `M = ℤʳ = (Fin r →₀ ℤ)` gives the **formal torus** `Ĝm^r = Spf R{X₁^±, …, Xᵣ^±}`.

This file generalizes the *functor of points* half of `FormalGm.lean` from `ℤ` to an arbitrary
discrete abelian group `M`, and specializes it to tori.

Following the design of `FormalSchemes/RestrictedPowerSeries.lean` and `FormalSchemes/FormalGm.lean`
we define `R⟨M⟩` directly as `AdicCompletion (I·R[M]) R[M]`; the general completion machinery makes
it a complete adic ring for the extension of `I` (no finiteness beyond `I.FG`, no closedness
hypotheses), and the formal group algebra is its formal spectrum.

For the functor of points, the key construction is **evaluation at a character**: a group
homomorphism `χ : Multiplicative M →* Sˣ` into the units of a complete adic `R`-algebra `S`
determines a continuous homomorphism `R⟨M⟩ →+* S` sending the group-like element `[g]` to `χ g`
(`FormalGroupAlgebra.charEval`), via group-algebra evaluation `AddMonoidAlgebra.lift` extended to
the completion by `AdicCompletion.extendRingHom`. The main result
`FormalGroupAlgebra.pointsEquivChars` identifies the continuous points of `Spf R⟨M⟩` in `S` with
the character group `Multiplicative M →* Sˣ`; for `M = ℤʳ` this becomes
`FormalTorus.pointsEquivPiUnits : {points} ≃ (Fin r → Sˣ)`, the `r`-fold product of the unit group,
exactly Bosch's description of `Ĝm^r` as `(Ĝm)ʳ`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §8.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
-/

noncomputable section

open Ideal AddMonoidAlgebra

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (M : Type) [AddCommGroup M]

/-- The **formal group algebra** `R⟨M⟩`: the `I`-adic completion of the group algebra `R[M]`.
Its formal spectrum is the formal diagonalizable group with character group `M`. -/
abbrev FormalGroupAlgebra : Type u :=
  AdicCompletion (I.map (algebraMap R (AddMonoidAlgebra R M))) (AddMonoidAlgebra R M)

namespace FormalGroupAlgebra

/-- The ideal of definition of `R⟨M⟩`: the extension of `I·R[M]` to the completion. -/
abbrev idealOfDefinition : Ideal (FormalGroupAlgebra R I M) :=
  (I.map (algebraMap R (AddMonoidAlgebra R M))).map
    (algebraMap (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M))

/-- The ideal of definition of `R⟨M⟩` is the extension of `I` itself. -/
theorem idealOfDefinition_eq_map :
    idealOfDefinition R I M = I.map (algebraMap R (FormalGroupAlgebra R I M)) := by
  change (I.map (algebraMap R (AddMonoidAlgebra R M))).map
    (algebraMap (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M)) = _
  rw [Ideal.map_map]
  congr 1

/-- The formal group algebra is a complete adic ring (`I` finitely generated). -/
theorem isAdicRing (hI : I.FG) : IsAdicRing (idealOfDefinition R I M) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

/-- Membership in the powers of the ideal of definition, expressed through the module filtration
`(I·R[M]) ^ m • ⊤` used by the completion API. -/
theorem mem_idealOfDefinition_pow_iff (m : ℕ) (x : FormalGroupAlgebra R I M) :
    x ∈ (idealOfDefinition R I M) ^ m ↔
      x ∈ ((I.map (algebraMap R (AddMonoidAlgebra R M))) ^ m • ⊤ :
        Submodule (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M)) := by
  rw [← Ideal.mem_map_pow_iff_mem_smul_top (I.map (algebraMap R (AddMonoidAlgebra R M))) m x,
    idealOfDefinition, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Algebra.algebraMap_self, Ideal.map_id]

/-- The **group-like element** `[g]` of `R⟨M⟩` attached to `g : M`. -/
def X (g : M) : FormalGroupAlgebra R I M :=
  AdicCompletion.of (I.map (algebraMap R (AddMonoidAlgebra R M))) (AddMonoidAlgebra R M)
    (single g 1)

/-- The group-like element `[g]` is the image of `single g 1` under the structure map. -/
theorem X_eq_algebraMap (g : M) :
    X R I M g = algebraMap (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M) (single g 1) := by
  rw [X, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- `[0] = 1`: the group-like element at the identity is the unit. -/
theorem X_zero : X R I M 0 = 1 := by
  rw [X_eq_algebraMap, ← AddMonoidAlgebra.one_def, map_one]

/-- `[g + g'] = [g] · [g']`: the group-likes are multiplicative. -/
theorem X_add (g g' : M) : X R I M (g + g') = X R I M g * X R I M g' := by
  rw [X_eq_algebraMap, X_eq_algebraMap, X_eq_algebraMap, ← map_mul, single_mul_single, mul_one]

/-- `[g] · [-g] = 1`: the group-like elements are units. -/
theorem X_mul_X_neg (g : M) : X R I M g * X R I M (-g) = 1 := by
  rw [← X_add, add_neg_cancel, X_zero]

/-- Each group-like element `[g]` is a unit. -/
theorem isUnit_X (g : M) : IsUnit (X R I M g) :=
  ⟨Units.mkOfMulEqOne (X R I M g) (X R I M (-g)) (X_mul_X_neg R I M g), rfl⟩

end FormalGroupAlgebra

/-- The **formal group algebra scheme** `D(M) = Spf R⟨M⟩` over an adic ring `R` with finitely
generated ideal of definition `I`, as a formal scheme. -/
def formalGroupAlgebra (hI : I.FG) : AlgebraicGeometry.FormalScheme :=
  haveI := FormalGroupAlgebra.isAdicRing R I M hI
  AlgebraicGeometry.FormalScheme.Spf (FormalGroupAlgebra.idealOfDefinition R I M)

namespace FormalGroupAlgebra

/-!
### Points of `D(M)`: evaluation at characters
-/

section Points

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)

/-- Evaluation of the group algebra at a character `χ`: the `R`-algebra homomorphism
`R[M] →ₐ[R] S` sending the group-like `[g] ↦ χ g`. -/
def charEvalPoly (χ : Multiplicative M →* Sˣ) : AddMonoidAlgebra R M →ₐ[R] S :=
  AddMonoidAlgebra.lift R S M ((Units.coeHom S).comp χ)

@[simp]
theorem charEvalPoly_single (χ : Multiplicative M →* Sˣ) (g : M) :
    charEvalPoly R M χ (single g 1) = ((χ (Multiplicative.ofAdd g) : Sˣ) : S) := by
  rw [charEvalPoly, AddMonoidAlgebra.lift_single]
  simp

/-- **Evaluation of the formal group algebra at a character**: a group homomorphism
`χ : Multiplicative M →* Sˣ` into the units of a complete adic `R`-algebra `S` determines a
continuous homomorphism from `R⟨M⟩` — a point of the formal diagonalizable group. -/
def charEval (χ : Multiplicative M →* Sˣ) : FormalGroupAlgebra R I M →+* S :=
  AdicCompletion.extendRingHom (I.map (algebraMap R (AddMonoidAlgebra R M))) L
    (charEvalPoly R M χ).toRingHom
    (Ideal.map_algebraMap_pow_le_comap I L hIL (charEvalPoly R M χ))

/-- The point attached to a character `χ` sends the group-like `[g]` to `χ g`. -/
theorem charEval_X (χ : Multiplicative M →* Sˣ) (g : M) :
    charEval R I M L hIL χ (X R I M g) = ((χ (Multiplicative.ofAdd g) : Sˣ) : S) := by
  rw [charEval, X, AdicCompletion.extendRingHom_of]
  exact charEvalPoly_single R M χ g

/-- The canonical `R`-algebra homomorphism from the group algebra into `R⟨M⟩`. -/
def ofAlgHom : AddMonoidAlgebra R M →ₐ[R] FormalGroupAlgebra R I M where
  toRingHom := algebraMap (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M)
  commutes' r := by
    change algebraMap (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M)
      (algebraMap R (AddMonoidAlgebra R M) r) = algebraMap R (FormalGroupAlgebra R I M) r
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.algebraMap_apply]

theorem ofAlgHom_apply (b : AddMonoidAlgebra R M) :
    ofAlgHom R I M b =
      AdicCompletion.of (I.map (algebraMap R (AddMonoidAlgebra R M))) (AddMonoidAlgebra R M) b := by
  change algebraMap (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M) b = _
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem ofAlgHom_single (g : M) : ofAlgHom R I M (single g 1) = X R I M g := by
  rw [ofAlgHom_apply, X]

section Points2

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)

/-- A **continuous point** of `D(M)` in a complete adic `R`-algebra `S`: an `R`-algebra
homomorphism from `R⟨M⟩` mapping the filtration into the powers of `L`. -/
def IsContinuousPoint (F : FormalGroupAlgebra R I M →ₐ[R] S) : Prop :=
  ∀ (m : ℕ) (x : FormalGroupAlgebra R I M),
    x ∈ ((I.map (algebraMap R (AddMonoidAlgebra R M))) ^ m • ⊤ :
      Submodule (AddMonoidAlgebra R M) (FormalGroupAlgebra R I M)) → F x ∈ L ^ m

/-- Evaluation at a character, bundled as an `R`-algebra homomorphism. -/
def charEvalAlgHom (χ : Multiplicative M →* Sˣ) : FormalGroupAlgebra R I M →ₐ[R] S where
  toRingHom := charEval R I M L hIL χ
  commutes' r := by
    change charEval R I M L hIL χ (algebraMap R (FormalGroupAlgebra R I M) r) = algebraMap R S r
    have h : algebraMap R (FormalGroupAlgebra R I M) r =
        AdicCompletion.of (I.map (algebraMap R (AddMonoidAlgebra R M))) (AddMonoidAlgebra R M)
          (algebraMap R (AddMonoidAlgebra R M) r) :=
      AdicCompletion.algebraMap_apply _ r
    rw [h, charEval, AdicCompletion.extendRingHom_of]
    exact (charEvalPoly R M χ).commutes r

theorem charEvalAlgHom_X (χ : Multiplicative M →* Sˣ) (g : M) :
    charEvalAlgHom R I M L hIL χ (X R I M g) = ((χ (Multiplicative.ofAdd g) : Sˣ) : S) :=
  charEval_X R I M L hIL χ g

/-- Evaluation at a character is a continuous point. -/
theorem isContinuousPoint_charEvalAlgHom (hI : I.FG) (χ : Multiplicative M →* Sˣ) :
    IsContinuousPoint R I M L (charEvalAlgHom R I M L hIL χ) := fun m x hx =>
  AdicCompletion.extendRingHom_continuous _ L _ _ (hI.map _) m x hx

/-- The **character attached to a continuous point**: the group homomorphism sending `g` to the
unit `F [g]` (invertible with inverse `F [-g]`). -/
def pointChar (F : FormalGroupAlgebra R I M →ₐ[R] S) : Multiplicative M →* Sˣ where
  toFun g :=
    Units.mkOfMulEqOne (F (X R I M g.toAdd)) (F (X R I M (-g.toAdd))) (by
      rw [← map_mul, X_mul_X_neg, map_one])
  map_one' := by
    apply Units.ext
    change F (X R I M (0 : M)) = (1 : S)
    rw [X_zero, map_one]
  map_mul' g g' := by
    apply Units.ext
    change F (X R I M (g.toAdd + g'.toAdd)) = F (X R I M g.toAdd) * F (X R I M g'.toAdd)
    rw [X_add, map_mul]

@[simp]
theorem pointChar_val (F : FormalGroupAlgebra R I M →ₐ[R] S) (g : Multiplicative M) :
    (pointChar R I M F g : S) = F (X R I M g.toAdd) :=
  rfl

/-- **Continuous points are determined by their values on the group-like elements** — the
uniqueness half of the functor-of-points description of `D(M)`. -/
theorem point_ext (hI : I.FG) {F G : FormalGroupAlgebra R I M →ₐ[R] S}
    (hF : IsContinuousPoint R I M L F) (hG : IsContinuousPoint R I M L G)
    (h : ∀ g : M, F (X R I M g) = G (X R I M g)) : F = G := by
  have halg : F.comp (ofAlgHom R I M) = G.comp (ofAlgHom R I M) := by
    refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
    simp only [AlgHom.comp_apply, ofAlgHom_single]
    exact h g
  have hring : F.toRingHom = G.toRingHom := by
    refine AdicCompletion.hom_ext_of_continuous _ L (hI.map _) hF hG fun b => ?_
    have hb := congrArg (fun (φ : AddMonoidAlgebra R M →ₐ[R] S) => φ b) halg
    simpa [ofAlgHom_apply] using hb
  exact AlgHom.ext fun x => DFunLike.congr_fun hring x

/-- **The functor of points of the formal group algebra**: continuous points of `D(M) = Spf R⟨M⟩`
in a complete adic `R`-algebra `S` correspond to characters `Multiplicative M →* Sˣ`. For `M = ℤ`
this is the functor of points of the formal multiplicative group (Bosch, §8). -/
def pointsEquivChars (hI : I.FG) :
    { F : FormalGroupAlgebra R I M →ₐ[R] S // IsContinuousPoint R I M L F } ≃
      (Multiplicative M →* Sˣ) where
  toFun F := pointChar R I M F.1
  invFun χ := ⟨charEvalAlgHom R I M L hIL χ, isContinuousPoint_charEvalAlgHom R I M L hIL hI χ⟩
  left_inv F := by
    refine Subtype.ext ?_
    refine point_ext R I M L hI
      (isContinuousPoint_charEvalAlgHom R I M L hIL hI _) F.2 fun g => ?_
    rw [charEvalAlgHom_X]
    exact (pointChar_val R I M F.1 (Multiplicative.ofAdd g)).symm
  right_inv χ := by
    refine MonoidHom.ext fun g => ?_
    apply Units.ext
    rw [pointChar_val, charEvalAlgHom_X, ofAdd_toAdd]

end Points2

end Points

end FormalGroupAlgebra

/-!
## Formal tori
-/

namespace FormalTorus

open FormalGroupAlgebra

variable (r : ℕ)

/-- The **formal torus** `Ĝm^r = Spf R{X₁^±, …, Xᵣ^±}` of rank `r` over an adic ring `R` with
finitely generated ideal of definition `I`: the formal group algebra of the character lattice
`ℤʳ = Fin r →₀ ℤ`. -/
def formalTorus (hI : I.FG) : AlgebraicGeometry.FormalScheme :=
  formalGroupAlgebra R I (Fin r →₀ ℤ) hI

section Points

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)

/-- Characters of the rank-`r` lattice `ℤʳ` correspond to `r`-tuples of units, by evaluating a
character on the `r` coordinate generators. This is the group-theoretic input identifying the
formal torus with the `r`-fold product of formal multiplicative groups. -/
def charsEquivPi : (Multiplicative (Fin r →₀ ℤ) →* Sˣ) ≃ (Fin r → Sˣ) :=
  (AddMonoidHom.toMultiplicativeLeft (α := Fin r →₀ ℤ) (β := Sˣ)).symm.trans <|
    (Finsupp.liftAddHom (α := Fin r) (M := ℤ) (N := Additive Sˣ)).toEquiv.symm.trans <|
      Equiv.piCongrRight fun _ =>
        (zmultiplesHom (Additive Sˣ)).symm.trans Additive.toMul

@[simp]
theorem charsEquivPi_apply (χ : Multiplicative (Fin r →₀ ℤ) →* Sˣ) (i : Fin r) :
    charsEquivPi r χ i = χ (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) :=
  rfl

/-- **The functor of points of the formal torus** (Bosch, §8): continuous points of `Ĝm^r` in a
complete adic `R`-algebra `S` correspond to `r`-tuples of units of `S`, i.e. `Ĝm^r` is the `r`-fold
product of the formal multiplicative group. -/
def pointsEquivPiUnits (hI : I.FG) :
    { F : FormalGroupAlgebra R I (Fin r →₀ ℤ) →ₐ[R] S //
        IsContinuousPoint R I (Fin r →₀ ℤ) L F } ≃ (Fin r → Sˣ) :=
  (pointsEquivChars R I (Fin r →₀ ℤ) L hIL hI).trans (charsEquivPi r)

end Points

end FormalTorus

end
