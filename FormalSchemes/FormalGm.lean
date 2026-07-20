import FormalSchemes.RestrictedPowerSeries
import FormalSchemes.AdicExtend
import FormalSchemes.CompletedTensor
import Mathlib.Algebra.Polynomial.Laurent

set_option linter.style.header false

/-!
# The formal multiplicative group

Over an adic ring `R` with ideal of definition `I`, the **formal multiplicative group** is
`Ĝm = Spf R{X, X⁻¹}`, where `R{X, X⁻¹}` is the `I`-adic completion of the Laurent polynomial
ring `R[T, T⁻¹]` (Bosch, *Lectures on Formal and Rigid Geometry*, §8). It is the ambient
formal group in which the period lattice `q^ℤ` of the Tate curve sits.

Following the design of `FormalSchemes/RestrictedPowerSeries.lean`, we define
`RestrictedLaurentSeries R I` directly as `AdicCompletion (I·R[T,T⁻¹]) R[T,T⁻¹]`; the general
completion machinery then makes it a complete adic ring for the extension of `I` (no
finiteness beyond `I.FG`, no closedness hypotheses), and `Ĝm` is the formal spectrum.

For the functor of points, the key construction is **evaluation at a unit**: a unit `u` of a
complete adic `R`-algebra `S` determines a continuous homomorphism `R{X,X⁻¹} →+* S` sending
`X ↦ u` (`RestrictedLaurentSeries.unitEval`), via Laurent-polynomial evaluation
`AddMonoidAlgebra.lift` at the group homomorphism `ℤ → Sˣ, n ↦ uⁿ`, extended to the completion
by `AdicCompletion.extendRingHom`. The inverse direction of the functor-of-points bijection
(every continuous point comes from the unit `image of X`) and the group-object structure
(comultiplication through the completed tensor product) are left to the follow-up parts of
this issue.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §8.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
-/

noncomputable section

open Ideal LaurentPolynomial

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The ring of **restricted Laurent series** `R{X, X⁻¹}`: the `I`-adic completion of the
Laurent polynomial ring. Its formal spectrum is the formal multiplicative group over `R`. -/
abbrev RestrictedLaurentSeries : Type u :=
  AdicCompletion (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R)

namespace RestrictedLaurentSeries

/-- The ideal of definition of `R{X, X⁻¹}`: the extension of `I·R[T,T⁻¹]` to the
completion. -/
abbrev idealOfDefinition : Ideal (RestrictedLaurentSeries R I) :=
  (I.map (algebraMap R (LaurentPolynomial R))).map
    (algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I))

/-- The ideal of definition of `R{X, X⁻¹}` is the extension of `I` itself. -/
theorem idealOfDefinition_eq_map :
    idealOfDefinition R I = I.map (algebraMap R (RestrictedLaurentSeries R I)) := by
  change (I.map (algebraMap R (LaurentPolynomial R))).map
    (algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I)) = _
  rw [Ideal.map_map]
  congr 1

/-- The restricted Laurent series ring is a complete adic ring (`I` finitely generated). -/
theorem isAdicRing (hI : I.FG) : IsAdicRing (idealOfDefinition R I) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

/-- The image of the Laurent variable `T ^ n` in the restricted Laurent series ring. -/
def X (n : ℤ) : RestrictedLaurentSeries R I :=
  AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R) (T n)

/-- The variable of `R{X, X⁻¹}` is a unit (with inverse the image of `T⁻¹`). -/
theorem isUnit_X (n : ℤ) : IsUnit (X R I n) := by
  have h : X R I n =
      algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I) (T n) := by
    rw [X, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h]
  exact (isUnit_T n).map (algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I))

end RestrictedLaurentSeries

/-- The **formal multiplicative group** `Ĝm = Spf R{X, X⁻¹}` over an adic ring `R` with
finitely generated ideal of definition `I`, as a formal scheme (Bosch, §8). -/
def formalGm (hI : I.FG) : AlgebraicGeometry.FormalScheme :=
  haveI := RestrictedLaurentSeries.isAdicRing R I hI
  AlgebraicGeometry.FormalScheme.Spf (RestrictedLaurentSeries.idealOfDefinition R I)

namespace RestrictedLaurentSeries

/-!
### Points of `Ĝm`: evaluation at units
-/

section Points

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)

/-- Evaluation of Laurent polynomials at a unit `u`: the `R`-algebra homomorphism
`R[T, T⁻¹] →ₐ[R] S` sending `T ^ n ↦ uⁿ`. -/
def laurentEval (u : Sˣ) : LaurentPolynomial R →ₐ[R] S :=
  AddMonoidAlgebra.lift R S ℤ ((Units.coeHom S).comp (zpowersHom Sˣ u))

@[simp]
theorem laurentEval_T (u : Sˣ) (n : ℤ) : laurentEval R (u := u) (T n) = ((u ^ n : Sˣ) : S) := by
  simp only [laurentEval, T]
  rw [AddMonoidAlgebra.lift_single]
  simp

/-- **Evaluation of restricted Laurent series at a unit**: a unit of a complete adic
`R`-algebra determines a continuous homomorphism from `R{X, X⁻¹}` — a point of the formal
multiplicative group. -/
def unitEval (u : Sˣ) : RestrictedLaurentSeries R I →+* S :=
  AdicCompletion.extendRingHom (I.map (algebraMap R (LaurentPolynomial R))) L
    (laurentEval R (u := u)).toRingHom
    (Ideal.map_algebraMap_pow_le_comap I L hIL (laurentEval R (u := u)))

/-- The point attached to a unit `u` sends the variable `X` to `u`. -/
theorem unitEval_X (u : Sˣ) (n : ℤ) :
    unitEval R I L hIL u (X R I n) = ((u ^ n : Sˣ) : S) := by
  rw [unitEval, X, AdicCompletion.extendRingHom_of]
  exact laurentEval_T R u n

/-- The canonical `R`-algebra homomorphism from Laurent polynomials into the restricted
Laurent series. -/
def ofAlgHom : LaurentPolynomial R →ₐ[R] RestrictedLaurentSeries R I where
  toRingHom := algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I)
  commutes' r := by
    change algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I)
      (algebraMap R (LaurentPolynomial R) r) = algebraMap R (RestrictedLaurentSeries R I) r
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.algebraMap_apply]

theorem ofAlgHom_apply (b : LaurentPolynomial R) :
    ofAlgHom R I b =
      AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R) b := by
  change algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I) b = _
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- `R`-algebra homomorphisms out of the Laurent polynomial ring are determined by the image
of the variable `T`. -/
theorem laurentAlgHom_ext {S : Type u} [CommRing S] [Algebra R S]
    {G₁ G₂ : LaurentPolynomial R →ₐ[R] S} (h : G₁ (T 1) = G₂ (T 1)) : G₁ = G₂ := by
  have h1 : (AddMonoidAlgebra.lift R S ℤ).symm G₁ = (AddMonoidAlgebra.lift R S ℤ).symm G₂ := by
    refine MonoidHom.ext_mint ?_
    rw [AddMonoidAlgebra.lift_symm_apply, AddMonoidAlgebra.lift_symm_apply]
    exact h
  calc G₁ = AddMonoidAlgebra.lift R S ℤ ((AddMonoidAlgebra.lift R S ℤ).symm G₁) :=
        ((AddMonoidAlgebra.lift R S ℤ).apply_symm_apply G₁).symm
    _ = AddMonoidAlgebra.lift R S ℤ ((AddMonoidAlgebra.lift R S ℤ).symm G₂) := by rw [h1]
    _ = G₂ := (AddMonoidAlgebra.lift R S ℤ).apply_symm_apply G₂

section Points2

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)

/-- A **continuous point** of `Ĝm` in a complete adic `R`-algebra `S`: an `R`-algebra
homomorphism from `R{X, X⁻¹}` mapping the filtration into the powers of `L`. -/
def IsContinuousPoint (F : RestrictedLaurentSeries R I →ₐ[R] S) : Prop :=
  ∀ (m : ℕ) (x : RestrictedLaurentSeries R I),
    x ∈ ((I.map (algebraMap R (LaurentPolynomial R))) ^ m • ⊤ :
      Submodule (LaurentPolynomial R) (RestrictedLaurentSeries R I)) → F x ∈ L ^ m

/-- The evaluation at a unit, bundled as an `R`-algebra homomorphism. -/
def unitEvalAlgHom (u : Sˣ) : RestrictedLaurentSeries R I →ₐ[R] S where
  toRingHom := unitEval R I L hIL u
  commutes' r := by
    change unitEval R I L hIL u (algebraMap R (RestrictedLaurentSeries R I) r) =
      algebraMap R S r
    have h : algebraMap R (RestrictedLaurentSeries R I) r =
        AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R)))
          (LaurentPolynomial R) (algebraMap R (LaurentPolynomial R) r) :=
      AdicCompletion.algebraMap_apply _ r
    rw [h, unitEval, AdicCompletion.extendRingHom_of]
    exact (laurentEval R (u := u)).commutes r

theorem unitEvalAlgHom_X (u : Sˣ) (n : ℤ) :
    unitEvalAlgHom R I L hIL u (X R I n) = ((u ^ n : Sˣ) : S) :=
  unitEval_X R I L hIL u n

/-- Evaluation at a unit is a continuous point. -/
theorem isContinuousPoint_unitEvalAlgHom (hI : I.FG) (u : Sˣ) :
    IsContinuousPoint R I L (unitEvalAlgHom R I L hIL u) := fun m x hx =>
  AdicCompletion.extendRingHom_continuous _ L _ _ (hI.map _) m x hx

/-- The unit attached to a continuous point: the image of the variable, invertible with
inverse the image of `X⁻¹`. -/
def pointUnit (F : RestrictedLaurentSeries R I →ₐ[R] S) : Sˣ :=
  Units.mkOfMulEqOne (F (X R I 1)) (F (X R I (-1))) (by
    rw [← map_mul]
    have hX : X R I 1 * X R I (-1) = 1 := by
      change algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I) (T 1) *
        algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I) (T (-1)) = 1
      rw [← map_mul, ← T_add]
      norm_num [T_zero]
    rw [hX, map_one])

@[simp]
theorem pointUnit_coe (F : RestrictedLaurentSeries R I →ₐ[R] S) :
    (pointUnit R I F : S) = F (X R I 1) :=
  rfl

/-- **Continuous points are determined by the image of the variable** — the uniqueness half of
the functor-of-points description of `Ĝm`. -/
theorem point_ext (hI : I.FG) {F G : RestrictedLaurentSeries R I →ₐ[R] S}
    (hF : IsContinuousPoint R I L F) (hG : IsContinuousPoint R I L G)
    (h : F (X R I 1) = G (X R I 1)) : F = G := by
  have hlaurent : F.comp (ofAlgHom R I) = G.comp (ofAlgHom R I) := by
    refine laurentAlgHom_ext R ?_
    simp only [AlgHom.comp_apply, ofAlgHom_apply]
    exact h
  have hring : F.toRingHom = G.toRingHom := by
    refine AdicCompletion.hom_ext_of_continuous _ L (hI.map _) hF hG fun b => ?_
    have hb := congrArg (fun (φ : LaurentPolynomial R →ₐ[R] S) => φ b) hlaurent
    simpa [ofAlgHom_apply] using hb
  exact AlgHom.ext fun x => DFunLike.congr_fun hring x

/-- **The functor of points of the formal multiplicative group** (Bosch, §8): continuous
points of `Ĝm` in a complete adic `R`-algebra `S` correspond to units of `S`. -/
def pointsEquivUnits (hI : I.FG) :
    { F : RestrictedLaurentSeries R I →ₐ[R] S // IsContinuousPoint R I L F } ≃ Sˣ where
  toFun F := pointUnit R I F.1
  invFun u := ⟨unitEvalAlgHom R I L hIL u, isContinuousPoint_unitEvalAlgHom R I L hIL hI u⟩
  left_inv F := by
    refine Subtype.ext ?_
    refine (point_ext R I L hI (isContinuousPoint_unitEvalAlgHom R I L hIL hI _) F.2 ?_)
    rw [unitEvalAlgHom_X]
    simp
  right_inv u := by
    refine Units.ext ?_
    rw [pointUnit_coe, unitEvalAlgHom_X]
    simp

end Points2

end Points


/-!
### The group structure: comultiplication, counit, antipode

The formal multiplicative group is a group object: the comultiplication sends the coordinate
`X` to `X ⊗ X` in the completed tensor product, the counit sends `X` to `1`, and the antipode
sends `X` to `X⁻¹`. Each is constructed by evaluating at an appropriate *unit* of a complete
adic `R`-algebra, using `unitEval`: the target of the comultiplication is the completed tensor
product `R{X,X⁻¹} ⊗̂_R R{X,X⁻¹}` (an adic ring by `CompletedTensorProduct.isAdicRing`), in which
the element `X ⊗ X` is a unit, being a product of images of the unit `X`.
-/

section Group

variable (hI : I.FG)

/-- The completed tensor square `R{X,X⁻¹} ⊗̂_R R{X,X⁻¹}`, the target of the comultiplication of
the formal multiplicative group. -/
abbrev tensorSquare : Type u :=
  CompletedTensorProduct R I (RestrictedLaurentSeries R I) (RestrictedLaurentSeries R I)

/-- The element `X ⊗ X` of the completed tensor square, as a unit: the product of the images of
the coordinate under the two canonical maps. -/
def tensorX : (tensorSquare R I)ˣ :=
  ((isUnit_X R I 1).map
    (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I))).unit *
  ((isUnit_X R I 1).map
    (CompletedTensorProduct.inr R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I))).unit

theorem tensorX_coe :
    (tensorX R I : tensorSquare R I) =
      CompletedTensorProduct.inl R I _ _ (X R I 1) *
        CompletedTensorProduct.inr R I _ _ (X R I 1) :=
  rfl

/-- **The comultiplication of the formal multiplicative group**: the continuous `R`-algebra map
`R{X,X⁻¹} → R{X,X⁻¹} ⊗̂_R R{X,X⁻¹}` sending the coordinate `X` to `X ⊗ X` (Bosch, §8). -/
def comul :
    letI := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI
    RestrictedLaurentSeries R I →+* tensorSquare R I :=
  letI hR := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
    (RestrictedLaurentSeries R I) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (tensorSquare R I) := hR.toIsAdicComplete
  unitEval R I
    (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I))
    (by
      rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]
      exact le_of_eq rfl)
    (tensorX R I)

/-- The comultiplication sends the coordinate to `X ⊗ X`. -/
theorem comul_X :
    letI := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI
    comul R I hI (X R I 1) =
      CompletedTensorProduct.inl R I _ _ (X R I 1) *
        CompletedTensorProduct.inr R I _ _ (X R I 1) := by
  letI hR := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
    (RestrictedLaurentSeries R I) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (tensorSquare R I) := hR.toIsAdicComplete
  have h := unitEval_X R I
    (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I))
    (by
      rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]
      exact le_of_eq rfl)
    (tensorX R I) 1
  rw [zpow_one] at h
  exact h.trans (tensorX_coe R I)

/-- **The counit**: the continuous `R`-algebra map `R{X,X⁻¹} → R` sending `X` to `1` — the
identity section of the formal multiplicative group. -/
def counit [TopologicalSpace R] [IsAdicRing I] : RestrictedLaurentSeries R I →+* R :=
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  unitEval R I I (le_of_eq (Ideal.map_id I)) 1

theorem counit_X [TopologicalSpace R] [IsAdicRing I] (n : ℤ) : counit R I (X R I n) = 1 := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  have h := unitEval_X R I I (le_of_eq (Ideal.map_id I)) 1 n
  rw [one_zpow] at h
  exact h

/-- **The antipode**: the continuous `R`-algebra map `R{X,X⁻¹} → R{X,X⁻¹}` sending `X` to
`X⁻¹` — the inversion of the formal multiplicative group. -/
def antipode (hI : I.FG) :
    letI := isAdicRing R I hI
    RestrictedLaurentSeries R I →+* RestrictedLaurentSeries R I :=
  letI hR := isAdicRing R I hI
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    hR.toIsAdicComplete
  unitEval R I (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm) (isUnit_X R I 1).unit⁻¹

/-- The coordinate `X` and its inverse `X⁻¹` multiply to `1` in `R{X, X⁻¹}`. -/
theorem X_one_mul_X_neg_one : X R I 1 * X R I (-1) = 1 := by
  change algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I) (T 1) *
    algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I) (T (-1)) = 1
  rw [← map_mul, ← T_add]
  norm_num [T_zero]

/-- **The antipode inverts the coordinate**: `antipode X = X⁻¹ = X R I (-1)`. Together with the
counit and comultiplication computations this exhibits the inversion of `Ĝm` on the functor of
points. -/
theorem antipode_X_one :
    letI := isAdicRing R I hI
    antipode R I hI (X R I 1) = X R I (-1) := by
  letI := isAdicRing R I hI
  set w : (RestrictedLaurentSeries R I)ˣ := (isUnit_X R I 1).unit with hw
  have hval : (w : RestrictedLaurentSeries R I) = X R I 1 := (isUnit_X R I 1).unit_spec
  have hAnti : antipode R I hI (X R I 1) = Units.val w⁻¹ := by
    have h := unitEval_X R I (idealOfDefinition R I)
      (le_of_eq (idealOfDefinition_eq_map R I).symm) w⁻¹ 1
    rw [zpow_one] at h
    exact h
  rw [hAnti]
  have hinv : Units.val w⁻¹ * X R I 1 = 1 := by
    have h := w.inv_mul
    rwa [hval] at h
  calc Units.val w⁻¹
      = Units.val w⁻¹ * (X R I 1 * X R I (-1)) := by rw [X_one_mul_X_neg_one, mul_one]
    _ = (Units.val w⁻¹ * X R I 1) * X R I (-1) := by rw [mul_assoc]
    _ = X R I (-1) := by rw [hinv, one_mul]

/-!
### The group-object axioms on the functor of points

The comultiplication, counit and antipode induce, on the functor of points
`Hom_cont(Spf S, Ĝm) ≃ Sˣ` (`pointsEquivUnits`), exactly the multiplication, unit and inversion
of the unit group `Sˣ`. Concretely, for continuous points `F, G` of `Ĝm` in a complete adic
`R`-algebra `S`:

* the *convolution product* `(F ⊗̂ G) ∘ comul` — obtained by composing the comultiplication with
  the lift `CompletedTensorProduct.lift F G` of the pair — sends the coordinate `X` to the
  product `F X · G X` (`lift_comp_comul_X`), i.e. to `↑(pointUnit F · pointUnit G)`;
* the counit followed by the structural map `R → S` is the trivial point `X ↦ 1`
  (`algebraMap_comp_counit_X`);
* precomposition with the antipode inverts the coordinate (`antipode_X_one`).

Since a continuous point is determined by the image of `X` (`point_ext`), these identities pin
the group structure down to the multiplication of `Sˣ`.
-/

section Points3

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)
variable (F G : RestrictedLaurentSeries R I →ₐ[R] S)

/-- **The comultiplication implements the group law on points**: the convolution product
`(F ⊗̂ G) ∘ comul` of two points sends the coordinate `X` to `F X · G X`. -/
theorem lift_comp_comul_X :
    (CompletedTensorProduct.lift L hIL F G).comp (comul R I hI) (X R I 1)
      = F (X R I 1) * G (X R I 1) := by
  rw [RingHom.comp_apply, comul_X, map_mul, CompletedTensorProduct.lift_inl,
    CompletedTensorProduct.lift_inr]

/-- The convolution product of two points corresponds to the product of the associated units:
the group law of `Ĝm` matches the multiplication of `Sˣ` under `pointsEquivUnits`. -/
theorem lift_comp_comul_X_eq_unit :
    (CompletedTensorProduct.lift L hIL F G).comp (comul R I hI) (X R I 1)
      = ((pointUnit R I F * pointUnit R I G : Sˣ) : S) := by
  rw [lift_comp_comul_X, Units.val_mul, pointUnit_coe, pointUnit_coe]

/-- **The counit is the identity section**: the counit followed by the structural map `R → S`
is the trivial point `X ↦ 1` (the unit of `Sˣ`). -/
theorem algebraMap_comp_counit_X [TopologicalSpace R] [IsAdicRing I] (n : ℤ) :
    (algebraMap R S).comp (counit R I) (X R I n) = 1 := by
  rw [RingHom.comp_apply, counit_X, map_one]

end Points3

end Group

end RestrictedLaurentSeries
