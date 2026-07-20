import FormalSchemes.RestrictedPowerSeries
import FormalSchemes.AdicExtend
import FormalSchemes.CompletedTensor
import FormalSchemes.CompletedTensorAssoc
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

/-- Membership in the powers of the ideal of definition, expressed through the module filtration
`(I·R[T,T⁻¹]) ^ m • ⊤` used by the completion API. -/
theorem mem_idealOfDefinition_pow_iff (m : ℕ) (x : RestrictedLaurentSeries R I) :
    x ∈ (idealOfDefinition R I) ^ m ↔
      x ∈ ((I.map (algebraMap R (LaurentPolynomial R))) ^ m • ⊤ :
        Submodule (LaurentPolynomial R) (RestrictedLaurentSeries R I)) := by
  rw [← Ideal.mem_map_pow_iff_mem_smul_top (I.map (algebraMap R (LaurentPolynomial R))) m x,
    idealOfDefinition, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Algebra.algebraMap_self, Ideal.map_id]

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

/-!
### The left counit axiom of `Ĝm`

At the level of the completed tensor product the counit `ε = counit` satisfies the *left counit
axiom* of a Hopf algebra: applying `ε` to the first tensor factor of the comultiplication
`Δ = comul` and then the left unitor `R ⊗̂_R R{X,X⁻¹} ≃+* R{X,X⁻¹}` recovers the identity. This
is the tensor-level (as opposed to functor-of-points) form of the identity-section law.
-/

/-- The counit, bundled as an `R`-algebra homomorphism `R{X,X⁻¹} →ₐ[R] R` (the `AlgHom` form of
`counit`, sending `X ↦ 1`); needed to feed it into `CompletedTensorProduct.map`. -/
def counitAlgHom [TopologicalSpace R] [IsAdicRing I] : RestrictedLaurentSeries R I →ₐ[R] R :=
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  unitEvalAlgHom R I I (le_of_eq (Ideal.map_id I)) 1

theorem counitAlgHom_X [TopologicalSpace R] [IsAdicRing I] (n : ℤ) :
    counitAlgHom R I (X R I n) = 1 := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  have h := unitEvalAlgHom_X R I I (le_of_eq (Ideal.map_id I)) 1 n
  rw [one_zpow] at h
  exact h

/-- The comultiplication, bundled as an `R`-algebra homomorphism (the `AlgHom` form of `comul`,
sending `X ↦ X ⊗ X`). -/
def comulAlgHom :
    letI := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI
    RestrictedLaurentSeries R I →ₐ[R] tensorSquare R I :=
  letI hR := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
    (RestrictedLaurentSeries R I) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (tensorSquare R I) := hR.toIsAdicComplete
  unitEvalAlgHom R I
    (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I))
    (by
      rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]
      exact le_of_eq rfl)
    (tensorX R I)

/-- The bundled comultiplication sends the coordinate to `X ⊗ X`. -/
theorem comulAlgHom_X :
    letI := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI
    comulAlgHom R I hI (X R I 1) =
      CompletedTensorProduct.inl R I _ _ (X R I 1) *
        CompletedTensorProduct.inr R I _ _ (X R I 1) := by
  letI hR := CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
    (RestrictedLaurentSeries R I) hI
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (tensorSquare R I) := hR.toIsAdicComplete
  exact comul_X R I hI

/-- The composite `ε ⊗̂ id` applying the counit to the first tensor factor, bundled as an
`R`-algebra homomorphism `R{X,X⁻¹} ⊗̂_R R{X,X⁻¹} →ₐ[R] R ⊗̂_R R{X,X⁻¹}` (the `AlgHom` form of
`CompletedTensorProduct.map hI counitAlgHom id`). -/
def counitMapAlgHom [TopologicalSpace R] [IsAdicRing I] :
    tensorSquare R I →ₐ[R]
      CompletedTensorProduct R I R (RestrictedLaurentSeries R I) where
  toRingHom := CompletedTensorProduct.map hI (counitAlgHom R I)
    (AlgHom.id R (RestrictedLaurentSeries R I))
  commutes' r := by
    have h : CompletedTensorProduct.map hI (counitAlgHom R I)
        (AlgHom.id R (RestrictedLaurentSeries R I))
        (algebraMap R (tensorSquare R I) r) =
          algebraMap R (CompletedTensorProduct R I R (RestrictedLaurentSeries R I)) r := by
      rw [← (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I)
          (RestrictedLaurentSeries R I)).commutes r, CompletedTensorProduct.map_inl,
        (counitAlgHom R I).commutes]
      exact (CompletedTensorProduct.inl R I R (RestrictedLaurentSeries R I)).commutes r
    exact h

theorem counitMapAlgHom_apply [TopologicalSpace R] [IsAdicRing I] (x : tensorSquare R I) :
    counitMapAlgHom R I hI x =
      CompletedTensorProduct.map hI (counitAlgHom R I)
        (AlgHom.id R (RestrictedLaurentSeries R I)) x :=
  rfl

/-- **The crux of the left counit axiom**: applying the counit to the first tensor factor of the
comultiplication is the canonical inclusion `inr` of the second factor, i.e.
`(ε ⊗̂ id) ∘ Δ = inr`. Both send `X ↦ inr X`. -/
theorem counitMap_comp_comul [TopologicalSpace R] [IsAdicRing I] :
    (CompletedTensorProduct.map hI (counitAlgHom R I)
        (AlgHom.id R (RestrictedLaurentSeries R I))).comp (comul R I hI) =
      (CompletedTensorProduct.inr R I R (RestrictedLaurentSeries R I)).toRingHom := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I R (RestrictedLaurentSeries R I))
      (CompletedTensorProduct R I R (RestrictedLaurentSeries R I)) :=
    (CompletedTensorProduct.isAdicRing R I R (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I))
      (CompletedTensorProduct R I (RestrictedLaurentSeries R I) (RestrictedLaurentSeries R I)) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I
      (CompletedTensorProduct.idealOfDefinition R I R (RestrictedLaurentSeries R I))
      ((counitMapAlgHom R I hI).comp (comulAlgHom R I hI)) := by
    intro m x hx
    rw [AlgHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI (counitAlgHom R I)
      (AlgHom.id R (RestrictedLaurentSeries R I)) m
      (isContinuousPoint_unitEvalAlgHom R I
        (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
          (RestrictedLaurentSeries R I))
        (by
          rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]
          exact le_of_eq rfl)
        hI (tensorX R I) m x hx)
  have hG : IsContinuousPoint R I
      (CompletedTensorProduct.idealOfDefinition R I R (RestrictedLaurentSeries R I))
      (CompletedTensorProduct.inr R I R (RestrictedLaurentSeries R I)) := by
    intro m x hx
    rw [← RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff, idealOfDefinition_eq_map] at hx
    exact CompletedTensorProduct.inr_mem_pow m hx
  have hX : (counitMapAlgHom R I hI).comp (comulAlgHom R I hI) (X R I 1) =
      CompletedTensorProduct.inr R I R (RestrictedLaurentSeries R I) (X R I 1) := by
    rw [AlgHom.comp_apply, comulAlgHom_X, counitMapAlgHom_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, counitAlgHom_X,
      map_one, AlgHom.id_apply, one_mul]
  have key := point_ext R I
    (CompletedTensorProduct.idealOfDefinition R I R (RestrictedLaurentSeries R I)) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

/-- **The left counit axiom of the formal multiplicative group `Ĝm`.** Applying the counit `ε`
to the first tensor factor of the comultiplication `Δ` and then the left unitor
`R ⊗̂_R R{X,X⁻¹} ≃+* R{X,X⁻¹}` recovers the identity: `unitEquiv ∘ (ε ⊗̂ id) ∘ Δ = id`. This
is the tensor-level (Hopf-algebra) form of the identity-section law. -/
theorem counit_law_left [TopologicalSpace R] [IsAdicRing I] :
    letI : IsAdicComplete (I.map (algebraMap R (RestrictedLaurentSeries R I)))
        (RestrictedLaurentSeries R I) := by
      rw [← idealOfDefinition_eq_map]
      exact (isAdicRing R I hI).toIsAdicComplete
    (CompletedTensorProduct.unitEquiv hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (counitAlgHom R I)
          (AlgHom.id R (RestrictedLaurentSeries R I))).comp (comul R I hI)) =
      RingHom.id (RestrictedLaurentSeries R I) := by
  letI : IsAdicComplete (I.map (algebraMap R (RestrictedLaurentSeries R I)))
      (RestrictedLaurentSeries R I) := by
    rw [← idealOfDefinition_eq_map]
    exact (isAdicRing R I hI).toIsAdicComplete
  rw [counitMap_comp_comul R I hI]
  exact RingHom.ext fun a => CompletedTensorProduct.unitEquiv_inr hI a

/-!
### The right counit axiom of `Ĝm`

The mirror of the left counit axiom: applying the counit `ε` to the *second* tensor factor of the
comultiplication `Δ` and then the right unitor `R{X,X⁻¹} ⊗̂_R R ≃+* R{X,X⁻¹}` also recovers the
identity. Together with `counit_law_left` these are the two counit axioms of the Hopf-algebra
structure on `R{X,X⁻¹}`.
-/

/-- The composite `id ⊗̂ ε` applying the counit to the second tensor factor, bundled as an
`R`-algebra homomorphism `R{X,X⁻¹} ⊗̂_R R{X,X⁻¹} →ₐ[R] R{X,X⁻¹} ⊗̂_R R` (the `AlgHom` form of
`CompletedTensorProduct.map hI id counitAlgHom`). -/
def counitMapAlgHomRight [TopologicalSpace R] [IsAdicRing I] :
    tensorSquare R I →ₐ[R]
      CompletedTensorProduct R I (RestrictedLaurentSeries R I) R where
  toRingHom := CompletedTensorProduct.map hI
    (AlgHom.id R (RestrictedLaurentSeries R I)) (counitAlgHom R I)
  commutes' r := by
    have h : CompletedTensorProduct.map hI
        (AlgHom.id R (RestrictedLaurentSeries R I)) (counitAlgHom R I)
        (algebraMap R (tensorSquare R I) r) =
          algebraMap R (CompletedTensorProduct R I (RestrictedLaurentSeries R I) R) r := by
      rw [← (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I)
          (RestrictedLaurentSeries R I)).commutes r, CompletedTensorProduct.map_inl,
        (AlgHom.id R (RestrictedLaurentSeries R I)).commutes]
      exact (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I) R).commutes r
    exact h

theorem counitMapAlgHomRight_apply [TopologicalSpace R] [IsAdicRing I] (x : tensorSquare R I) :
    counitMapAlgHomRight R I hI x =
      CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
        (counitAlgHom R I) x :=
  rfl

/-- **The crux of the right counit axiom**: applying the counit to the second tensor factor of the
comultiplication is the canonical inclusion `inl` of the first factor, i.e.
`(id ⊗̂ ε) ∘ Δ = inl`. Both send `X ↦ inl X`. -/
theorem counitMapRight_comp_comul [TopologicalSpace R] [IsAdicRing I] :
    (CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
        (counitAlgHom R I)).comp (comul R I hI) =
      (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I) R).toRingHom := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I) R)
      (CompletedTensorProduct R I (RestrictedLaurentSeries R I) R) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I) R hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I))
      (CompletedTensorProduct R I (RestrictedLaurentSeries R I) (RestrictedLaurentSeries R I)) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I) R)
      ((counitMapAlgHomRight R I hI).comp (comulAlgHom R I hI)) := by
    intro m x hx
    rw [AlgHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI (AlgHom.id R (RestrictedLaurentSeries R I))
      (counitAlgHom R I) m
      (isContinuousPoint_unitEvalAlgHom R I
        (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
          (RestrictedLaurentSeries R I))
        (by
          rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]
          exact le_of_eq rfl)
        hI (tensorX R I) m x hx)
  have hG : IsContinuousPoint R I
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I) R)
      (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I) R) := by
    intro m x hx
    rw [← RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff, idealOfDefinition_eq_map] at hx
    exact CompletedTensorProduct.inl_mem_pow m hx
  have hX : (counitMapAlgHomRight R I hI).comp (comulAlgHom R I hI) (X R I 1) =
      CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I) R (X R I 1) := by
    rw [AlgHom.comp_apply, comulAlgHom_X, counitMapAlgHomRight_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, counitAlgHom_X,
      map_one, AlgHom.id_apply, mul_one]
  have key := point_ext R I
    (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I) R) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

/-- **The right counit axiom of the formal multiplicative group `Ĝm`.** Applying the counit `ε`
to the second tensor factor of the comultiplication `Δ` and then the right unitor
`R{X,X⁻¹} ⊗̂_R R ≃+* R{X,X⁻¹}` recovers the identity: `rightUnitEquiv ∘ (id ⊗̂ ε) ∘ Δ = id`. This
is the tensor-level (Hopf-algebra) form of the identity-section law, mirroring `counit_law_left`. -/
theorem counit_law_right [TopologicalSpace R] [IsAdicRing I] :
    letI : IsAdicComplete (I.map (algebraMap R (RestrictedLaurentSeries R I)))
        (RestrictedLaurentSeries R I) := by
      rw [← idealOfDefinition_eq_map]
      exact (isAdicRing R I hI).toIsAdicComplete
    (CompletedTensorProduct.rightUnitEquiv hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
          (counitAlgHom R I)).comp (comul R I hI)) =
      RingHom.id (RestrictedLaurentSeries R I) := by
  letI : IsAdicComplete (I.map (algebraMap R (RestrictedLaurentSeries R I)))
      (RestrictedLaurentSeries R I) := by
    rw [← idealOfDefinition_eq_map]
    exact (isAdicRing R I hI).toIsAdicComplete
  rw [counitMapRight_comp_comul R I hI]
  exact RingHom.ext fun a => CompletedTensorProduct.rightUnitEquiv_inl hI a

/-!
### Coassociativity of `Ĝm`

The remaining structural Hopf-algebra axiom: the comultiplication `Δ = comul` is *coassociative*.
Concretely, applying `Δ` to either tensor factor of `Δ` and then re-associating the completed
tensor product with the associator
`(R{X,X⁻¹} ⊗̂_R R{X,X⁻¹}) ⊗̂_R R{X,X⁻¹} ≃+* R{X,X⁻¹} ⊗̂_R (R{X,X⁻¹} ⊗̂_R R{X,X⁻¹})`
gives the same continuous `R`-algebra map. Both composites send `X ↦ X ⊗ X ⊗ X`.
-/

/-- The comultiplication tensored with the identity on the second factor, `Δ ⊗̂ id`, bundled as an
`R`-algebra homomorphism `R{X,X⁻¹} ⊗̂_R R{X,X⁻¹} →ₐ[R] (R{X,X⁻¹} ⊗̂_R R{X,X⁻¹}) ⊗̂_R R{X,X⁻¹}`
(the `AlgHom` form of `CompletedTensorProduct.map hI comulAlgHom id`; built via `liftAlgHom`, so it
coincides with `map` as a ring homomorphism). -/
def comulMapLeftAlgHom :
    tensorSquare R I →ₐ[R]
      CompletedTensorProduct R I (tensorSquare R I) (RestrictedLaurentSeries R I) :=
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (tensorSquare R I)
        (RestrictedLaurentSeries R I))
      (CompletedTensorProduct R I (tensorSquare R I) (RestrictedLaurentSeries R I)) :=
    (CompletedTensorProduct.isAdicRing R I (tensorSquare R I)
      (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  CompletedTensorProduct.liftAlgHom
    (CompletedTensorProduct.idealOfDefinition R I (tensorSquare R I) (RestrictedLaurentSeries R I))
    (le_of_eq CompletedTensorProduct.idealOfDefinition_eq_map.symm)
    ((CompletedTensorProduct.inl R I (tensorSquare R I) (RestrictedLaurentSeries R I)).comp
      (comulAlgHom R I hI))
    ((CompletedTensorProduct.inr R I (tensorSquare R I) (RestrictedLaurentSeries R I)).comp
      (AlgHom.id R (RestrictedLaurentSeries R I)))

theorem comulMapLeftAlgHom_apply (x : tensorSquare R I) :
    comulMapLeftAlgHom R I hI x =
      CompletedTensorProduct.map hI (comulAlgHom R I hI)
        (AlgHom.id R (RestrictedLaurentSeries R I)) x :=
  rfl

/-- The identity on the first factor tensored with the comultiplication, `id ⊗̂ Δ`, bundled as an
`R`-algebra homomorphism `R{X,X⁻¹} ⊗̂_R R{X,X⁻¹} →ₐ[R] R{X,X⁻¹} ⊗̂_R (R{X,X⁻¹} ⊗̂_R R{X,X⁻¹})`
(the `AlgHom` form of `CompletedTensorProduct.map hI id comulAlgHom`; built via `liftAlgHom`, so it
coincides with `map` as a ring homomorphism). -/
def comulMapRightAlgHom :
    tensorSquare R I →ₐ[R]
      CompletedTensorProduct R I (RestrictedLaurentSeries R I) (tensorSquare R I) :=
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (tensorSquare R I))
      (CompletedTensorProduct R I (RestrictedLaurentSeries R I) (tensorSquare R I)) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (tensorSquare R I) hI).toIsAdicComplete
  CompletedTensorProduct.liftAlgHom
    (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I) (tensorSquare R I))
    (le_of_eq CompletedTensorProduct.idealOfDefinition_eq_map.symm)
    ((CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I) (tensorSquare R I)).comp
      (AlgHom.id R (RestrictedLaurentSeries R I)))
    ((CompletedTensorProduct.inr R I (RestrictedLaurentSeries R I) (tensorSquare R I)).comp
      (comulAlgHom R I hI))

theorem comulMapRightAlgHom_apply (x : tensorSquare R I) :
    comulMapRightAlgHom R I hI x =
      CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
        (comulAlgHom R I hI) x :=
  rfl

set_option maxHeartbeats 1000000 in
-- The composite runs through the triply-nested completed tensor products
-- `(R{X,X⁻¹} ⊗̂ R{X,X⁻¹}) ⊗̂ R{X,X⁻¹}`, whose `whnf`/`isDefEq` exceeds the default budget.
/-- **Coassociativity of the comultiplication of `Ĝm`** — the tensor-level Hopf-algebra
coassociativity axiom: routing `(Δ ⊗̂ id) ∘ Δ` through the associator agrees with `(id ⊗̂ Δ) ∘ Δ`.
Both continuous points send the coordinate `X` to `X ⊗ X ⊗ X`. -/
theorem comul_coassoc :
    (CompletedTensorProduct.assocHom hI).comp
        ((CompletedTensorProduct.map hI (comulAlgHom R I hI)
          (AlgHom.id R (RestrictedLaurentSeries R I))).comp (comul R I hI)) =
      (CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
        (comulAlgHom R I hI)).comp (comul R I hI) := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (tensorSquare R I) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (tensorSquare R I)
        (RestrictedLaurentSeries R I))
      (CompletedTensorProduct R I (tensorSquare R I) (RestrictedLaurentSeries R I)) :=
    (CompletedTensorProduct.isAdicRing R I (tensorSquare R I)
      (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (tensorSquare R I))
      (CompletedTensorProduct R I (RestrictedLaurentSeries R I) (tensorSquare R I)) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (tensorSquare R I) hI).toIsAdicComplete
  set L := CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
    (tensorSquare R I)
  have hcomul : IsContinuousPoint R I
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (comulAlgHom R I hI) := fun m x hx =>
    isContinuousPoint_unitEvalAlgHom R I
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I))
      (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
      hI (tensorX R I) m x hx
  have hF : IsContinuousPoint R I L
      ((CompletedTensorProduct.assocAlgHom hI).comp
        ((comulMapLeftAlgHom R I hI).comp (comulAlgHom R I hI))) := by
    intro m x hx
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    exact CompletedTensorProduct.assocHom_mem_pow hI m
      (CompletedTensorProduct.map_mem_pow hI (comulAlgHom R I hI)
        (AlgHom.id R (RestrictedLaurentSeries R I)) m (hcomul m x hx))
  have hG : IsContinuousPoint R I L
      ((comulMapRightAlgHom R I hI).comp (comulAlgHom R I hI)) := by
    intro m x hx
    rw [AlgHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI (AlgHom.id R (RestrictedLaurentSeries R I))
      (comulAlgHom R I hI) m (hcomul m x hx)
  have hX : (CompletedTensorProduct.assocAlgHom hI).comp
        ((comulMapLeftAlgHom R I hI).comp (comulAlgHom R I hI)) (X R I 1) =
      (comulMapRightAlgHom R I hI).comp (comulAlgHom R I hI) (X R I 1) := by
    simp only [AlgHom.comp_apply, comulAlgHom_X, comulMapLeftAlgHom_apply,
      comulMapRightAlgHom_apply, map_mul, CompletedTensorProduct.map_inl,
      CompletedTensorProduct.map_inr, AlgHom.id_apply,
      CompletedTensorProduct.assocAlgHom_apply, CompletedTensorProduct.assocHom_inl_inl,
      CompletedTensorProduct.assocHom_inl_inr, CompletedTensorProduct.assocHom_inr, mul_assoc]
  have key := point_ext R I L hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

/-!
### The antipode axiom of `Ĝm`

The final Hopf-algebra axiom: the antipode `S = antipode` is a *convolution inverse* of the
identity. Folding the completed tensor square by the multiplication `∇` after applying the
antipode to one factor of the comultiplication `Δ` recovers the trivial endomorphism
`η ∘ ε` (the "multiply by `1`" section): `∇ ∘ (S ⊗̂ id) ∘ Δ = η ∘ ε`, and the mirror with the
antipode on the second factor. Both composites send the coordinate `X ↦ X⁻¹ · X = 1`.
-/

/-- The antipode of `Ĝm`, bundled as an `R`-algebra homomorphism `R{X,X⁻¹} →ₐ[R] R{X,X⁻¹}`
sending `X ↦ X⁻¹` (the `AlgHom` form of `antipode`); needed to feed it into
`CompletedTensorProduct.map`. -/
def antipodeAlgHom :
    letI := isAdicRing R I hI
    RestrictedLaurentSeries R I →ₐ[R] RestrictedLaurentSeries R I :=
  letI hR := isAdicRing R I hI
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    hR.toIsAdicComplete
  unitEvalAlgHom R I (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm) (isUnit_X R I 1).unit⁻¹

/-- The bundled antipode inverts the coordinate: `antipode X = X⁻¹ = X R I (-1)`. -/
theorem antipodeAlgHom_X :
    letI := isAdicRing R I hI
    antipodeAlgHom R I hI (X R I 1) = X R I (-1) := by
  letI := isAdicRing R I hI
  set w : (RestrictedLaurentSeries R I)ˣ := (isUnit_X R I 1).unit with hw
  have hval : (w : RestrictedLaurentSeries R I) = X R I 1 := (isUnit_X R I 1).unit_spec
  have hAnti : antipodeAlgHom R I hI (X R I 1) = Units.val w⁻¹ := by
    have h := unitEvalAlgHom_X R I (idealOfDefinition R I)
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

/-- **The multiplication of `R{X,X⁻¹}` as a completed-tensor fold** `∇ : R{X,X⁻¹} ⊗̂_R R{X,X⁻¹}
→ₐ[R] R{X,X⁻¹}`, folding both factors by the identity (`inl a ↦ a`, `inr b ↦ b`, hence
`a ⊗ b ↦ a · b`); the target of the convolution product in the antipode axiom. -/
def mulAlgHom : tensorSquare R I →ₐ[R] RestrictedLaurentSeries R I :=
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  CompletedTensorProduct.liftAlgHom (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm)
    (AlgHom.id R (RestrictedLaurentSeries R I))
    (AlgHom.id R (RestrictedLaurentSeries R I))

@[simp]
theorem mulAlgHom_inl (a : RestrictedLaurentSeries R I) :
    mulAlgHom R I hI (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) a) = a := by
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  exact CompletedTensorProduct.liftAlgHom_inl (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm)
    (AlgHom.id R (RestrictedLaurentSeries R I))
    (AlgHom.id R (RestrictedLaurentSeries R I)) a

@[simp]
theorem mulAlgHom_inr (b : RestrictedLaurentSeries R I) :
    mulAlgHom R I hI (CompletedTensorProduct.inr R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) b) = b := by
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  exact CompletedTensorProduct.liftAlgHom_inr (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm)
    (AlgHom.id R (RestrictedLaurentSeries R I))
    (AlgHom.id R (RestrictedLaurentSeries R I)) b

/-- The multiplication `∇` maps the powers of the ideal of definition of the tensor square into
those of `R{X,X⁻¹}` — continuity of `∇`. -/
theorem mulAlgHom_mem_pow (m : ℕ) {x : tensorSquare R I}
    (hx : x ∈ (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I)) ^ m) :
    mulAlgHom R I hI x ∈ (idealOfDefinition R I) ^ m := by
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  exact CompletedTensorProduct.liftAlgHom_mem_pow (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm)
    (AlgHom.id R (RestrictedLaurentSeries R I))
    (AlgHom.id R (RestrictedLaurentSeries R I)) hI m hx

/-- The antipode applied to the first tensor factor, `S ⊗̂ id`, bundled as an `R`-algebra
homomorphism (the `AlgHom` form of `CompletedTensorProduct.map hI antipodeAlgHom id`). -/
def antipodeMapAlgHom : tensorSquare R I →ₐ[R] tensorSquare R I where
  toRingHom := CompletedTensorProduct.map hI (antipodeAlgHom R I hI)
    (AlgHom.id R (RestrictedLaurentSeries R I))
  commutes' r := by
    change CompletedTensorProduct.map hI (antipodeAlgHom R I hI)
        (AlgHom.id R (RestrictedLaurentSeries R I))
        (algebraMap R (tensorSquare R I) r) = algebraMap R (tensorSquare R I) r
    rw [← (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)).commutes r, CompletedTensorProduct.map_inl,
      (antipodeAlgHom R I hI).commutes]

theorem antipodeMapAlgHom_apply (x : tensorSquare R I) :
    antipodeMapAlgHom R I hI x =
      CompletedTensorProduct.map hI (antipodeAlgHom R I hI)
        (AlgHom.id R (RestrictedLaurentSeries R I)) x :=
  rfl

/-- The antipode applied to the second tensor factor, `id ⊗̂ S`, bundled as an `R`-algebra
homomorphism (the `AlgHom` form of `CompletedTensorProduct.map hI id antipodeAlgHom`). -/
def antipodeMapAlgHomRight : tensorSquare R I →ₐ[R] tensorSquare R I where
  toRingHom := CompletedTensorProduct.map hI
    (AlgHom.id R (RestrictedLaurentSeries R I)) (antipodeAlgHom R I hI)
  commutes' r := by
    change CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
        (antipodeAlgHom R I hI)
        (algebraMap R (tensorSquare R I) r) = algebraMap R (tensorSquare R I) r
    rw [← (CompletedTensorProduct.inl R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)).commutes r, CompletedTensorProduct.map_inl,
      (AlgHom.id R (RestrictedLaurentSeries R I)).commutes]

theorem antipodeMapAlgHomRight_apply (x : tensorSquare R I) :
    antipodeMapAlgHomRight R I hI x =
      CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
        (antipodeAlgHom R I hI) x :=
  rfl

/-- Continuity of the antipode-on-the-first-factor / comultiplication composite: the trivial
endomorphism `η ∘ ε` and the convolution `∇ ∘ (S ⊗̂ id) ∘ Δ` are continuous points, so it
suffices to compare their action on the coordinate `X`. This lemma packages the continuity of
the trivial endomorphism `η ∘ ε` used in both antipode laws. -/
theorem isContinuousPoint_algebraMap_comp_counit (hI : I.FG) [TopologicalSpace R] [IsAdicRing I] :
    IsContinuousPoint R I (idealOfDefinition R I)
      ((Algebra.ofId R (RestrictedLaurentSeries R I)).comp (counitAlgHom R I)) := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  intro m x hx
  rw [AlgHom.comp_apply]
  have hc : counitAlgHom R I x ∈ I ^ m :=
    isContinuousPoint_unitEvalAlgHom R I I (le_of_eq (Ideal.map_id I)) hI 1 m x hx
  rw [idealOfDefinition_eq_map]
  have hmem : (algebraMap R (RestrictedLaurentSeries R I)) (counitAlgHom R I x) ∈
      (I ^ m).map (algebraMap R (RestrictedLaurentSeries R I)) :=
    Ideal.mem_map_of_mem _ hc
  rwa [Ideal.map_pow] at hmem

set_option maxHeartbeats 800000 in
-- The `point_ext` comparison unfolds the convolution through the nested completed tensor square
-- `R{X,X⁻¹} ⊗̂ R{X,X⁻¹}`, whose `whnf`/`isDefEq` exceeds the default heartbeat budget.
/-- **The (left) antipode axiom of the formal multiplicative group `Ĝm`.** Applying the antipode
`S` to the first tensor factor of the comultiplication `Δ` and folding by the multiplication `∇`
recovers the trivial endomorphism `η ∘ ε` (the identity section composed with the counit):
`∇ ∘ (S ⊗̂ id) ∘ Δ = η ∘ ε`. This is the tensor-level (Hopf-algebra) antipode/inversion axiom,
expressing `X⁻¹ · X = 1`. -/
theorem antipode_law_left [TopologicalSpace R] [IsAdicRing I] :
    (mulAlgHom R I hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (antipodeAlgHom R I hI)
          (AlgHom.id R (RestrictedLaurentSeries R I))).comp (comul R I hI)) =
      (algebraMap R (RestrictedLaurentSeries R I)).comp (counit R I) := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (tensorSquare R I) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I (idealOfDefinition R I)
      ((mulAlgHom R I hI).comp
        ((antipodeMapAlgHom R I hI).comp (comulAlgHom R I hI))) := by
    intro m x hx
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    refine mulAlgHom_mem_pow R I hI m ?_
    rw [antipodeMapAlgHom_apply]
    exact CompletedTensorProduct.map_mem_pow hI (antipodeAlgHom R I hI)
      (AlgHom.id R (RestrictedLaurentSeries R I)) m
      (isContinuousPoint_unitEvalAlgHom R I
        (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
          (RestrictedLaurentSeries R I))
        (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
        hI (tensorX R I) m x hx)
  have hG := isContinuousPoint_algebraMap_comp_counit R I hI
  have hX : (mulAlgHom R I hI).comp
        ((antipodeMapAlgHom R I hI).comp (comulAlgHom R I hI)) (X R I 1) =
      (Algebra.ofId R (RestrictedLaurentSeries R I)).comp (counitAlgHom R I) (X R I 1) := by
    simp only [AlgHom.comp_apply, comulAlgHom_X, antipodeMapAlgHom_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, antipodeAlgHom_X,
      AlgHom.id_apply, mulAlgHom_inl, mulAlgHom_inr, counitAlgHom_X, map_one]
    rw [mul_comm (X R I (-1)) (X R I 1), X_one_mul_X_neg_one]
  have key := point_ext R I (idealOfDefinition R I) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

set_option maxHeartbeats 800000 in
-- The `point_ext` comparison unfolds the convolution through the nested completed tensor square
-- `R{X,X⁻¹} ⊗̂ R{X,X⁻¹}`, whose `whnf`/`isDefEq` exceeds the default heartbeat budget.
/-- **The (right) antipode axiom of the formal multiplicative group `Ĝm`**, mirroring
`antipode_law_left`: applying the antipode `S` to the *second* tensor factor of the
comultiplication `Δ` and folding by `∇` also recovers the trivial endomorphism `η ∘ ε`:
`∇ ∘ (id ⊗̂ S) ∘ Δ = η ∘ ε`. -/
theorem antipode_law_right [TopologicalSpace R] [IsAdicRing I] :
    (mulAlgHom R I hI).toRingHom.comp
        ((CompletedTensorProduct.map hI (AlgHom.id R (RestrictedLaurentSeries R I))
          (antipodeAlgHom R I hI)).comp (comul R I hI)) =
      (algebraMap R (RestrictedLaurentSeries R I)).comp (counit R I) := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
        (RestrictedLaurentSeries R I)) (tensorSquare R I) :=
    (CompletedTensorProduct.isAdicRing R I (RestrictedLaurentSeries R I)
      (RestrictedLaurentSeries R I) hI).toIsAdicComplete
  have hF : IsContinuousPoint R I (idealOfDefinition R I)
      ((mulAlgHom R I hI).comp
        ((antipodeMapAlgHomRight R I hI).comp (comulAlgHom R I hI))) := by
    intro m x hx
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    refine mulAlgHom_mem_pow R I hI m ?_
    rw [antipodeMapAlgHomRight_apply]
    exact CompletedTensorProduct.map_mem_pow hI (AlgHom.id R (RestrictedLaurentSeries R I))
      (antipodeAlgHom R I hI) m
      (isContinuousPoint_unitEvalAlgHom R I
        (CompletedTensorProduct.idealOfDefinition R I (RestrictedLaurentSeries R I)
          (RestrictedLaurentSeries R I))
        (by rw [CompletedTensorProduct.idealOfDefinition, Ideal.map_map]; exact le_of_eq rfl)
        hI (tensorX R I) m x hx)
  have hG := isContinuousPoint_algebraMap_comp_counit R I hI
  have hX : (mulAlgHom R I hI).comp
        ((antipodeMapAlgHomRight R I hI).comp (comulAlgHom R I hI)) (X R I 1) =
      (Algebra.ofId R (RestrictedLaurentSeries R I)).comp (counitAlgHom R I) (X R I 1) := by
    simp only [AlgHom.comp_apply, comulAlgHom_X, antipodeMapAlgHomRight_apply, map_mul,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr, antipodeAlgHom_X,
      AlgHom.id_apply, mulAlgHom_inl, mulAlgHom_inr, counitAlgHom_X, map_one]
    rw [X_one_mul_X_neg_one]
  have key := point_ext R I (idealOfDefinition R I) hI hF hG hX
  refine RingHom.ext fun z => ?_
  exact DFunLike.congr_fun key z

end Group

/-!
### Naturality of the functor of points

The bijection `pointsEquivUnits : Hom_cont(Spf S, Ĝm) ≃ Sˣ` is **natural in `S`**: a morphism
`φ : S ⟶ S'` of complete adic `R`-algebras carrying the filtration compatibly
(`L.map φ ≤ L'`) intertwines the two point sets — via post-composition of points on one side and
the induced map on units `Sˣ → S'ˣ` on the other. This upgrades the pointwise group structure of
the previous section to a *functorial* group structure `S ↦ Sˣ` on the functor of points, which
is the content of `Ĝm` being a group object (Bosch, §8).
-/

section Naturality

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable {S' : Type u} [CommRing S'] (L' : Ideal S') [Algebra R S'] [IsAdicComplete L' S']
variable (hIL : I.map (algebraMap R S) ≤ L) (hIL' : I.map (algebraMap R S') ≤ L')

omit [IsAdicComplete L S] [IsAdicComplete L' S'] in
/-- A morphism `φ : S →ₐ[R] S'` of complete adic `R`-algebras carrying the filtration
compatibly (`L.map φ ≤ L'`) sends continuous points of `Ĝm` to continuous points: `φ.comp F` is
again continuous. -/
theorem isContinuousPoint_comp (φ : S →ₐ[R] S') (hφ : L.map φ.toRingHom ≤ L')
    {F : RestrictedLaurentSeries R I →ₐ[R] S} (hF : IsContinuousPoint R I L F) :
    IsContinuousPoint R I L' (φ.comp F) := by
  intro m x hx
  have hmem : φ.toRingHom (F x) ∈ (L ^ m).map φ.toRingHom :=
    Ideal.mem_map_of_mem _ (hF m x hx)
  rw [Ideal.map_pow] at hmem
  rw [AlgHom.comp_apply]
  exact Ideal.pow_right_mono hφ m hmem

/-- **Naturality of the unit-evaluation point in `S`.** Evaluation at a unit is natural:
post-composing the point attached to `u : Sˣ` with `φ` gives the point attached to the image
unit `φ(u) : S'ˣ`. -/
theorem unitEvalAlgHom_comp (hI : I.FG) (φ : S →ₐ[R] S') (hφ : L.map φ.toRingHom ≤ L') (u : Sˣ) :
    φ.comp (unitEvalAlgHom R I L hIL u) =
      unitEvalAlgHom R I L' hIL' (Units.map φ.toRingHom.toMonoidHom u) := by
  refine point_ext R I L' hI ?_ (isContinuousPoint_unitEvalAlgHom R I L' hIL' hI _) ?_
  · exact isContinuousPoint_comp R I L L' φ hφ (isContinuousPoint_unitEvalAlgHom R I L hIL hI u)
  · rw [AlgHom.comp_apply, unitEvalAlgHom_X, unitEvalAlgHom_X, zpow_one, zpow_one, Units.coe_map]
    rfl

/-- **Naturality of the unit attached to a point in `S`.** The unit of a post-composed point
`φ.comp F` is the image under `φ` of the unit of `F`. -/
theorem pointUnit_comp (φ : S →ₐ[R] S') (F : RestrictedLaurentSeries R I →ₐ[R] S) :
    pointUnit R I (φ.comp F) = Units.map φ.toRingHom.toMonoidHom (pointUnit R I F) := by
  refine Units.ext ?_
  rw [pointUnit_coe, AlgHom.comp_apply, Units.coe_map, pointUnit_coe]
  rfl

/-- **The functor of points of `Ĝm` is natural in `S`.** For a morphism `φ : S →ₐ[R] S'` of
complete adic `R`-algebras carrying the filtration compatibly, the square relating
`pointsEquivUnits` over `S` and over `S'` to post-composition of points and the induced map on
units commutes. Together with `pointsEquivUnits` and the group-object identities of the previous
section, this exhibits `Ĝm` as a group object via the functorial group structure `S ↦ Sˣ`. -/
theorem pointsEquivUnits_naturality (hI : I.FG) (φ : S →ₐ[R] S') (hφ : L.map φ.toRingHom ≤ L')
    (F : { F : RestrictedLaurentSeries R I →ₐ[R] S // IsContinuousPoint R I L F }) :
    pointsEquivUnits R I L' hIL' hI
        ⟨φ.comp F.1, isContinuousPoint_comp R I L L' φ hφ F.2⟩ =
      Units.map φ.toRingHom.toMonoidHom (pointsEquivUnits R I L hIL hI F) :=
  pointUnit_comp R I φ F.1

end Naturality

end RestrictedLaurentSeries
