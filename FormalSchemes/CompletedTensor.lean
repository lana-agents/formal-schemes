import FormalSchemes.AdicExtend
import FormalSchemes.RestrictedPowerSeries
import Mathlib.RingTheory.TensorProduct.Maps

set_option linter.style.header false

/-!
# The completed tensor product of adic algebras

For adic `R`-algebras `A` and `B` over a base `(R, I)`, the **completed tensor product**
`A ⊗̂_R B` is the `I`-adic completion of the ordinary tensor product `A ⊗_R B` (Bosch,
*Lectures on Formal and Rigid Geometry*, §7; EGA I, 10.7). It is the coordinate ring of the
fibre product `Spf A ×_{Spf R} Spf B`, and is the construction needed to express group
structures on formal schemes (comultiplications land in a completed tensor product) and, more
generally, fibre products of formal schemes.

With the design used throughout this development the construction is immediate: the completion
of any ring at a finitely generated ideal is a complete adic ring
(`AdicCompletion.isAdicRing_map`), so `A ⊗̂_R B` is an adic `R`-algebra with ideal of definition
the extension of `I`, and the universal property follows from the universal property of the
tensor product composed with the continuous-extension machinery of
`FormalSchemes/AdicExtend.lean`.

## Main definitions and results

* `CompletedTensorProduct R I A B`: the completed tensor product, i.e. `AdicCompletion` of
  `A ⊗[R] B` at the extension of `I`.
* `CompletedTensorProduct.isAdicRing`: it is a complete adic ring (for `I` finitely generated),
  so its formal spectrum is an affine formal scheme.
* `CompletedTensorProduct.inl`, `inr`: the canonical `R`-algebra maps from the two factors.
* `CompletedTensorProduct.lift`: the universal property (existence direction) — a pair of
  `R`-algebra maps into a complete adic `R`-algebra, whose images of `I` land in the ideal of
  definition, induces a map from the completed tensor product; `lift_inl`, `lift_inr` compute
  it on the factors.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open Ideal TensorProduct

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The **completed tensor product** `A ⊗̂_R B` of two `R`-algebras, relative to the ideal `I`
of the base: the `I`-adic completion of `A ⊗[R] B`. -/
abbrev CompletedTensorProduct : Type u :=
  AdicCompletion (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B)

namespace CompletedTensorProduct

/-- The ideal of definition of the completed tensor product: the extension of `I`. -/
abbrev idealOfDefinition : Ideal (CompletedTensorProduct R I A B) :=
  (I.map (algebraMap R (A ⊗[R] B))).map
    (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B))

/-- The completed tensor product is a complete adic ring, for `I` finitely generated; hence its
formal spectrum is an affine formal scheme. -/
theorem isAdicRing (hI : I.FG) : IsAdicRing (idealOfDefinition R I A B) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

/-- The canonical `R`-algebra map from the first factor. -/
def inl : A →ₐ[R] CompletedTensorProduct R I A B :=
  (IsScalarTower.toAlgHom R (A ⊗[R] B) (CompletedTensorProduct R I A B)).comp
    Algebra.TensorProduct.includeLeft

/-- The canonical `R`-algebra map from the second factor. -/
def inr : B →ₐ[R] CompletedTensorProduct R I A B :=
  (IsScalarTower.toAlgHom R (A ⊗[R] B) (CompletedTensorProduct R I A B)).comp
    Algebra.TensorProduct.includeRight

/-!
### The universal property (existence direction)
-/

section Lift

variable {R I A B}
variable {S : Type u} [CommRing S] [Algebra R S] (L : Ideal S) [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)
variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)

/-- The universal property of the **completed** tensor product, existence direction: two
`R`-algebra maps into a complete adic `R`-algebra `S` — complete for an ideal `L` containing
`I·S` — induce a ring homomorphism from `A ⊗̂_R B`, since the tensor-product map is continuous
for the `I`-adic topologies. -/
def lift : CompletedTensorProduct R I A B →+* S :=
  AdicCompletion.extendRingHom (I.map (algebraMap R (A ⊗[R] B))) L
    (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
    (Ideal.map_algebraMap_pow_le_comap I L hIL (Algebra.TensorProduct.lift f g
      (fun _ _ => Commute.all _ _)))

theorem lift_of (x : A ⊗[R] B) :
    lift L hIL f g (AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B) x) =
      Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) x :=
  AdicCompletion.extendRingHom_of _ _ _ _ x

theorem lift_tmul (a : A) (b : B) :
    lift L hIL f g (AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B)
      (a ⊗ₜ[R] b)) = f a * g b := by
  rw [lift_of]
  exact Algebra.TensorProduct.lift_tmul _ _ _ a b

/-- The lift restricted to the first factor is `f`. -/
theorem lift_inl (a : A) : lift L hIL f g (inl R I A B a) = f a := by
  have h : inl R I A B a =
      AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B) (a ⊗ₜ[R] (1 : B)) := by
    change algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) (a ⊗ₜ[R] (1 : B)) = _
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h, lift_tmul, map_one, mul_one]

/-- The lift restricted to the second factor is `g`. -/
theorem lift_inr (b : B) : lift L hIL f g (inr R I A B b) = g b := by
  have h : inr R I A B b =
      AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b) := by
    change algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) ((1 : A) ⊗ₜ[R] b) = _
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h, lift_tmul, map_one, one_mul]

end Lift

end CompletedTensorProduct
