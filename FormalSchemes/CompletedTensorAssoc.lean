import FormalSchemes.CompletedTensor

set_option linter.style.header false

/-!
# The associativity isomorphism of the completed tensor product

For adic `R`-algebras `A`, `B`, `C` over a base `(R, I)` with `I` finitely generated, the
completed tensor product is associative:
`(A ⊗̂_R B) ⊗̂_R C ≃+* A ⊗̂_R (B ⊗̂_R C)`. This is the completed-tensor counterpart of
`Algebra.TensorProduct.assoc`, and is the piece needed for the tensor-level coassociativity Hopf
identity of a formal group (e.g. `Ĝm`, issue 67), whose comultiplication lands in a completed
tensor product.

The construction is entirely universal-property driven. The one new ingredient over the existing
`CompletedTensor.lean` API is that `lift` produces a *ring* homomorphism, whereas feeding it into
an outer `lift` (whose factors are themselves completed tensor products) requires an *algebra*
homomorphism; `CompletedTensorProduct.liftAlgHom` packages `lift` as an `R`-algebra homomorphism
(it commutes with `algebraMap R` because it agrees with the `R`-algebra maps `inl`/`inr` on the
factors). The two structural maps are then built from `lift`/`liftAlgHom`, and shown mutually
inverse by the uniqueness principle `hom_ext` (applied once on the outer completed tensor product
and once, nested, on the inner one).

## Main definitions and results

* `CompletedTensorProduct.liftAlgHom`: the universal-property `lift`, packaged as an `R`-algebra
  homomorphism.
* `CompletedTensorProduct.inl_mem_pow`: the canonical map `inl` carries the powers of the
  ideal of definition of the first factor into the powers of the ideal of definition of the
  completed tensor product (the `inr` counterpart lives in `CompletedTensor.lean`).
* `CompletedTensorProduct.assocHom` / `assocInvHom`: the two structural maps of the associativity
  isomorphism.
* `CompletedTensorProduct.assocEquiv`: the associativity isomorphism
  `(A ⊗̂_R B) ⊗̂_R C ≃+* A ⊗̂_R (B ⊗̂_R C)`, with the simp lemmas `assocEquiv_inl_inl`,
  `assocEquiv_inl_inr`, `assocEquiv_inr` computing it on generators.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open Ideal TensorProduct

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Membership in the powers of the ideal of definition of `A ⊗̂_R B`, phrased through the
extension `I·(A ⊗̂_R B)` of the base ideal (a convenient form of `idealOfDefinition_eq_map`). -/
theorem mem_pow_iff_map (m : ℕ) {x : CompletedTensorProduct R I A B} :
    x ∈ (idealOfDefinition R I A B) ^ m ↔
      x ∈ (I.map (algebraMap R (CompletedTensorProduct R I A B))) ^ m := by
  rw [idealOfDefinition_eq_map]

/-!
### `lift` as an algebra homomorphism
-/

section LiftAlgHom

variable {S : Type u} [CommRing S] [Algebra R S] (L : Ideal S) [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L) (f : A →ₐ[R] S) (g : B →ₐ[R] S)

/-- The universal-property `lift`, packaged as an `R`-algebra homomorphism. It coincides with
`lift` as a ring homomorphism; it commutes with `algebraMap R` because it agrees with the
`R`-algebra maps `f`, `g` on the factors. -/
def liftAlgHom : CompletedTensorProduct R I A B →ₐ[R] S :=
  { lift L hIL f g with
    commutes' := fun r => by
      change lift L hIL f g (algebraMap R (CompletedTensorProduct R I A B) r) = algebraMap R S r
      rw [← (inl R I A B).commutes r, lift_inl]
      exact f.commutes r }

@[simp]
theorem liftAlgHom_inl (a : A) : liftAlgHom L hIL f g (inl R I A B a) = f a :=
  lift_inl L hIL f g a

@[simp]
theorem liftAlgHom_inr (b : B) : liftAlgHom L hIL f g (inr R I A B b) = g b :=
  lift_inr L hIL f g b

theorem liftAlgHom_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I A B} (hx : x ∈ (idealOfDefinition R I A B) ^ m) :
    liftAlgHom L hIL f g x ∈ L ^ m :=
  lift_mem_pow L hIL f g hI m hx

end LiftAlgHom

/-!
### The associativity isomorphism

We abbreviate `AB = A ⊗̂_R B`, `BC = B ⊗̂_R C`, and write `assocHom` for the forward map
`(A ⊗̂_R B) ⊗̂_R C →+* A ⊗̂_R (B ⊗̂_R C)` and `assocInvHom` for its inverse.
-/

section Associator

variable {C : Type u} [CommRing C] [Algebra R C]

/-- The forward structural map `(A ⊗̂_R B) ⊗̂_R C →+* A ⊗̂_R (B ⊗̂_R C)`: `inl (inl a) ↦ inl a`,
`inl (inr b) ↦ inr (inl b)`, `inr c ↦ inr (inr c)`. -/
def assocHom (hI : I.FG) :
    CompletedTensorProduct R I (CompletedTensorProduct R I A B) C →+*
      CompletedTensorProduct R I A (CompletedTensorProduct R I B C) :=
  haveI : IsAdicComplete (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) :=
    (isAdicRing R I A (CompletedTensorProduct R I B C) hI).toIsAdicComplete
  lift (idealOfDefinition R I A (CompletedTensorProduct R I B C))
    (le_of_eq idealOfDefinition_eq_map.symm)
    (liftAlgHom (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (le_of_eq idealOfDefinition_eq_map.symm)
      (inl R I A (CompletedTensorProduct R I B C))
      ((inr R I A (CompletedTensorProduct R I B C)).comp (inl R I B C)))
    ((inr R I A (CompletedTensorProduct R I B C)).comp (inr R I B C))

/-- The inverse structural map `A ⊗̂_R (B ⊗̂_R C) →+* (A ⊗̂_R B) ⊗̂_R C`: `inl a ↦ inl (inl a)`,
`inr (inl b) ↦ inl (inr b)`, `inr (inr c) ↦ inr c`. -/
def assocInvHom (hI : I.FG) :
    CompletedTensorProduct R I A (CompletedTensorProduct R I B C) →+*
      CompletedTensorProduct R I (CompletedTensorProduct R I A B) C :=
  haveI : IsAdicComplete (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) :=
    (isAdicRing R I (CompletedTensorProduct R I A B) C hI).toIsAdicComplete
  lift (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
    (le_of_eq idealOfDefinition_eq_map.symm)
    ((inl R I (CompletedTensorProduct R I A B) C).comp (inl R I A B))
    (liftAlgHom (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (le_of_eq idealOfDefinition_eq_map.symm)
      ((inl R I (CompletedTensorProduct R I A B) C).comp (inr R I A B))
      (inr R I (CompletedTensorProduct R I A B) C))

/-- Continuity of `assocHom`: it carries the powers of the ideal of definition into the powers of
the ideal of definition of the target. -/
theorem assocHom_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I (CompletedTensorProduct R I A B) C}
    (hx : x ∈ (idealOfDefinition R I (CompletedTensorProduct R I A B) C) ^ m) :
    assocHom hI x ∈ (idealOfDefinition R I A (CompletedTensorProduct R I B C)) ^ m := by
  haveI : IsAdicComplete (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) :=
    (isAdicRing R I A (CompletedTensorProduct R I B C) hI).toIsAdicComplete
  unfold assocHom
  exact lift_mem_pow _ _ _ _ hI m hx

/-- Continuity of `assocInvHom`. -/
theorem assocInvHom_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I A (CompletedTensorProduct R I B C)}
    (hx : x ∈ (idealOfDefinition R I A (CompletedTensorProduct R I B C)) ^ m) :
    assocInvHom hI x ∈ (idealOfDefinition R I (CompletedTensorProduct R I A B) C) ^ m := by
  haveI : IsAdicComplete (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) :=
    (isAdicRing R I (CompletedTensorProduct R I A B) C hI).toIsAdicComplete
  unfold assocInvHom
  exact lift_mem_pow _ _ _ _ hI m hx

/-! Action of the two maps on generators. -/

@[simp]
theorem assocHom_inl_inl (hI : I.FG) (a : A) :
    assocHom hI (inl R I (CompletedTensorProduct R I A B) C (inl R I A B a)) =
      inl R I A (CompletedTensorProduct R I B C) a := by
  haveI : IsAdicComplete (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) :=
    (isAdicRing R I A (CompletedTensorProduct R I B C) hI).toIsAdicComplete
  unfold assocHom
  rw [lift_inl, liftAlgHom_inl]

@[simp]
theorem assocHom_inl_inr (hI : I.FG) (b : B) :
    assocHom hI (inl R I (CompletedTensorProduct R I A B) C (inr R I A B b)) =
      inr R I A (CompletedTensorProduct R I B C) (inl R I B C b) := by
  haveI : IsAdicComplete (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) :=
    (isAdicRing R I A (CompletedTensorProduct R I B C) hI).toIsAdicComplete
  unfold assocHom
  rw [lift_inl, liftAlgHom_inr, AlgHom.comp_apply]

@[simp]
theorem assocHom_inr (hI : I.FG) (c : C) :
    assocHom hI (inr R I (CompletedTensorProduct R I A B) C c) =
      inr R I A (CompletedTensorProduct R I B C) (inr R I B C c) := by
  haveI : IsAdicComplete (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) :=
    (isAdicRing R I A (CompletedTensorProduct R I B C) hI).toIsAdicComplete
  unfold assocHom
  rw [lift_inr, AlgHom.comp_apply]

@[simp]
theorem assocInvHom_inl (hI : I.FG) (a : A) :
    assocInvHom hI (inl R I A (CompletedTensorProduct R I B C) a) =
      inl R I (CompletedTensorProduct R I A B) C (inl R I A B a) := by
  haveI : IsAdicComplete (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) :=
    (isAdicRing R I (CompletedTensorProduct R I A B) C hI).toIsAdicComplete
  unfold assocInvHom
  rw [lift_inl, AlgHom.comp_apply]

@[simp]
theorem assocInvHom_inr_inl (hI : I.FG) (b : B) :
    assocInvHom hI (inr R I A (CompletedTensorProduct R I B C) (inl R I B C b)) =
      inl R I (CompletedTensorProduct R I A B) C (inr R I A B b) := by
  haveI : IsAdicComplete (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) :=
    (isAdicRing R I (CompletedTensorProduct R I A B) C hI).toIsAdicComplete
  unfold assocInvHom
  rw [lift_inr, liftAlgHom_inl, AlgHom.comp_apply]

@[simp]
theorem assocInvHom_inr_inr (hI : I.FG) (c : C) :
    assocInvHom hI (inr R I A (CompletedTensorProduct R I B C) (inr R I B C c)) =
      inr R I (CompletedTensorProduct R I A B) C c := by
  haveI : IsAdicComplete (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) :=
    (isAdicRing R I (CompletedTensorProduct R I A B) C hI).toIsAdicComplete
  unfold assocInvHom
  rw [lift_inr, liftAlgHom_inr]

/-- On the image of the first factor `A ⊗̂_R B` of the left-associated product, `assocInvHom`
undoes `assocHom`. Proved by the uniqueness principle applied to the inner completed tensor
product `A ⊗̂_R B`. -/
theorem assocInvHom_assocHom_inl (hI : I.FG) (x : CompletedTensorProduct R I A B) :
    assocInvHom hI (assocHom hI (inl R I (CompletedTensorProduct R I A B) C x)) =
      inl R I (CompletedTensorProduct R I A B) C x := by
  haveI : IsAdicComplete (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) :=
    (isAdicRing R I (CompletedTensorProduct R I A B) C hI).toIsAdicComplete
  have key :
      ((assocInvHom hI).comp (assocHom hI)).comp
          (inl R I (CompletedTensorProduct R I A B) C).toRingHom =
        (inl R I (CompletedTensorProduct R I A B) C).toRingHom := by
    refine hom_ext (idealOfDefinition R I (CompletedTensorProduct R I A B) C) hI
      (fun m y hy => ?_) (fun m y hy => ?_) (fun a => ?_) (fun b => ?_)
    · -- continuity of the composite
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      refine assocInvHom_mem_pow hI m (assocHom_mem_pow hI m (inl_mem_pow m ?_))
      rwa [← mem_pow_iff_map]
    · -- continuity of inl
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact inl_mem_pow m ((mem_pow_iff_map m).mp hy)
    · -- agreement on inl a
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        assocHom_inl_inl, assocInvHom_inl]
    · -- agreement on inr b
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        assocHom_inl_inr, assocInvHom_inr_inl]
  exact DFunLike.congr_fun key x

/-- On the image of the second factor `B ⊗̂_R C` of the right-associated product, `assocHom`
undoes `assocInvHom`. Proved by the uniqueness principle applied to the inner completed tensor
product `B ⊗̂_R C`. -/
theorem assocHom_assocInvHom_inr (hI : I.FG) (y : CompletedTensorProduct R I B C) :
    assocHom hI (assocInvHom hI (inr R I A (CompletedTensorProduct R I B C) y)) =
      inr R I A (CompletedTensorProduct R I B C) y := by
  haveI : IsAdicComplete (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) :=
    (isAdicRing R I A (CompletedTensorProduct R I B C) hI).toIsAdicComplete
  have key :
      ((assocHom hI).comp (assocInvHom hI)).comp
          (inr R I A (CompletedTensorProduct R I B C)).toRingHom =
        (inr R I A (CompletedTensorProduct R I B C)).toRingHom := by
    refine hom_ext (idealOfDefinition R I A (CompletedTensorProduct R I B C)) hI
      (fun m z hz => ?_) (fun m z hz => ?_) (fun b => ?_) (fun c => ?_)
    · -- continuity of the composite
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      refine assocHom_mem_pow hI m (assocInvHom_mem_pow hI m (inr_mem_pow m ?_))
      rwa [← mem_pow_iff_map]
    · -- continuity of inr
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact inr_mem_pow m ((mem_pow_iff_map m).mp hz)
    · -- agreement on inl b
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        assocInvHom_inr_inl, assocHom_inl_inr]
    · -- agreement on inr c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        assocInvHom_inr_inr, assocHom_inr]
  exact DFunLike.congr_fun key y

/-- `assocInvHom` is a left inverse of `assocHom`. -/
theorem assocInvHom_comp_assocHom (hI : I.FG) :
    (assocInvHom hI).comp (assocHom hI) =
      RingHom.id (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) := by
  haveI : IsAdicComplete (idealOfDefinition R I (CompletedTensorProduct R I A B) C)
      (CompletedTensorProduct R I (CompletedTensorProduct R I A B) C) :=
    (isAdicRing R I (CompletedTensorProduct R I A B) C hI).toIsAdicComplete
  refine hom_ext (idealOfDefinition R I (CompletedTensorProduct R I A B) C) hI
    (fun m x hx => ?_) (fun m x hx => hx) (fun x => ?_) (fun c => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply]
    exact assocInvHom_mem_pow hI m (assocHom_mem_pow hI m hx)
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    exact assocInvHom_assocHom_inl hI x
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, assocHom_inr,
      assocInvHom_inr_inr]

/-- `assocInvHom` is a right inverse of `assocHom`. -/
theorem assocHom_comp_assocInvHom (hI : I.FG) :
    (assocHom hI).comp (assocInvHom hI) =
      RingHom.id (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) := by
  haveI : IsAdicComplete (idealOfDefinition R I A (CompletedTensorProduct R I B C))
      (CompletedTensorProduct R I A (CompletedTensorProduct R I B C)) :=
    (isAdicRing R I A (CompletedTensorProduct R I B C) hI).toIsAdicComplete
  refine hom_ext (idealOfDefinition R I A (CompletedTensorProduct R I B C)) hI
    (fun m x hx => ?_) (fun m x hx => hx) (fun a => ?_) (fun y => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply]
    exact assocHom_mem_pow hI m (assocInvHom_mem_pow hI m hx)
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, assocInvHom_inl,
      assocHom_inl_inl]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    exact assocHom_assocInvHom_inr hI y

/-- **The associativity isomorphism** of the completed tensor product (for `I` finitely
generated): `(A ⊗̂_R B) ⊗̂_R C ≃+* A ⊗̂_R (B ⊗̂_R C)`. -/
def assocEquiv (hI : I.FG) :
    CompletedTensorProduct R I (CompletedTensorProduct R I A B) C ≃+*
      CompletedTensorProduct R I A (CompletedTensorProduct R I B C) :=
  RingEquiv.ofRingHom (assocHom hI) (assocInvHom hI)
    (assocHom_comp_assocInvHom hI) (assocInvHom_comp_assocHom hI)

@[simp]
theorem assocEquiv_inl_inl (hI : I.FG) (a : A) :
    assocEquiv hI (inl R I (CompletedTensorProduct R I A B) C (inl R I A B a)) =
      inl R I A (CompletedTensorProduct R I B C) a :=
  assocHom_inl_inl hI a

@[simp]
theorem assocEquiv_inl_inr (hI : I.FG) (b : B) :
    assocEquiv hI (inl R I (CompletedTensorProduct R I A B) C (inr R I A B b)) =
      inr R I A (CompletedTensorProduct R I B C) (inl R I B C b) :=
  assocHom_inl_inr hI b

@[simp]
theorem assocEquiv_inr (hI : I.FG) (c : C) :
    assocEquiv hI (inr R I (CompletedTensorProduct R I A B) C c) =
      inr R I A (CompletedTensorProduct R I B C) (inr R I B C c) :=
  assocHom_inr hI c

@[simp]
theorem assocEquiv_symm_inl (hI : I.FG) (a : A) :
    (assocEquiv hI).symm (inl R I A (CompletedTensorProduct R I B C) a) =
      inl R I (CompletedTensorProduct R I A B) C (inl R I A B a) :=
  assocInvHom_inl hI a

@[simp]
theorem assocEquiv_symm_inr_inl (hI : I.FG) (b : B) :
    (assocEquiv hI).symm (inr R I A (CompletedTensorProduct R I B C) (inl R I B C b)) =
      inl R I (CompletedTensorProduct R I A B) C (inr R I A B b) :=
  assocInvHom_inr_inl hI b

@[simp]
theorem assocEquiv_symm_inr_inr (hI : I.FG) (c : C) :
    (assocEquiv hI).symm (inr R I A (CompletedTensorProduct R I B C) (inr R I B C c)) =
      inr R I (CompletedTensorProduct R I A B) C c :=
  assocInvHom_inr_inr hI c

end Associator

end CompletedTensorProduct
