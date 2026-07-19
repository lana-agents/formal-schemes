import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

set_option linter.style.header false

/-!
# The adic completion as a categorical limit of the quotient tower

For a commutative ring `R` and an ideal `I`, the `I`-adic completion `AdicCompletion I R` is,
by construction, the inverse limit of the tower of quotients `n ↦ R ⧸ I ^ n` with the quotient
factor maps `Ideal.Quotient.factorPow` as transition maps. This file records that description at
the level of `CommRingCat`: it packages the tower as a functor `ℕᵒᵖ ⥤ CommRingCat`, exhibits the
canonical projections `AdicCompletion.evalₐ` as a cone over it, and identifies the cone point
`AdicCompletion I R` with the categorical `limit` as a `RingEquiv`.

This is the commutative-algebra / category-theory reconciliation step needed to identify the
sections of the structure sheaf of a formal spectrum on a basic open `D(f)` with an adic
completion (EGA I 10.5.6ff / Stacks Tag 0AI7): the sheaf side produces a limit of a tower
`n ↦ A ⧸ J ^ (n + 1)` in `CommRingCat`, and this file turns such a limit into `AdicCompletion J A`.

## Main definitions

* `AdicCompletion.quotientTower I : ℕᵒᵖ ⥤ CommRingCat`: the tower `n ↦ R ⧸ I ^ n` with transition
  maps `Ideal.Quotient.factorPow`.
* `AdicCompletion.evalCone I`: the cone over `quotientTower I` with point `AdicCompletion I R` and
  projections `evalₐ`.
* `AdicCompletion.limitRingEquiv I : AdicCompletion I R ≃+* limit (quotientTower I)`: the resulting
  ring isomorphism exhibiting the adic completion as the limit of its quotient tower.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §10.5.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The tower `n ↦ R ⧸ I ^ n`, with the quotient factor maps `Ideal.Quotient.factorPow` as
transition maps, packaged as a functor `ℕᵒᵖ ⥤ CommRingCat`. Its limit is `AdicCompletion I R`
(see `AdicCompletion.limitRingEquiv`). -/
def quotientTower : ℕᵒᵖ ⥤ CommRingCat :=
  Functor.ofOpSequence (X := fun n => CommRingCat.of (R ⧸ I ^ n))
    (fun n => CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ n)))

@[simp]
theorem quotientTower_obj (n : ℕ) :
    (quotientTower I).obj ⟨n⟩ = CommRingCat.of (R ⧸ I ^ n) :=
  rfl

@[simp]
theorem quotientTower_map_succ (n : ℕ) :
    (quotientTower I).map (homOfLE (Nat.le_add_right n 1)).op =
      CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ n)) := by
  simp [quotientTower]

/-- The transition maps of `quotientTower I` are the quotient factor maps `factorPow`, for an
arbitrary `m ≤ n` (not only the consecutive case). -/
theorem quotientTower_map {m n : ℕ} (hmn : m ≤ n) :
    (quotientTower I).map (homOfLE hmn).op =
      CommRingCat.ofHom (Ideal.Quotient.factorPow I hmn) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl m)).op = 𝟙 (Opposite.op m) from rfl,
      CategoryTheory.Functor.map_id]
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_id]
    exact Ideal.Quotient.factor_eq.symm
  | succ n hmn ih =>
    rw [show (homOfLE (hmn.trans (Nat.le_succ n))).op =
        (homOfLE (Nat.le_add_right n 1)).op ≫ (homOfLE hmn).op from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_comp, quotientTower_map_succ, ih]
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp]
    exact Ideal.Quotient.factor_comp (Ideal.pow_le_pow_right (Nat.le_succ n))
      (Ideal.pow_le_pow_right hmn)

/-- Compatibility of the projections `evalₐ` with the transition maps: `factorPow` after `evalₐ`
at level `n` is `evalₐ` at level `m`. This is the naturality that makes `evalₐ` a cone over
`quotientTower I`. -/
theorem factorPow_evalₐ {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  have hn : (I ^ n • ⊤ : Submodule R R) ≤ I ^ n := by simp
  have hm : (I ^ m • ⊤ : Submodule R R) ≤ I ^ m := by simp
  rw [← factor_eval_eq_evalₐ I x hn, ← factor_eval_eq_evalₐ I x hm, eval_apply, eval_apply,
    ← transitionMap_comp_eval_apply I R hmn x]
  simp only [transitionMap, Submodule.factorPow, Submodule.factor_eq_factor,
    Ideal.Quotient.factor_comp_apply]

theorem factorPow_comp_evalₐ {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (evalₐ I n).toRingHom = (evalₐ I m).toRingHom :=
  RingHom.ext (factorPow_evalₐ I hmn)

/-- The cone over `quotientTower I` whose point is `AdicCompletion I R` and whose projections are
the canonical evaluation maps `evalₐ`. -/
def evalCone : Cone (quotientTower I) where
  pt := CommRingCat.of (AdicCompletion I R)
  π := NatTrans.ofOpSequence
    (fun n => CommRingCat.ofHom (evalₐ I n).toRingHom)
    (fun n => by
      apply CommRingCat.hom_ext
      ext r
      simp only [Functor.const_obj_map, quotientTower_map_succ, CommRingCat.hom_comp,
        RingHom.coe_comp, Function.comp_apply]
      exact (factorPow_evalₐ I (Nat.le_succ n) r).symm)

@[simp]
theorem evalCone_π_app (n : ℕ) :
    (evalCone I).π.app ⟨n⟩ = CommRingCat.ofHom (evalₐ I n).toRingHom :=
  rfl

/-- The compatible family of projections `limit (quotientTower I) →+* R ⧸ I ^ n` cut out by the
limit cone, expressed as ring homomorphisms landing in `R ⧸ I ^ n`. -/
def limitProj (n : ℕ) : (limit (quotientTower I) : CommRingCat) →+* R ⧸ I ^ n :=
  (limit.π (quotientTower I) ⟨n⟩).hom

theorem factorPow_comp_limitProj {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (limitProj I n) = limitProj I m := by
  have hw := limit.w (quotientTower I) (homOfLE hmn).op
  rw [quotientTower_map] at hw
  refine RingHom.ext fun z => ?_
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hw) z
  rw [CommRingCat.hom_comp] at h
  exact h

/-- The ring homomorphism `limit (quotientTower I) →+* AdicCompletion I R` obtained from the
universal property of the adic completion applied to the limit's projections. -/
def fromLimitHom : (limit (quotientTower I) : CommRingCat) →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (limitProj I) (fun hmn => factorPow_comp_limitProj I hmn)

@[simp]
theorem evalₐ_fromLimitHom (n : ℕ) (y : (limit (quotientTower I) : CommRingCat)) :
    evalₐ I n (fromLimitHom I y) = limitProj I n y :=
  evalₐ_liftRingHom I _ _ n y

/-- The evaluation cone `evalCone` transported through the limit's projections recovers the
`evalₐ` maps: `limit.lift evalCone ≫ π n = ofHom (evalₐ n)`. -/
theorem lift_evalCone_π (n : ℕ) :
    limit.lift (quotientTower I) (evalCone I) ≫ limit.π (quotientTower I) ⟨n⟩ =
      CommRingCat.ofHom (evalₐ I n).toRingHom :=
  (limit.lift_π (evalCone I) ⟨n⟩).trans (evalCone_π_app I n)

/-- The ring homomorphism `AdicCompletion I R →+* limit (quotientTower I)` obtained from the
evaluation cone. Its domain is stated as `AdicCompletion I R` (rather than the definitionally
equal `↑(evalCone I).pt`) so that it can be applied to elements without transparency friction. -/
def toLimitHom : AdicCompletion I R →+* (limit (quotientTower I) : CommRingCat) :=
  (limit.lift (quotientTower I) (evalCone I)).hom

theorem limitProj_comp_toLimitHom (n : ℕ) :
    (limitProj I n).comp (toLimitHom I) = (evalₐ I n).toRingHom := by
  have h := congrArg CommRingCat.Hom.hom (lift_evalCone_π I n)
  rw [CommRingCat.hom_comp] at h
  exact h

theorem limitProj_toLimitHom (n : ℕ) (x : AdicCompletion I R) :
    limitProj I n (toLimitHom I x) = evalₐ I n x :=
  DFunLike.congr_fun (limitProj_comp_toLimitHom I n) x

theorem evalₐ_comp_fromLimitHom (n : ℕ) :
    (evalₐ I n).toRingHom.comp (fromLimitHom I) = limitProj I n := by
  ext y
  exact evalₐ_fromLimitHom I n y

/-- The adic completion `AdicCompletion I R` is the categorical limit, in `CommRingCat`, of the
quotient tower `n ↦ R ⧸ I ^ n`. -/
def limitRingEquiv : AdicCompletion I R ≃+* (limit (quotientTower I) : CommRingCat) where
  toFun := toLimitHom I
  invFun := fromLimitHom I
  map_mul' := map_mul _
  map_add' := map_add _
  left_inv x := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_fromLimitHom, limitProj_toLimitHom]
  right_inv y := by
    refine Concrete.limit_ext (quotientTower I) _ _ fun ⟨n⟩ => ?_
    change limitProj I n (toLimitHom I (fromLimitHom I y)) = limitProj I n y
    rw [limitProj_toLimitHom, evalₐ_fromLimitHom]

end AdicCompletion
