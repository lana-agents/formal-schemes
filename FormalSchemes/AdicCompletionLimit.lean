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

/-!
### Limits of towers identified with a shifted quotient tower

The towers arising from sheaves on formal spectra have level `n` given by (a ring isomorphic
to) `R ⧸ I ^ (n + 1)` — the tower is *shifted* by one relative to `quotientTower I`, whose level
`n` is `R ⧸ I ^ n`. The following generic bridge identifies the limit of any such shifted tower
with `AdicCompletion I R`: given level isomorphisms `e n : T.obj n ≃+* R ⧸ I ^ (n + 1)`
intertwining the transition maps of `T` with the quotient factor maps, the limit of `T` is the
adic completion. The missing level `0` of the shifted tower is no loss: `R ⧸ I ^ 0` is the zero
ring, so it carries no information.
-/

section ShiftedTower

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (T : ℕᵒᵖ ⥤ CommRingCat.{u})
variable (e : ∀ n : ℕ, (T.obj ⟨n⟩ : Type u) ≃+* R ⧸ I ^ (n + 1))
variable (he : ∀ n : ℕ, (e n).toRingHom.comp (T.map (homOfLE (Nat.le_add_right n 1)).op).hom =
  (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))).comp (e (n + 1)).toRingHom)

/-- The projection of the limit of a shifted tower to its `n`-th level, transported to
`R ⧸ I ^ (n + 1)` through the level isomorphism. -/
def towerProj (n : ℕ) : (limit T : CommRingCat) →+* R ⧸ I ^ (n + 1) :=
  (e n).toRingHom.comp (limit.π T ⟨n⟩).hom

theorem towerProj_apply (n : ℕ) (z : (limit T : CommRingCat)) :
    towerProj I T e n z = e n ((limit.π T ⟨n⟩).hom z) :=
  rfl

include he in
theorem factorPow_towerProj (n : ℕ) (z : (limit T : CommRingCat)) :
    Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) (towerProj I T e (n + 1) z) =
      towerProj I T e n z := by
  have hz : (T.map (homOfLE (Nat.le_add_right n 1)).op).hom ((limit.π T ⟨n + 1⟩).hom z) =
      (limit.π T ⟨n⟩).hom z := by
    have h := DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom (limit.w T (homOfLE (Nat.le_add_right n 1)).op)) z
    rwa [CommRingCat.hom_comp] at h
  have h1 := DFunLike.congr_fun (he n) ((limit.π T ⟨n + 1⟩).hom z)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe] at h1
  rw [towerProj_apply, towerProj_apply, ← hz, h1]

/-- The compatible family of projections `limit T →+* R ⧸ I ^ n`, for *all* `n` (the missing
level `0` of the shifted tower is recovered by factoring from level `1`). -/
def towerProjFamily (n : ℕ) : (limit T : CommRingCat) →+* R ⧸ I ^ n :=
  (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (towerProj I T e n)

theorem towerProjFamily_apply (n : ℕ) (z : (limit T : CommRingCat)) :
    towerProjFamily I T e n z =
      Ideal.Quotient.factorPow I (Nat.le_succ n) (towerProj I T e n z) :=
  rfl

include he in
theorem factorPow_comp_towerProjFamily {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (towerProjFamily I T e n) =
      towerProjFamily I T e m := by
  induction n, hmn using Nat.le_induction with
  | base =>
    refine RingHom.ext fun z => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, towerProjFamily_apply,
      Ideal.Quotient.factor_comp_apply]
  | succ n hmn ih =>
    refine RingHom.ext fun z => ?_
    have h1 := DFunLike.congr_fun ih z
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 ⊢
    rw [← h1, towerProjFamily_apply, towerProjFamily_apply,
      ← factorPow_towerProj I T e he n z]
    simp only [Ideal.Quotient.factor_comp_apply]

/-- The ring homomorphism from the limit of a shifted tower to the adic completion, given by
the universal property of the completion applied to the projections. -/
def towerToAdicCompletion : (limit T : CommRingCat) →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (towerProjFamily I T e)
    (fun hmn => factorPow_comp_towerProjFamily I T e he hmn)

@[simp]
theorem evalₐ_towerToAdicCompletion (n : ℕ) (y : (limit T : CommRingCat)) :
    evalₐ I n (towerToAdicCompletion I T e he y) = towerProjFamily I T e n y :=
  evalₐ_liftRingHom I _ _ n y

/-- The cone over a shifted tower with point the adic completion, whose projections are the
evaluations `evalₐ` at level `n + 1` transported through the level isomorphisms. -/
def towerCone : Cone T where
  pt := CommRingCat.of (AdicCompletion I R)
  π := NatTrans.ofOpSequence
    (fun n => CommRingCat.ofHom ((e n).symm.toRingHom.comp (evalₐ I (n + 1)).toRingHom))
    (fun n => by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun x => ?_
      change (e n).symm (evalₐ I (n + 1) x) =
        (T.map (homOfLE (Nat.le_add_right n 1)).op).hom
          ((e (n + 1)).symm (evalₐ I (n + 1 + 1) x))
      apply (e n).injective
      rw [RingEquiv.apply_symm_apply]
      have h := DFunLike.congr_fun (he n) ((e (n + 1)).symm (evalₐ I (n + 1 + 1) x))
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, RingEquiv.apply_symm_apply] at h
      rw [h]
      exact (factorPow_evalₐ I (Nat.le_succ (n + 1)) x).symm)

@[simp]
theorem towerCone_π_app (n : ℕ) :
    (towerCone I T e he).π.app ⟨n⟩ =
      CommRingCat.ofHom ((e n).symm.toRingHom.comp (evalₐ I (n + 1)).toRingHom) :=
  rfl

/-- The ring homomorphism from the adic completion to the limit of a shifted tower, induced by
the cone `towerCone`. -/
def adicCompletionToTower : AdicCompletion I R →+* (limit T : CommRingCat) :=
  (limit.lift T (towerCone I T e he)).hom

theorem π_adicCompletionToTower (n : ℕ) (x : AdicCompletion I R) :
    (limit.π T ⟨n⟩).hom (adicCompletionToTower I T e he x) =
      (e n).symm (evalₐ I (n + 1) x) := by
  have h := congrArg CommRingCat.Hom.hom (limit.lift_π (towerCone I T e he) ⟨n⟩)
  rw [CommRingCat.hom_comp] at h
  exact DFunLike.congr_fun h x

/-- **The limit of a shifted quotient tower is the adic completion.** Given a tower
`T : ℕᵒᵖ ⥤ CommRingCat` whose level `n` is identified with `R ⧸ I ^ (n + 1)` compatibly with
the transition maps, the categorical limit of `T` is `AdicCompletion I R`. -/
def towerLimitRingEquiv : (limit T : CommRingCat) ≃+* AdicCompletion I R where
  toFun := towerToAdicCompletion I T e he
  invFun := adicCompletionToTower I T e he
  map_mul' := map_mul _
  map_add' := map_add _
  left_inv x := by
    refine Concrete.limit_ext T _ _ fun ⟨n⟩ => ?_
    change (limit.π T ⟨n⟩).hom _ = (limit.π T ⟨n⟩).hom x
    rw [π_adicCompletionToTower, evalₐ_towerToAdicCompletion]
    apply (e n).injective
    rw [RingEquiv.apply_symm_apply, towerProjFamily_apply,
      factorPow_towerProj I T e he n x, towerProj_apply]
  right_inv y := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_towerToAdicCompletion, towerProjFamily_apply, towerProj_apply,
      π_adicCompletionToTower, RingEquiv.apply_symm_apply]
    exact factorPow_evalₐ I (Nat.le_succ n) y

theorem evalₐ_towerLimitRingEquiv (n : ℕ) (z : (limit T : CommRingCat)) :
    evalₐ I (n + 1) (towerLimitRingEquiv I T e he z) = towerProj I T e n z := by
  change evalₐ I (n + 1) (towerToAdicCompletion I T e he z) = _
  rw [evalₐ_towerToAdicCompletion, towerProjFamily_apply,
    factorPow_towerProj I T e he n z]

end AdicCompletion

end ShiftedTower
