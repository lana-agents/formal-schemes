import FormalSchemes.IndSchemeLimitComponents

set_option linter.style.header false

/-!
# The existence half of the colimit property (EGA I, 10.6.7)

`FormalSchemes/IndSchemeThickening.lean` proved that restricting `g : Spf R ⟶ Spec B` along
`thickeningMap I n` is `Spec` of the reduction of `specHomEquiv I B g` modulo `I ^ (n + 1)`, and
that a morphism out of `Spf R` into an affine scheme is **determined** by those restrictions
(`hom_ext_thickeningMap`). `FormalSchemes/IndSchemeLimitComponents.lean` identified the
restrictions with the components of `specHomLimitEquiv`.

Both of those are uniqueness statements. This file supplies the missing existence half:

```
existsUnique_thickeningMap_comp :
  ∃! g : Spf R ⟶ Spec B, ∀ n, thickeningMap I n ≫ g = Spec (φ (n + 1))
```

for any compatible family of ring homomorphisms `φ n : B →+* R ⧸ Iⁿ`. Together with
`hom_ext_thickeningMap` that is the universal property of `Spf R` as the colimit of its
infinitesimal thickenings, for affine targets, as a usable theorem rather than as a bijection
between two abstractly-defined sets.

## What was missing, concretely

Surjectivity of `specHomLimitEquiv` gives existence in principle, but its domain is
`limit (quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B)))` — an abstract limit object — and
nothing in this development constructed an element of it from a family of ring maps. `towerCone`
is that construction: `CategoryTheory.NatTrans.ofOpSequence` turns a family with **consecutive**
compatibility into a cone over `quotientTower I`, whose transition maps are exactly
`Ideal.Quotient.factorPow` on consecutive indices. Completeness of `R` (through `ringLimitIso`)
then lands the cone's lift in `R` itself.

The bridge back to geometry is `mk_liftOfTower`, which reads off the reduction of the lift modulo
`Iⁿ`; it is the first consumer of `limitProj_ringLimitEquiv`.

## The index shift

`AdicCompletion.quotientTower I` has level `n` equal to `R ⧸ Iⁿ`, whereas `thickeningMap I n`
lands on `Spec (R ⧸ I ^ (n + 1))` — the same shift that
`FormalSchemes/IndSchemeLimitComponents.lean` documents. So the family `φ` is indexed by the
tower, and the `n`-th thickening sees `φ (n + 1)`. The level-0 term `φ 0` is a map into the zero
ring `R ⧸ I⁰ = R ⧸ ⊤` (`subsingleton_quotient_pow_zero`) and constrains nothing; it is carried
only because the tower is indexed from `0`.

## Using `existsUnique_thickeningMap_comp`

The family must be supplied **explicitly** at a call site whose statement spells out `φ (n + 1)`:
higher-order unification cannot solve `?φ (n + 1)` against an elaborated expression, and the
failure is a plain type mismatch displaying `?m (n + 1)`, not a defeq problem. The closing
`example` shows the working shape.

## Main results

* `FormalSpectrum.towerCone`: a compatible family of ring maps `B →+* R ⧸ Iⁿ` as a cone over the
  quotient tower.
* `FormalSpectrum.liftOfTower`, `FormalSpectrum.mk_liftOfTower`: the ring map `B →+* R` it lifts
  to, and its reductions.
* `FormalSpectrum.factorPow_comp_mk_comp`: the canonical compatible family attached to a ring map,
  so the hypothesis above is never vacuous.
* `FormalSpectrum.liftOfTower_mk_comp`: `liftOfTower` inverts that family — the lift is a genuine
  two-sided inverse, not merely *a* lift.
* `FormalSpectrum.existsUnique_thickeningMap_comp`: **the existence half of the colimit
  property.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.7).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (B : Type u) [CommRing B]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A compatible family of ring maps `B →+* R ⧸ Iⁿ` is a cone over the quotient tower.**
Compatibility is required only for consecutive indices, which is what
`CategoryTheory.NatTrans.ofOpSequence` consumes; the transition maps of `quotientTower I` on
consecutive indices are `Ideal.Quotient.factorPow`. -/
def towerCone (φ : ∀ n : ℕ, B →+* R ⧸ I ^ n)
    (hφ : ∀ n : ℕ, (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (φ (n + 1)) = φ n) :
    Cone (AdicCompletion.quotientTower I) where
  pt := CommRingCat.of B
  π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj (CommRingCat.of B))
    (fun n => CommRingCat.ofHom (φ n)) (by
      intro n
      rw [AdicCompletion.quotientTower_map_succ]
      simp only [Functor.const_obj_map]
      exact (congrArg CommRingCat.ofHom (hφ n)).symm)

/-- **The ring homomorphism `B →+* R` lifting a compatible family.** The cone lifts through the
limit of the tower, and completeness of `R` (`ringLimitIso`) identifies that limit with `R`. -/
def liftOfTower (φ : ∀ n : ℕ, B →+* R ⧸ I ^ n)
    (hφ : ∀ n : ℕ, (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (φ (n + 1)) = φ n) :
    B →+* R :=
  (limit.lift (AdicCompletion.quotientTower I) (towerCone I B φ hφ) ≫ (ringLimitIso I).inv).hom

/-- **The reductions of the lift are the family it was built from.** `limit.lift_π` gives the
component in the limit object and `limitProj_ringLimitEquiv`
(`FormalSchemes/IndSchemeLimitComponents.lean`) turns it into a reduction. -/
theorem mk_liftOfTower (φ : ∀ n : ℕ, B →+* R ⧸ I ^ n)
    (hφ : ∀ n : ℕ, (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (φ (n + 1)) = φ n)
    (n : ℕ) (b : B) :
    Ideal.Quotient.mk (I ^ n) (liftOfTower I B φ hφ b) = φ n b := by
  have h1 : ringLimitEquiv I (liftOfTower I B φ hφ b) =
      (limit.lift (AdicCompletion.quotientTower I) (towerCone I B φ hφ)).hom b :=
    (ringLimitEquiv I).apply_symm_apply _
  rw [← limitProj_ringLimitEquiv I n (liftOfTower I B φ hφ b), h1]
  -- the motive's argument is typed at the `⟶` spelling; `congrFun` cannot see through it
  exact congrArg (fun m : CommRingCat.of B ⟶ (AdicCompletion.quotientTower I).obj ⟨n⟩ =>
    m.hom b) (limit.lift_π (towerCone I B φ hφ) (⟨n⟩ : ℕᵒᵖ))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Every ring homomorphism gives a compatible family**, namely its reductions. So the hypothesis
of `existsUnique_thickeningMap_comp` is satisfiable for any `B` and any `ψ : B →+* R`. -/
theorem factorPow_comp_mk_comp (ψ : B →+* R) (n : ℕ) :
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp
        ((Ideal.Quotient.mk (I ^ (n + 1))).comp ψ) =
      (Ideal.Quotient.mk (I ^ n)).comp ψ := by
  refine RingHom.ext fun b => ?_
  -- unfolding `factorPow` first pins down `factor_mk`'s ideal argument, which instance search
  -- otherwise cannot determine
  simp only [RingHom.comp_apply, Ideal.Quotient.factorPow]
  exact Ideal.Quotient.factor_mk _ _

/-- **`liftOfTower` inverts the canonical family**: the lift of the reductions of `ψ` is `ψ`.
Two elements of `R` with the same reductions modulo every `Iⁿ` are equal, by Hausdorffness of the
`I`-adic topology. -/
theorem liftOfTower_mk_comp (ψ : B →+* R) :
    liftOfTower I B (fun n => (Ideal.Quotient.mk (I ^ n)).comp ψ)
        (factorPow_comp_mk_comp I B ψ) = ψ := by
  refine RingHom.ext fun b => ?_
  exact IsHausdorff.eq_of_mk_pow_eq I fun n =>
    mk_liftOfTower I B _ (factorPow_comp_mk_comp I B ψ) n b

/-- **The existence half of the colimit property** (EGA I, 10.6.7): a compatible family of
morphisms out of the infinitesimal thickenings of `Spf R` comes from a **unique** morphism out of
`Spf R` itself.

Existence is `liftOfTower` — the family is a cone over the quotient tower, and completeness of `R`
lifts it — and uniqueness is `hom_ext_thickeningMap`
(`FormalSchemes/IndSchemeThickening.lean`). The two halves meet through
`thickeningMap_comp_specHomEquiv_symm`.

Note the index shift: `thickeningMap I n` sees `φ (n + 1)`, since `quotientTower I` has level `n`
equal to `R ⧸ Iⁿ`. -/
theorem existsUnique_thickeningMap_comp (φ : ∀ n : ℕ, B →+* R ⧸ I ^ n)
    (hφ : ∀ n : ℕ, (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (φ (n + 1)) = φ n) :
    ∃! g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B),
      ∀ n : ℕ, thickeningMap I n ≫ g =
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (φ (n + 1))) := by
  refine ⟨(specHomEquiv I B).symm (liftOfTower I B φ hφ), fun n => ?_, fun g hg => ?_⟩
  · rw [thickeningMap_comp_specHomEquiv_symm]
    exact congrArg (fun ψ : B →+* R ⧸ I ^ (n + 1) => Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom ψ)) (RingHom.ext fun b => mk_liftOfTower I B φ hφ (n + 1) b)
  · refine hom_ext_thickeningMap I B g _ fun n => ?_
    rw [hg n, thickeningMap_comp_specHomEquiv_symm]
    exact congrArg (fun ψ : B →+* R ⧸ I ^ (n + 1) => Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom ψ)) (RingHom.ext fun b => (mk_liftOfTower I B φ hφ (n + 1) b).symm)

/-! ### A concrete witness

Every statement above is an equation or an `∃!`, so the vacuity risk is not the usual one. It is
that `[IsAdicRing I]` might only ever be instantiated at `I = ⊥`, where all the thickenings are
`Spec R` and the whole file degenerates. The `2`-adic integers rule that out — the ideal is nonzero
by `FormalSpectrum.twoAdicIdeal_ne_bot` (`FormalSchemes/TwoAdicWitness.lean`) — so the tower is
`ℤ ⧸ 2ⁿ`, genuinely infinite, and the thickenings are smaller than `Spf ℤ^` as ringed spaces. -/

section Witness

attribute [local instance] isAdicRing_twoAdicIdeal

/-- **The lift of the reductions of `ℤ → ℤ₂` is `ℤ → ℤ₂` itself.** -/
example : liftOfTower twoAdicIdeal ℤ
      (fun n => (Ideal.Quotient.mk (twoAdicIdeal ^ n)).comp
        (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)))
      (factorPow_comp_mk_comp twoAdicIdeal ℤ _) =
    (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)) :=
  liftOfTower_mk_comp twoAdicIdeal ℤ _

/-- **There is a unique `Spf ℤ₂ ⟶ Spec ℤ` restricting to the given family on every thickening.**
Note that the family is supplied explicitly: higher-order unification cannot solve `?φ (n + 1)`
against the expression in the statement. -/
example : ∃! g : locallyRingedSpaceObj twoAdicIdeal ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of ℤ),
    ∀ n : ℕ, thickeningMap twoAdicIdeal n ≫ g =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom
        ((Ideal.Quotient.mk (twoAdicIdeal ^ (n + 1))).comp
          (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)))) :=
  existsUnique_thickeningMap_comp twoAdicIdeal ℤ
    (fun n => (Ideal.Quotient.mk (twoAdicIdeal ^ n)).comp
      (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)))
    (factorPow_comp_mk_comp twoAdicIdeal ℤ _)

end Witness

end FormalSpectrum

end
