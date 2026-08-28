import FormalSchemes.IndSchemeExistence

set_option linter.style.header false

/-!
# The existence half of the colimit property, for families of morphisms (EGA I, 10.6.7)

`FormalSchemes/IndSchemeExistence.lean` proved that a compatible family of **ring**
homomorphisms `φ n : B →+* R ⧸ Iⁿ` comes from a unique morphism `Spf R ⟶ Spec B`
(`existsUnique_thickeningMap_comp`). A consumer of the colimit property does not usually hold such
a family: it holds a family of **morphisms of locally ringed spaces**

```
f n : Spec (R ⧸ I ^ (n + 1)) ⟶ Spec B
```

out of the infinitesimal thickenings, compatible with the transition maps
`Spec.locallyRingedSpaceMap (stepRingHom I n)`. Manufacturing `φ` from `f` is the step this file
supplies, and with it the colimit property takes its geometric form:

```
existsUnique_thickeningMap_comp_of_specHom :
  ∃! g : Spf R ⟶ Spec B, ∀ n, thickeningMap I n ≫ g = f n
```

Together with `hom_ext_thickeningMap` (`FormalSchemes/IndSchemeThickening.lean`) that is the
statement that `Spf R` **is** the colimit of its infinitesimal thickenings, for affine targets.

## How the family is turned into ring maps

`Spec.toLocallyRingedSpace` is full and faithful, so each `f n` is `Spec` of a unique ring map
`specPreimage I B n (f n)`, and the compatibility of `f` transports to a compatibility of those
ring maps (`specPreimage_comp_stepRingHom`). The only friction is `ᵒᵖ` bookkeeping:
`Functor.preimage` hands back a morphism of `CommRingCatᵒᵖ`, and transporting an equation back
**down** is `Quiver.Hom.op_inj (Spec.toLocallyRingedSpace.map_injective ·)` — in that order, the
idiom already used in `FormalSchemes/IndSchemeThickening.lean`. Note also that
`Spec.locallyRingedSpaceMap_comp` is contravariant.

## The index shift, and why level `0` is free

`existsUnique_thickeningMap_comp` consumes a family indexed by `R ⧸ Iⁿ` starting at `n = 0`,
whereas `f n` lands on `R ⧸ I ^ (n + 1)`. `paddedFamily` closes the gap by defining level `0` as
`factorPow` of level `1` — the same padding trick as `AdicCompletionLimit.lean`'s
`towerProjFamily`. Choosing that value rather than an arbitrary map into the zero ring
`R ⧸ I⁰` makes the level-`0` compatibility **`rfl`**, and `paddedFamily _ (n + 1)` reduces to the
`n`-th ring map definitionally, so no proof in this file case-splits on `n = 0`.

## Main results

* `FormalSpectrum.specPreimage`, `FormalSpectrum.specMap_specPreimage`: the ring map underlying a
  morphism into an affine scheme.
* `FormalSpectrum.specPreimage_comp_stepRingHom`: compatibility of the family transports down.
* `FormalSpectrum.existsUnique_thickeningMap_comp_of_specHom`: **the existence half of the colimit
  property, geometrically.**
* `FormalSpectrum.specMap_mk_comp_compatible`: the canonical compatible family of morphisms
  attached to a ring map `B →+* R`, so the hypothesis above is satisfiable.

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
/-- **The ring homomorphism underlying a morphism `Spec (R ⧸ I ^ (n + 1)) ⟶ Spec B`**, by fullness
of `Spec.toLocallyRingedSpace`. `Functor.preimage` lands in `CommRingCatᵒᵖ`, whence the `unop`. -/
def specPreimage (n : ℕ)
    (f : Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of B)) :
    CommRingCat.of B ⟶ CommRingCat.of (R ⧸ I ^ (n + 1)) :=
  (Spec.toLocallyRingedSpace.preimage f).unop

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `specPreimage` is a section of `Spec`. -/
@[simp]
theorem specMap_specPreimage (n : ℕ)
    (f : Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of B)) :
    Spec.locallyRingedSpaceMap (specPreimage I B n f) = f :=
  Spec.toLocallyRingedSpace.map_preimage f

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Compatibility of a family of morphisms transports to its underlying ring maps**, by
faithfulness of `Spec.toLocallyRingedSpace`. -/
theorem specPreimage_comp_stepRingHom
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) (n : ℕ) :
    specPreimage I B (n + 1) (f (n + 1)) ≫ stepRingHom I n = specPreimage I B n (f n) := by
  refine Quiver.Hom.op_inj (Spec.toLocallyRingedSpace.map_injective ?_)
  change Spec.locallyRingedSpaceMap (specPreimage I B (n + 1) (f (n + 1)) ≫ stepRingHom I n) =
    Spec.locallyRingedSpaceMap (specPreimage I B n (f n))
  rw [Spec.locallyRingedSpaceMap_comp, specMap_specPreimage, specMap_specPreimage, hf]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A family of ring maps `B →+* R ⧸ I ^ (n + 1)` padded to one indexed by the quotient tower.**
Level `0` is `factorPow` of level `1`, which is what makes the level-`0` compatibility `rfl`; any
map into `R ⧸ I⁰` would do, since that ring is a subsingleton. -/
def paddedFamily (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ CommRingCat.of (R ⧸ I ^ (n + 1))) :
    ∀ n : ℕ, B →+* R ⧸ I ^ n
  | 0 => (Ideal.Quotient.factorPow I (Nat.le_succ 0)).comp (ψ 0).hom
  | n + 1 => (ψ n).hom

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `paddedFamily` of a family compatible with `stepRingHom` is compatible with the transition maps
of the quotient tower. The `n = 0` case is `rfl` by construction. -/
theorem paddedFamily_compat (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ CommRingCat.of (R ⧸ I ^ (n + 1)))
    (hψ : ∀ n : ℕ, ψ (n + 1) ≫ stepRingHom I n = ψ n) (n : ℕ) :
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (paddedFamily I B ψ (n + 1)) =
      paddedFamily I B ψ n := by
  cases n with
  | zero => rfl
  | succ m => exact congrArg CommRingCat.Hom.hom (hψ m)

/-- **The existence half of the colimit property, geometrically** (EGA I, 10.6.7): a family of
morphisms out of the infinitesimal thickenings of `Spf R`, compatible with the transition maps of
the tower of thickenings, comes from a **unique** morphism out of `Spf R` itself.

This is `existsUnique_thickeningMap_comp` (`FormalSchemes/IndSchemeExistence.lean`) with the family
presented geometrically; `specPreimage` and `paddedFamily` are what convert one presentation into
the other.

Beware that instantiating this `∃!` requires the family to be supplied **explicitly**:
higher-order unification cannot solve `?f (n + 1)` against an elaborated expression, and the
failure is a plain type mismatch, not a defeq problem. -/
theorem existsUnique_thickeningMap_comp_of_specHom
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) :
    ∃! g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B),
      ∀ n : ℕ, thickeningMap I n ≫ g = f n := by
  have key := existsUnique_thickeningMap_comp I B
    (paddedFamily I B fun n => specPreimage I B n (f n))
    (paddedFamily_compat I B _ (specPreimage_comp_stepRingHom I B f hf))
  refine (existsUnique_congr fun g => forall_congr' fun n => ?_).mp key
  rw [show CommRingCat.ofHom (paddedFamily I B (fun n => specPreimage I B n (f n)) (n + 1)) =
    specPreimage I B n (f n) from rfl, specMap_specPreimage]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Every ring homomorphism `ψ : B →+* R` gives a compatible family of morphisms** out of the
thickenings, namely `Spec` of its reductions. So the hypothesis of
`existsUnique_thickeningMap_comp_of_specHom` is satisfiable for any `B` and any `ψ`. -/
theorem specMap_mk_comp_compatible (ψ : B →+* R) (n : ℕ) :
    Spec.locallyRingedSpaceMap (stepRingHom I n) ≫
        Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1 + 1))).comp ψ)) =
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1))).comp ψ)) := by
  rw [← Spec.locallyRingedSpaceMap_comp]
  exact congrArg (fun τ : B →+* R ⧸ I ^ (n + 1) =>
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom τ)) (factorPow_comp_mk_comp I B ψ (n + 1))

/-! ### A concrete witness

As in `FormalSchemes/IndSchemeExistence.lean`, the risk is not that the statements are vacuous —
they are equations and an `∃!` — but that `[IsAdicRing I]` is only ever instantiated at `I = ⊥`,
where every thickening is `Spec R`. The `2`-adic integers rule that out, by
`FormalSpectrum.twoAdicIdeal_ne_bot` (`FormalSchemes/TwoAdicWitness.lean`). -/

section Witness

attribute [local instance] isAdicRing_twoAdicIdeal

/-- **There is a unique `Spf ℤ₂ ⟶ Spec ℤ` restricting on the `n`-th thickening to `Spec` of the
reduction of `ℤ → ℤ₂` modulo `2 ^ (n + 1)`.** The family is supplied explicitly, as the docstring
of `existsUnique_thickeningMap_comp_of_specHom` warns. -/
example : ∃! g : locallyRingedSpaceObj twoAdicIdeal ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of ℤ),
    ∀ n : ℕ, thickeningMap twoAdicIdeal n ≫ g =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom
        ((Ideal.Quotient.mk (twoAdicIdeal ^ (n + 1))).comp
          (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)))) :=
  existsUnique_thickeningMap_comp_of_specHom twoAdicIdeal ℤ
    (fun n => Spec.locallyRingedSpaceMap (CommRingCat.ofHom
      ((Ideal.Quotient.mk (twoAdicIdeal ^ (n + 1))).comp
        (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)))))
    (specMap_mk_comp_compatible twoAdicIdeal ℤ _)

end Witness

end FormalSpectrum

end
