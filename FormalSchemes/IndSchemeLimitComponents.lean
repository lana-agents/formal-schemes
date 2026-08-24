import FormalSchemes.IndSchemeLimit
import FormalSchemes.IndSchemeThickening

set_option linter.style.header false

/-!
# The components of `specHomLimitEquiv` are the thickening restrictions (EGA I, 10.6.7)

`FormalSchemes/IndSchemeLimit.lean` builds

```
specHomLimitEquiv : Hom_{LRS}(Spf R, Spec B) ≃ lim_n (B →+* R ⧸ Iⁿ)
```

as a chain of four abstract equivalences — `specHomEquiv`, a repackaging, completeness of `R`, and
`coyoneda` preserving limits — and its module docstring reads that as *"`Spf R` is the filtered
colimit of its infinitesimal thickenings, so mapping out of it is the limit over `n` of mapping out
of each thickening"*. Nothing in that construction says what the components of the equivalence are,
so the sentence was, strictly, a statement about two sets being in bijection.

`FormalSchemes/IndSchemeThickening.lean` supplied the geometric legs: restricting `g` along
`thickeningMap I n` is `Spec` of the reduction of `specHomEquiv I B g` modulo `I ^ (n + 1)`. This
file identifies those legs with the limit's projections, which is what makes the sentence literally
true:

```
limit.π _ ⟨n⟩ (specHomLimitEquiv I B g) = ofHom (mod I ^ n ∘ specHomEquiv I B g)
thickeningMap I n ≫ g = Spec (limit.π _ ⟨n + 1⟩ (specHomLimitEquiv I B g))
```

## The index shift

`AdicCompletion.quotientTower I` has level `n` equal to `R ⧸ Iⁿ`
(`FormalSchemes/AdicCompletionLimit.lean`), whereas `thickeningMap I n` lands on
`Spec (R ⧸ I ^ (n + 1))`. **So the geometric statement pairs `limit.π _ ⟨n + 1⟩ with
`thickeningMap I n`**, and the missing level is `π ⟨0⟩`, whose target `R ⧸ I⁰ = R ⧸ ⊤` is the zero
ring (`subsingleton_quotient_pow_zero` below) and which therefore carries no information. This is
the same shift, for the same reason, that `AdicCompletionLimit.lean`'s "shifted tower" section
discusses: a tower and its shift have the same limit, and the level-0 term is trivial.

## Main results

* `FormalSpectrum.limitProj_ringLimitEquiv`: the `n`-th projection of the completeness isomorphism
  `R ≃+* lim_n R ⧸ Iⁿ` is reduction modulo `Iⁿ`.
* `FormalSpectrum.limit_π_specHomLimitEquiv`: **the component rule** — the `n`-th projection of
  `specHomLimitEquiv I B g` is `specHomEquiv I B g` followed by reduction modulo `Iⁿ`.
* `FormalSpectrum.thickeningMap_comp_eq_limit_π`: **the geometric reading** — restriction of `g`
  to the `n`-th infinitesimal thickening is `Spec` of the `(n + 1)`-st component of
  `specHomLimitEquiv I B g`.
* `FormalSpectrum.subsingleton_quotient_pow_zero`: the level-0 term of the tower is the zero ring.

## Implementation note

`IsLimit.conePointUniqueUpToIso_hom_comp` is an equality of morphisms in `Type u`, and applying it
at a point is the one fiddly step. `congrFun` does **not** work: unification cannot see through
`X ⟶ Y` to `X → Y` while solving for the motive of `congrFun`, and the error is an application type
mismatch naming the cone rather than anything about functions. `congrArg` with the motive's argument
**typed explicitly at the `⟶` spelling** — `fun (m : (…mapCone…).pt ⟶ (…).obj ⟨n⟩) => m u` — does
work, because there the type is given rather than solved for. Note the domain has to be written as
`(…mapCone (limit.cone …)).pt`, not as the definitionally equal
`CommRingCat.of B ⟶ limit (quotientTower I)`; spelling it the second way reintroduces the same
mismatch.

For the same reason `rw` is unusable on the unfolded `specHomLimitEquiv`: the term is only
type-correct after unfolding `.pt`, so every rewrite reports "did not find an occurrence" with an
`instances`-transparency note attached. As in `FormalSchemes/IndSchemeThickening.lean`, the fix is
`exact`/`Eq.trans`, not a transparency `set_option` — this file needs none.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.7).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- **The components of the completeness isomorphism are the reductions.** The `n`-th projection of
`R ≃+* lim_n R ⧸ Iⁿ` sends `r` to its class modulo `Iⁿ`. Unfold `ringLimitEquiv` to
`toLimitHom ∘ ofAlgEquiv` and apply `limitProj_toLimitHom` and `evalₐ_of`. -/
theorem limitProj_ringLimitEquiv (n : ℕ) (r : R) :
    AdicCompletion.limitProj I n (ringLimitEquiv I r) = Ideal.Quotient.mk (I ^ n) r := by
  rw [ringLimitEquiv]
  change AdicCompletion.limitProj I n
    (AdicCompletion.limitRingEquiv I (AdicCompletion.ofAlgEquiv (S := R) I r)) = _
  rw [AdicCompletion.limitRingEquiv]
  change AdicCompletion.limitProj I n
    (AdicCompletion.toLimitHom I (AdicCompletion.ofAlgEquiv (S := R) I r)) = _
  rw [AdicCompletion.limitProj_toLimitHom, AdicCompletion.ofAlgEquiv_apply,
    AdicCompletion.evalₐ_of]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The level-0 term of the quotient tower is the zero ring: `I ^ 0 = ⊤`. This is why the shift
between `quotientTower`'s indexing and `thickeningMap`'s loses nothing. -/
theorem subsingleton_quotient_pow_zero : Subsingleton (R ⧸ I ^ 0) :=
  Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])

variable (B : Type u) [CommRing B]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The comparison isomorphism between the `coyoneda`-image of the limit cone and the limit cone of
the composed functor is compatible with the projections, read at a point. -/
private theorem limit_π_conePointUniqueUpToIso (n : ℕ)
    (u : CommRingCat.of B ⟶ (limit (AdicCompletion.quotientTower I) : CommRingCat)) :
    limit.π (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))) ⟨n⟩
        ((IsLimit.conePointUniqueUpToIso
          (isLimitOfPreserves (coyoneda.obj (op (CommRingCat.of B)))
            (limit.isLimit (AdicCompletion.quotientTower I)))
          (limit.isLimit
            (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))))).hom u) =
      u ≫ limit.π (AdicCompletion.quotientTower I) ⟨n⟩ := by
  have hP := IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitOfPreserves (coyoneda.obj (op (CommRingCat.of B)))
      (limit.isLimit (AdicCompletion.quotientTower I)))
    (limit.isLimit (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))))
    ⟨n⟩
  exact congrArg (fun (m : ((coyoneda.obj (op (CommRingCat.of B))).mapCone
      (limit.cone (AdicCompletion.quotientTower I))).pt ⟶
      (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))).obj ⟨n⟩) =>
      m u) hP

/-- **The component rule for `specHomLimitEquiv`** (EGA I, 10.6.7): the `n`-th component of the
compatible family attached to `g : Spf R ⟶ Spec B` is the ring homomorphism `specHomEquiv I B g`
followed by reduction modulo `Iⁿ`.

This is what makes `FormalSchemes/IndSchemeLimit.lean`'s `lim_n Hom(Spec (R ⧸ Iⁿ), Spec B)` a
statement about the tower rather than an abstract bijection: the equivalence is not merely *some*
bijection onto the limit, it is the one whose legs are reduction. -/
theorem limit_π_specHomLimitEquiv
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) (n : ℕ) :
    limit.π (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))) ⟨n⟩
        (specHomLimitEquiv I B g) =
      CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ n)).comp (specHomEquiv I B g)) := by
  simp only [specHomLimitEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp]
  refine (limit_π_conePointUniqueUpToIso I B n
    (CommRingCat.ofHom (specHomEquiv I B g) ≫ (ringLimitIso I).hom)).trans ?_
  refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
  exact limitProj_ringLimitEquiv I n (specHomEquiv I B g b)

/-- **Mapping out of `Spf R` is the limit over the thickenings**, geometrically: restricting
`g : Spf R ⟶ Spec B` along the canonical `Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R` is `Spec` of the
`(n + 1)`-st component of `specHomLimitEquiv I B g`.

Note the index shift discussed in the module docstring: `thickeningMap I n` pairs with
`limit.π _ ⟨n + 1⟩`, because `quotientTower I` has level `n` equal to `R ⧸ Iⁿ`. -/
theorem thickeningMap_comp_eq_limit_π
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) (n : ℕ) :
    thickeningMap I n ≫ g =
      Spec.locallyRingedSpaceMap
        (limit.π (AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B)))
          ⟨n + 1⟩ (specHomLimitEquiv I B g)) := by
  rw [limit_π_specHomLimitEquiv I B g (n + 1), thickeningMap_comp_specHom]
  rfl

section Nonvacuity

attribute [local instance] isAdicRing_twoAdicIdeal

/-- **The statements above are not vacuous, and not only for discrete rings.** At `R = ℤ^` the
`2`-adic integers, with `I = (2)·ℤ^`, the tower is `ℤ ⧸ 2ⁿ` and the thickenings are genuinely
smaller than `Spf ℤ^` as ringed spaces; the canonical `Spf ℤ^ ⟶ Spec ℤ` restricts on the `n`-th
thickening to `Spec` of the `(n + 1)`-st component of its compatible family. -/
example (n : ℕ) :
    thickeningMap (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) n ≫
        (specHomEquiv (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) ℤ).symm
          (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)) =
      Spec.locallyRingedSpaceMap
        (limit.π (AdicCompletion.quotientTower
            (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) ⋙
          coyoneda.obj (op (CommRingCat.of ℤ))) ⟨n + 1⟩
          (specHomLimitEquiv (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) ℤ
            ((specHomEquiv (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) ℤ).symm
              (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ))))) :=
  thickeningMap_comp_eq_limit_π _ ℤ _ n

end Nonvacuity

end FormalSpectrum
