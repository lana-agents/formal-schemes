import FormalSchemes.IndSchemeExistenceGeometric
import FormalSchemes.ThickeningCocone
import FormalSchemes.TwoAdicWitness

set_option linter.style.header false

/-!
# The colimit property of `Spf R` as a bijection (EGA I, 10.6.7)

`Spf R` is the colimit of its infinitesimal thickenings `Spec (R ⧸ I ^ (n + 1))`, and for an affine
target that statement is a **bijection**

```
(Spf R ⟶ Spec B)  ≃  { compatible families of morphisms Spec (R ⧸ I ^ (n + 1)) ⟶ Spec B }
```

which is what this file builds, as `FormalSpectrum.thickeningRestrictionEquiv`.

## Why an `Equiv` and not the `∃!` we already had

`FormalSchemes/IndSchemeExistenceGeometric.lean` proves
`existsUnique_thickeningMap_comp_of_specHom`: for every compatible family there is a unique morphism
restricting to it. That is the same mathematical content, and it is not the same *object*. An `∃!`
does not hand a consumer the inverse construction, does not compose with other equivalences, and
cannot be transported along one; and instantiating it requires writing the family out explicitly,
because higher-order unification cannot solve `?f (n + 1)` (a warning its own docstring carries).
Packaging it as an `Equiv` fixes all four at once — inside this file the warning already stops
biting, since `f.1` is a variable rather than a pattern.

## The cocone equation, and its first consumer

The forward map sends `g` to `fun n => thickeningMap I n ≫ g`, and the compatibility of that family
is precisely `FormalSpectrum.thickeningMap_comp` from `FormalSchemes/ThickeningCocone.lean`:

```lean
Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ thickeningMap I (n + 1) = thickeningMap I n
```

**That lemma had no consumers before this file.** `ThickeningCocone.lean` landed in July with the
genuine equation of morphisms of locally ringed spaces, and the whole `IndScheme*` layer was
subsequently built around it rather than on it, routing every compatibility argument through the
ring side. Here the geometric form is what the definition needs, and the compatibility proof is one
rewrite.

## Relation to the ring-side bijection

`specHomEquiv` (`FormalSchemes/IndScheme.lean`) already identifies `Spf R ⟶ Spec B` with `B →+* R`.
`thickeningRestrictionEquiv_specHomEquiv_symm` says the two bijections agree: the family attached to
a ring homomorphism `ψ` by restriction to the thickenings is the family of its reductions,
`specFamily`. Without that comparison the new `Equiv` would be a parallel construction that happens
to have the same source; with it, it is recognisably the same object seen through the tower.

## Main definitions and results

* `FormalSpectrum.ThickeningFamily`: compatible families out of the thickenings.
* `FormalSpectrum.thickeningRestrictionEquiv`: **the bijection**, EGA I 10.6.7 for affine targets.
* `FormalSpectrum.thickeningRestrictionEquiv_apply` and
  `FormalSpectrum.thickeningMap_comp_thickeningRestrictionEquiv_symm`: the two computation rules,
  which are what downstream should cite rather than unfolding the `Equiv`.
* `FormalSpectrum.thickeningRestrictionEquiv_specHomEquiv_symm`: it extends `specHomEquiv`.

## Scope

Affine targets only — in *this* file. Both of the things this section used to describe as open have
since landed, in modules that import this one, and are named here so that the restriction above is
not read as a statement about the tree:

* the general target, `thickeningRestrictionEquivLRS`
  (`FormalSchemes/IndSchemeColimitEquivLRS.lean`), which is EGA I 10.6.10 for any locally ringed
  space `X` carrying an affine open cover;
* the reconciliation with `specHomLimitEquiv` (`FormalSchemes/IndSchemeLimit.lean`) — a subtype of
  families versus a `CategoryTheory.limit` — which is `thickeningFamilyLimitEquiv`
  (`FormalSchemes/IndSchemeFamilyLimit.lean`) for an affine target and `spfHomLimitEquivLRS`
  (`FormalSchemes/IndSchemeFamilyLimitLRS.lean`) for a general one.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.7).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (B : Type u) [CommRing B]

/-- **A compatible family of morphisms out of the infinitesimal thickenings of `Spf R`**: a
morphism `Spec (R ⧸ I ^ (n + 1)) ⟶ Spec B` for every `n`, compatible with the transition maps of
the tower.

This is the right-hand side of EGA I 10.6.7 for an affine target. The compatibility is phrased
through `stepRingHom`, in the same direction as
`existsUnique_thickeningMap_comp_of_specHom`'s hypothesis: `Spec (stepRingHom I n)` goes from the
`n`-th thickening to the `(n + 1)`-st, so composing it with `f (n + 1)` lands back on `f n`. -/
def ThickeningFamily : Type u :=
  { f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of B) //
    ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n }

/-- **Restricting a morphism out of `Spf R` to the thickenings.** The forward map of the
bijection; that the resulting family is compatible is `thickeningMap_comp`, the cocone equation of
`FormalSchemes/ThickeningCocone.lean`, and this is that lemma's first consumer. -/
def restrictToThickenings
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) :
    ThickeningFamily I B :=
  ⟨fun n => thickeningMap I n ≫ g, fun n => by rw [← Category.assoc, thickeningMap_comp]⟩

/-- **`Spf R` is the colimit of its infinitesimal thickenings** (EGA I, 10.6.7), for an affine
target: restriction to the thickenings is a bijection from `Spf R ⟶ Spec B` onto the compatible
families.

Both directions come from `existsUnique_thickeningMap_comp_of_specHom`. Note that its `∃!` unfolds
to `∃ x, p x ∧ ∀ y, p y → y = x`, so the uniqueness clause proves `g = choose` and the round trip
on the left needs the symmetric form. -/
def thickeningRestrictionEquiv :
    (locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) ≃
      ThickeningFamily I B where
  toFun := restrictToThickenings I B
  invFun f := (existsUnique_thickeningMap_comp_of_specHom I B f.1 f.2).choose
  left_inv g := ((existsUnique_thickeningMap_comp_of_specHom I B _
    (restrictToThickenings I B g).2).choose_spec.2 g fun _ => rfl).symm
  right_inv f := Subtype.ext (funext fun n =>
    (existsUnique_thickeningMap_comp_of_specHom I B f.1 f.2).choose_spec.1 n)

/-- **Computation rule, forward**: the `n`-th member of the family attached to `g` is the
restriction of `g` to the `n`-th thickening. Cite this rather than unfolding the `Equiv`. -/
theorem thickeningRestrictionEquiv_apply
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) (n : ℕ) :
    (thickeningRestrictionEquiv I B g).1 n = thickeningMap I n ≫ g := rfl

/-- **Computation rule, backwards**: the morphism glued from a compatible family restricts on the
`n`-th thickening to the family's `n`-th member. This is the existence clause of
`existsUnique_thickeningMap_comp_of_specHom`, and it is the rule downstream will actually use. -/
theorem thickeningMap_comp_thickeningRestrictionEquiv_symm (f : ThickeningFamily I B) (n : ℕ) :
    thickeningMap I n ≫ (thickeningRestrictionEquiv I B).symm f = f.1 n :=
  (existsUnique_thickeningMap_comp_of_specHom I B f.1 f.2).choose_spec.1 n

/-- **The family of reductions of a ring homomorphism** `ψ : B →+* R`: the canonical compatible
family, and the witness that `ThickeningFamily I B` is not empty for any `B` admitting a map to
`R`. Compatibility is `specMap_mk_comp_compatible`. -/
def specFamily (ψ : B →+* R) : ThickeningFamily I B :=
  ⟨fun n => Spec.locallyRingedSpaceMap
    (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1))).comp ψ)),
   specMap_mk_comp_compatible I B ψ⟩

/-- **The bijection extends the ring-side one.** The morphism `Spf R ⟶ Spec B` attached to
`ψ : B →+* R` by `specHomEquiv` restricts on the thickenings to the family of reductions of `ψ`.

This is what makes `thickeningRestrictionEquiv` the same object as `specHomEquiv` seen through the
tower, rather than a second bijection out of the same source that happens to exist. -/
theorem thickeningRestrictionEquiv_specHomEquiv_symm (ψ : B →+* R) :
    thickeningRestrictionEquiv I B ((specHomEquiv I B).symm ψ) = specFamily I B ψ :=
  Subtype.ext (funext fun n => thickeningMap_comp_specHomEquiv_symm I B ψ n)

section Nonvacuity

/-! ### Non-vacuity

`[IsAdicRing I]` does **not** exclude `I = ⊥`; at `⊥` it degenerates to discreteness of `R`
(`is_bot_adic_iff`, which is the whole content of `instIsAdicRingBotOfDiscreteTopology`,
`FormalSchemes/AdicRing.lean`), and there every thickening is `Spec R` itself and the bijection
says nothing. The shared `2`-adic witness exhibits it away from `⊥`, and that is now a theorem
rather than a claim: `FormalSpectrum.twoAdicIdeal_ne_bot`
(`FormalSchemes/TwoAdicWitness.lean`). -/

attribute [local instance] isAdicRing_twoAdicIdeal

/-- **The bijection at a genuinely adic ring**: the `2`-adic integers, with `B = ℤ`. -/
example : (locallyRingedSpaceObj twoAdicIdeal ⟶
    Spec.locallyRingedSpaceObj (CommRingCat.of ℤ)) ≃ ThickeningFamily twoAdicIdeal ℤ :=
  thickeningRestrictionEquiv twoAdicIdeal ℤ

/-- And it has a point: the family of reductions of the canonical map `ℤ → ℤ^`. -/
example : ThickeningFamily twoAdicIdeal ℤ :=
  specFamily twoAdicIdeal ℤ (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ))

end Nonvacuity

end FormalSpectrum
