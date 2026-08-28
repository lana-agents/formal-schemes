import FormalSchemes.SpfHomScheme

set_option linter.style.header false

/-!
# Naturality in `X` of EGA I, 10.6.7: `Spf R` corepresents `X ↦ lim_n Hom(Spec (R ⧸ Iⁿ), X)`

`FormalSchemes/SpfHomScheme.lean` proves, for each scheme `X` separately,

```
spfHomLimitEquivScheme :  (Spf R ⟶ X)  ≃  lim_n Hom(Spec (R ⧸ Iⁿ), X)
```

This file makes both sides functors on `Scheme.{u}` and upgrades the family of bijections to a
natural isomorphism, `FormalSpectrum.spfHomLimitNatIso`. That is the last thing umbrella 97 asks
for: EGA I 10.6.7 is a statement about a *corepresentable functor*, and a bijection stated one
object at a time is not yet that statement.

## The target functor has to be built; the source one is `coyoneda`

`homTowerLRS I X` is an `abbrev` **in** `X`, not a functor **of** `X`, so `X ↦ lim_n Hom(Spec (R ⧸
Iⁿ), X)` is not available off the shelf. It is assembled here in one line from `yoneda`:
`homTowerFunctorLRS` is `yoneda` restricted along `(thickeningTower I).op`, and the limit functor
is that composed with `lim`. Two consequences worth stating, because they are the reason this file
is short:

* **the functor laws are free** — every piece is a composite of existing functors, so no
  `map_id`/`map_comp` is proved here;
* **the action on morphisms is postcomposition**, definitionally, since that is what `yoneda.map`
  is. `limit_π_spfHomLimitFunctor_map` records it at the level of a limit component and is one
  application of `limMap_π_apply`.

The source functor needs nothing built: it is `coyoneda.obj (op (Spf R))` restricted along
`Scheme.forgetToLocallyRingedSpace`.

## Why the statement is on `Scheme` and not on `LocallyRingedSpace`

Both functors above make sense on all of `LocallyRingedSpace` — `spfHomLimitFunctorLRS` is defined
there and is used here through the restriction. What does *not* make sense there is the
isomorphism: `spfHomLimitEquivLRS` needs affine cover data as an argument, and a bare locally
ringed space carries none, so there is no family of bijections to be natural. A scheme carries the
data in its `local_affine` field, which is what `FormalSchemes/SpfHomScheme.lean` discharges.

The choice made there is per object and arbitrary — `schemeCoverOpen X` picks one affine
neighbourhood per point of `X` by `Classical.choice`, and nothing relates the choice at `X` to the
choice at `Y` along a morphism `X ⟶ Y`. **That is not an obstruction to naturality**, and the
proof below does not have to compare two chosen covers: `spfHomLimitEquivScheme_eq` says the
equivalence *equals* the cover-carrying one for every cover, so no cover can occur in the forward
map, and the naturality square is checked on the forward map alone. Concretely it is
`limitLRS_ext_succ` — an element of the limit is determined by its legs at `⟨n + 1⟩` — followed by
the component rule on each side; both routes round the square are `thickeningMap I n ≫ g ≫ f` and
the square closes by associativity.

## What the "`IsColimit` restricted to schemes" sentence meant, settled

`FormalSchemes/IndSchemeColimitEquivLRS.lean` and `FormalSchemes/IndSchemeFamilyLimitLRS.lean`
both carried, until this file landed, a sentence ending *"Restricted to schemes it should follow;
that is a separate row."* It does not follow, and not because of a missing proof:

* `CategoryTheory.Limits.IsColimit t` for a cocone `t` in `LocallyRingedSpace` quantifies over
  cocones `s` with an **arbitrary** `s.pt : LocallyRingedSpace` — that is the type of `desc`.
  Restricting the *diagram* to schemes, which the tower of thickenings already satisfies (each
  `Spec (R ⧸ Iⁿ)` is affine), does not touch that quantifier.
* An `IsColimit` **in `Scheme`** is not available either, because the vertex would have to be an
  object of `Scheme`: nothing on this tree equips `Spf R` with a `Scheme` structure, and for an
  adic ring that is not discrete one should not expect one.

So "restricted to schemes" does not name a weaker `IsColimit`; it names **corepresentability on
`Scheme`**, which is what `spfHomLimitNatIso` is and what EGA I 10.6.7 actually asserts. The
existence-and-uniqueness content, in elementary form, is
`existsUnique_hom_thickeningMap_scheme` (`FormalSchemes/SpfHomScheme.lean`): every compatible
family into a scheme factors through `Spf R` uniquely. Both docstrings now say this instead.

Nothing here rules out a genuine `IsColimit` in `LocallyRingedSpace`. It would need
`existsUnique_hom_thickeningMap` for targets carrying no cover data at all, which the tree neither
proves nor refutes.

## Main definitions and results

* `FormalSpectrum.homTowerFunctorLRS`: the tower of hom-sets as a functor of the target,
  `X ↦ (n ↦ Hom(Spec (R ⧸ Iⁿ), X))`, with `homTowerFunctorLRS_map_app_apply` saying its action is
  postcomposition.
* `FormalSpectrum.spfHomLimitFunctorLRS` and `FormalSpectrum.spfHomLimitFunctor`:
  `X ↦ lim_n Hom(Spec (R ⧸ Iⁿ), X)`, on `LocallyRingedSpace` and restricted to `Scheme`, with
  `limit_π_spfHomLimitFunctor_map` as the component rule for the action on morphisms.
* `FormalSpectrum.spfHomFunctor`: `X ↦ Hom(Spf R, X)` on `Scheme`, i.e. `coyoneda` at `Spf R`.
* `FormalSpectrum.spfHomLimitEquivScheme_naturality`: **the naturality square**, as a standalone
  equation between morphisms of locally ringed spaces, so that a consumer with a specific
  `f : X ⟶ Y` need not go through the `NatIso`.
* `FormalSpectrum.spfHomLimitNatIso`: **umbrella 97's headline as a natural isomorphism**,
  `spfHomFunctor ≅ spfHomLimitFunctor`, with `spfHomLimitNatIso_hom_app_apply` and
  `spfHomLimitNatIso_inv_app_apply` identifying its components with `spfHomLimitEquivScheme`.

## Scope

Naturality in `R` and in `I` is not packaged, and neither is naturality in `B` of the affine
`specHomLimitEquiv` (`FormalSchemes/IndSchemeLimit.lean`), which is a different shape: it is
contravariant and lives on the ring side, and goals 1–3 here do not make it a corollary, because
`spfHomFunctor` fixes `R` throughout.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-! ### The two functors

Both are composites of functors that already exist, so their functor laws come for free and are
not proved here. `abbrev`, matching `homTowerLRS` and `thickeningTower`, so that a goal stated
with either name is reachable from lemmas stated with the other.
-/

/-- **The tower of hom-sets as a functor of the target**: `X ↦ (n ↦ Hom(Spec (R ⧸ Iⁿ), X))`.

This is `yoneda` restricted along `(thickeningTower I).op`; its action on `f : X ⟶ Y` is
postcomposition with `f`, levelwise (`homTowerFunctorLRS_map_app_apply`). -/
abbrev homTowerFunctorLRS : LocallyRingedSpace.{u} ⥤ (ℕᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (thickeningTower I).op

/-- **`X ↦ lim_n Hom(Spec (R ⧸ Iⁿ), X)`, as a functor on locally ringed spaces.** The
isomorphism with `X ↦ Hom(Spf R, X)` is available only after restricting to schemes, see
`spfHomLimitNatIso`; the functor itself needs no cover data. -/
abbrev spfHomLimitFunctorLRS : LocallyRingedSpace.{u} ⥤ Type u :=
  homTowerFunctorLRS I ⋙ lim

/-- **`X ↦ lim_n Hom(Spec (R ⧸ Iⁿ), X)` on schemes**: the right-hand side of EGA I 10.6.7, as a
functor `Scheme.{u} ⥤ Type u`. -/
abbrev spfHomLimitFunctor : Scheme.{u} ⥤ Type u :=
  Scheme.forgetToLocallyRingedSpace ⋙ spfHomLimitFunctorLRS I

/-- **`X ↦ Hom_{LRS}(Spf R, X)` on schemes**: the left-hand side of EGA I 10.6.7. This is
`coyoneda` at `Spf R`, which is not a scheme, restricted along the forgetful functor. -/
abbrev spfHomFunctor : Scheme.{u} ⥤ Type u :=
  Scheme.forgetToLocallyRingedSpace ⋙ coyoneda.obj (op (locallyRingedSpaceObj I))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The hom-tower functor acts by postcomposition**, level by level. -/
@[simp]
theorem homTowerFunctorLRS_map_app_apply {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (n : ℕ)
    (g : (homTowerLRS I X).obj ⟨n⟩) :
    ((homTowerFunctorLRS I).map f).app ⟨n⟩ g = g ≫ f :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `Spf`-hom functor acts by postcomposition.** -/
@[simp]
theorem spfHomFunctor_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) :
    (spfHomFunctor I).map f g = g ≫ f.toLRSHom :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Component rule for the action of `spfHomLimitFunctor` on morphisms**: the `n`-th leg of
`f · u` is the `n`-th leg of `u` followed by `f`. Cite this rather than unfolding `limMap`. -/
@[simp]
theorem limit_π_spfHomLimitFunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (u : (limit (homTowerLRS I X.toLocallyRingedSpace) : Type u)) (n : ℕ) :
    limit.π (homTowerLRS I Y.toLocallyRingedSpace) ⟨n⟩ ((spfHomLimitFunctor I).map f u) =
      limit.π (homTowerLRS I X.toLocallyRingedSpace) ⟨n⟩ u ≫ f.toLRSHom :=
  limMap_π_apply _ _ _

/-! ### Naturality -/

/-- **The naturality square of EGA I 10.6.7 in the target**, as a standalone equation: restricting
`g ≫ f` to the thickenings is the same as restricting `g` and then postcomposing with `f`.

The proof compares legs: `limitLRS_ext_succ` reduces to the components at `⟨n + 1⟩`, where both
sides are `thickeningMap I n ≫ g ≫ f` by the two component rules and associativity. **No cover
data enters**, which is the point — `spfHomLimitEquivScheme` is defined through an arbitrary
per-object choice of affine cover, but `spfHomLimitEquivScheme_eq` shows that choice cannot occur
in the forward map. -/
@[simp]
theorem spfHomLimitEquivScheme_naturality (hI : I.FG) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) :
    spfHomLimitEquivScheme I Y hI (g ≫ f.toLRSHom) =
      (spfHomLimitFunctor I).map f (spfHomLimitEquivScheme I X hI g) := by
  refine limitLRS_ext_succ I Y.toLocallyRingedSpace fun n => ?_
  rw [limit_π_spfHomLimitEquivScheme, limit_π_spfHomLimitFunctor_map,
    limit_π_spfHomLimitEquivScheme]
  exact (Category.assoc _ _ _).symm

/-- **Umbrella 97's headline as a natural isomorphism** (EGA I, 10.6.7):

```
Hom_{LRS}(Spf R, -)  ≅  lim_n Hom_{LRS}(Spec (R ⧸ Iⁿ), -)      on Scheme.{u}
```

`Spf R` corepresents the limit functor. The component at `X` is `spfHomLimitEquivScheme I X hI`
(`spfHomLimitNatIso_hom_app_apply`), so nothing is lost against the object-by-object form, and the
naturality square is `spfHomLimitEquivScheme_naturality`.

This is the statement that "an `IsColimit` restricted to schemes" was reaching for; the module
docstring records why that phrase does not name a theorem and this one does. -/
def spfHomLimitNatIso (hI : I.FG) : spfHomFunctor I ≅ spfHomLimitFunctor I :=
  NatIso.ofComponents (fun X => (spfHomLimitEquivScheme I X hI).toIso)
    fun {X Y} f => by ext g; exact spfHomLimitEquivScheme_naturality I hI f g

/-- The forward component of `spfHomLimitNatIso` is `spfHomLimitEquivScheme`. -/
@[simp]
theorem spfHomLimitNatIso_hom_app_apply (hI : I.FG) (X : Scheme.{u})
    (g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) :
    (spfHomLimitNatIso I hI).hom.app X g = spfHomLimitEquivScheme I X hI g :=
  rfl

/-- The backward component of `spfHomLimitNatIso` is `spfHomLimitEquivScheme.symm`: the morphism
`Spf R ⟶ X` glued from a point of the limit. -/
@[simp]
theorem spfHomLimitNatIso_inv_app_apply (hI : I.FG) (X : Scheme.{u})
    (u : (limit (homTowerLRS I X.toLocallyRingedSpace) : Type u)) :
    (spfHomLimitNatIso I hI).inv.app X u = (spfHomLimitEquivScheme I X hI).symm u :=
  rfl

/-- **The naturality square on the inverse**: gluing a point of the limit and then postcomposing
with `f` is gluing the pushed-forward point. Stated separately because a consumer producing
morphisms out of `Spf R` uses this direction, and extracting it from the `NatIso` means
transporting along `Iso.inv`. -/
theorem spfHomLimitEquivScheme_symm_naturality (hI : I.FG) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (u : (limit (homTowerLRS I X.toLocallyRingedSpace) : Type u)) :
    (spfHomLimitEquivScheme I X hI).symm u ≫ f.toLRSHom =
      (spfHomLimitEquivScheme I Y hI).symm ((spfHomLimitFunctor I).map f u) := by
  have h := spfHomLimitEquivScheme_naturality I hI f ((spfHomLimitEquivScheme I X hI).symm u)
  rw [Equiv.apply_symm_apply] at h
  exact (Equiv.eq_symm_apply _).2 h

end FormalSpectrum

end
