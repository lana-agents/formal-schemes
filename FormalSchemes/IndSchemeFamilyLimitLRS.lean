import FormalSchemes.EmptyLocallyRingedSpace
import FormalSchemes.IndSchemeColimitEquivLRS
import FormalSchemes.IndSchemeFamilyLimit

set_option linter.style.header false

/-!
# The `limit` form of the colimit property, for a general target (EGA I, 10.6.7)

`FormalSchemes/IndSchemeColimitEquivLRS.lean` packages the colimit property of `Spf R` for a
general target as a bijection onto a **subtype**:

```
(Spf R ⟶ X)  ≃  ThickeningFamilyLRS I X
```

Umbrella 97's literal shape is a `CategoryTheory.Limits.limit`:

```
(Spf R ⟶ X)  ≃  lim_n Hom(Spec (R ⧸ Iⁿ), X)
```

This file supplies that form — `FormalSpectrum.spfHomLimitEquivLRS` — together with the component
rule and the extensionality principle that make it usable without unfolding.

## Why the affine route does not transfer

For an affine target the limit form is `specHomLimitEquiv` (`FormalSchemes/IndSchemeLimit.lean`),
built from `specHomEquiv : (Spf R ⟶ Spec B) ≃ (B →+* R)` together with `R ≅ lim_n R ⧸ Iⁿ` in
`CommRingCat`. Both ingredients live on the ring side, which a bare locally ringed space does not
have, so the composite route is unavailable rather than merely inconvenient: there is nothing to
compose with. The limit is compared with `ThickeningFamilyLRS I X` directly, through
`CategoryTheory.Limits.Types.limitEquivSections`, and two things then have to be supplied that the
affine route never has to state.

**Successor-only compatibility, promoted to every `m ≤ n`.** A `ThickeningFamilyLRS` is compatible
one step at a time; a section of `homTowerLRS I X` is compatible along *every* morphism of `ℕᵒᵖ`.
`thickeningLeg_comp` closes the gap by `Nat.le_induction`, with the consecutive case
`thickeningLeg_step` stated separately — the same shape as `AdicCompletion.quotientTower_map`
(`FormalSchemes/AdicCompletionLimit.lean`), which does the tower half of this induction.

**The level-`0` leg.** `homTowerLRS` has level `n` equal to `Hom(Spec (R ⧸ Iⁿ), X)` while a
`ThickeningFamilyLRS` starts at `R ⧸ I¹`, so `f.1 n` pairs with the leg at `⟨n + 1⟩` and the leg at
`⟨0⟩` is matched by nothing — the same shift `FormalSchemes/IndSchemeFamilyLimit.lean` records for
the affine case. It carries no information, and here the reason is geometric rather than algebraic:
`R ⧸ I⁰` is the zero ring (`subsingleton_quotient_pow_zero`), so `PrimeSpectrum (R ⧸ I⁰)` is empty
(`PrimeSpectrum.isEmpty_iff_subsingleton`), and a locally ringed space with
empty carrier is **initial** — `AlgebraicGeometry.LocallyRingedSpace.isInitialOfIsEmpty`, which
`FormalSchemes/EmptyLocallyRingedSpace.lean` has carried since the Tate-chain gluing needed it.
So `Hom(Spec (R ⧸ I⁰), X)` is a subsingleton for *every* `X`; that is
`isInitialThickeningTowerZero`, and it is what `limitLRS_π_zero_eq` and the `right_inv` field of
`thickeningFamilySectionsEquivLRS` use. The affine analogue `limit_π_zero_eq` instead observes that
`B →+* R ⧸ I⁰` is a subsingleton because its *target* is — an argument about rings, with no
geometry in it, which does not generalise.

## The variance bookkeeping

`AdicCompletion.quotientTower I : ℕᵒᵖ ⥤ CommRingCat` is contravariant in `n` and `Spec` is
contravariant again, so the thickenings `n ↦ Spec (R ⧸ Iⁿ)` are **covariant**: the composite is
`Functor.rightOp` (which sends `Cᵒᵖ ⥤ D` to `C ⥤ Dᵒᵖ`), not `Functor.leftOp`. Homming into `X`
turns it contravariant once more:

```
thickeningTower I : ℕ ⥤ LocallyRingedSpace       homTowerLRS I X : ℕᵒᵖ ⥤ Type u
```

`homTowerLRS_map_apply` states the transition map as what it is — precomposition with the
inclusion of one thickening into the next — so no consumer has to unfold the composite.

## The cover is still scaffolding

`spfHomLimitEquivLRS` inherits `thickeningRestrictionEquivLRS`'s cover data, and does not depend on
it: `spfHomLimitEquivLRS_eq_of_cover` is an equality of `Equiv`s, proved by
`Equiv.coe_fn_injective rfl`, because the composite's forward map is
`thickeningFamilyLimitEquivLRS ∘ restrictToThickeningsLRS` and neither factor mentions the cover.

## The affine case is an instance, but only up to an isomorphism of functors

`homTower I B` and `homTowerLRS I (Spec B)` are **not** the same functor: the first has ring
homomorphisms `B →+* R ⧸ Iⁿ` for objects, the second morphisms of locally ringed spaces
`Spec (R ⧸ Iⁿ) ⟶ Spec B`. The comparison is therefore a natural isomorphism, `homTowerIsoLRS`,
whose components are `Spec` on hom-sets — bijective by `Spec.fullyFaithfulToLocallyRingedSpace`.
This is unlike `thickeningFamily_eq_thickeningFamilyLRS`, where the two family types are equal on
the nose. It induces `limitIsoLRS`, and then
`limitIsoLRS_hom_thickeningFamilyLimitEquiv` and `spfHomLimitEquivLRS_specHomLimitEquiv` say that
all three affine presentations — `specHomLimitEquiv`, `thickeningFamilyLimitEquiv` and this file's
`spfHomLimitEquivLRS` — agree at `X = Spec B`.

## Scope

Naturality in `X` is not available at this generality: the equivalence takes cover data as an
argument, so it is stated for each locally ringed space *and each cover* separately and there is
no functor for it to be natural between. At a scheme target the cover is discharged and the
naturality does exist — `FormalSchemes/SpfHomSchemeNatural.lean` proves
`FormalSpectrum.spfHomLimitNatIso`, whose component at `X` is
`FormalSchemes/SpfHomScheme.lean`'s `spfHomLimitEquivScheme`. Naturality in `B` of the affine
`specHomLimitEquiv` remains unpackaged, as `IndScheme.lean` records.

An `IsColimit` for the tower of thickenings is a different statement and is still not available;
`FormalSchemes/IndSchemeColimitEquivLRS.lean` sets out why narrowing the target to schemes does
not produce one, and why corepresentability on `Scheme` is what the narrowing actually gives.

## Main definitions and results

* `FormalSpectrum.thickeningTower`: the tower `n ↦ Spec (R ⧸ Iⁿ)` in `LocallyRingedSpace`.
* `FormalSpectrum.homTowerLRS`: the tower of hom-sets `n ↦ Hom(Spec (R ⧸ Iⁿ), X)`.
* `FormalSpectrum.isInitialThickeningTowerZero`: **the level-`0` thickening is initial**.
* `FormalSpectrum.thickeningFamilySectionsEquivLRS`: a compatible family is a section of the tower.
* `FormalSpectrum.thickeningFamilyLimitEquivLRS`: `ThickeningFamilyLRS I X ≃ lim_n Hom(…, X)`.
* `FormalSpectrum.spfHomLimitEquivLRS`: **umbrella 97's headline**,
  `(Spf R ⟶ X) ≃ lim_n Hom(Spec (R ⧸ Iⁿ), X)`, with `limit_π_spfHomLimitEquivLRS` as its
  component rule and `spfHomLimitEquivLRS_eq_of_cover` for cover-independence.
* `FormalSpectrum.limitLRS_ext_succ` and `FormalSpectrum.eq_thickeningFamilyLimitEquivLRS`: the
  components at `⟨n + 1⟩` determine an element of the limit, and determine the equivalence.
* `FormalSpectrum.homTowerIsoLRS`, `FormalSpectrum.limitIsoLRS`,
  `FormalSpectrum.limitIsoLRS_hom_thickeningFamilyLimitEquiv`,
  `FormalSpectrum.spfHomLimitEquivLRS_specHomLimitEquiv`: the affine case is this one.
* `FormalSpectrum.spfHomLimitEquivFormalLine`: the headline at the concrete witness
  `Spf ℤ⟦X⟧ ⟶ Spec ℤ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7–10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (X : LocallyRingedSpace.{u})

/-- **The tower of infinitesimal thickenings** `n ↦ Spec (R ⧸ Iⁿ)`, as a functor `ℕ ⥤
LocallyRingedSpace`. Covariant: `quotientTower` and `Spec` are each contravariant, so
`Functor.rightOp` (`Cᵒᵖ ⥤ D` to `C ⥤ Dᵒᵖ`) is the composition that applies, not `Functor.leftOp`.
An `abbrev`, so that lemmas stated with `quotientTower` apply to goals stated with this name. -/
abbrev thickeningTower : ℕ ⥤ LocallyRingedSpace.{u} :=
  (AdicCompletion.quotientTower I).rightOp ⋙ Spec.toLocallyRingedSpace

/-- **The tower of hom-sets** `n ↦ Hom(Spec (R ⧸ Iⁿ), X)`, whose limit is the right-hand side of
`spfHomLimitEquivLRS`. Contravariant, the transition maps being precomposition with the inclusions
of the thickenings (`homTowerLRS_map_apply`). At `X = Spec B` this is *not* `homTower I B` but is
naturally isomorphic to it, see `homTowerIsoLRS`. -/
abbrev homTowerLRS : ℕᵒᵖ ⥤ Type u :=
  (thickeningTower I).op ⋙ yoneda.obj X

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Level `n` of the tower of thickenings is `Spec (R ⧸ Iⁿ)`, on the nose. -/
@[simp]
theorem thickeningTower_obj (n : ℕ) :
    (thickeningTower I).obj n = Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ n)) :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Level `n` of the hom-tower is `Hom(Spec (R ⧸ Iⁿ), X)`, on the nose. Note the index: a
`ThickeningFamilyLRS` starts at `R ⧸ I¹`, so its `n`-th member sits at `⟨n + 1⟩` here. -/
@[simp]
theorem homTowerLRS_obj (n : ℕ) :
    (homTowerLRS I X).obj ⟨n⟩ =
      (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ n)) ⟶ X) :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The transition map of the hom-tower is precomposition** with the inclusion of the `m`-th
thickening into the `n`-th. Cite this rather than unfolding the composite of functors. -/
theorem homTowerLRS_map_apply {m n : ℕ} (hmn : m ≤ n) (g : (homTowerLRS I X).obj ⟨n⟩) :
    (homTowerLRS I X).map (homOfLE hmn).op g = (thickeningTower I).map (homOfLE hmn) ≫ g :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The transition maps of the tower of thickenings are `Spec` of the quotient factor maps, for an
arbitrary `m ≤ n`. This is `AdicCompletion.quotientTower_map` pushed through `Spec`. -/
theorem thickeningTower_map {m n : ℕ} (hmn : m ≤ n) :
    (thickeningTower I).map (homOfLE hmn) =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.Quotient.factorPow I hmn)) := by
  change Spec.locallyRingedSpaceMap ((AdicCompletion.quotientTower I).map (homOfLE hmn).op) = _
  rw [AdicCompletion.quotientTower_map I hmn]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The consecutive case**, spelled with `stepRingHom` — the map a `ThickeningFamilyLRS`'s
compatibility condition is phrased through, so that the two conditions can be compared directly. -/
@[simp]
theorem thickeningTower_map_succ (n : ℕ) :
    (thickeningTower I).map (homOfLE (Nat.le_succ (n + 1))) =
      Spec.locallyRingedSpaceMap (stepRingHom I n) :=
  thickeningTower_map I (Nat.le_succ (n + 1))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The level-`0` thickening has empty carrier**: `R ⧸ I⁰ = R ⧸ ⊤` is the zero ring
(`subsingleton_quotient_pow_zero`), and the prime spectrum of a subsingleton ring is empty. -/
theorem isEmpty_thickeningTower_zero : IsEmpty ((thickeningTower I).obj 0) := by
  haveI := subsingleton_quotient_pow_zero I
  exact inferInstanceAs (IsEmpty (PrimeSpectrum (R ⧸ I ^ 0)))

/-- **The level-`0` thickening is initial in `LocallyRingedSpace`**, hence `Hom(Spec (R ⧸ I⁰), X)`
is a subsingleton for every `X`. This is the fact that makes the index shift of `homTowerLRS`
harmless, and it is where this file's construction differs from the affine one: there the level-`0`
hom-set is `B →+* R ⧸ I⁰`, a subsingleton for elementary reasons about rings, whereas here the
source is empty and the statement is geometric. -/
def isInitialThickeningTowerZero : IsInitial ((thickeningTower I).obj 0) :=
  haveI := isEmpty_thickeningTower_zero I
  LocallyRingedSpace.isInitialOfIsEmpty

/-- **The legs of the cone attached to a compatible family**: the `(n + 1)`-st leg is the family's
`n`-th member, and the `0`-th is the unique morphism out of the initial object. -/
def thickeningLeg (f : ThickeningFamilyLRS I X) : ∀ n : ℕ, ((thickeningTower I).obj n ⟶ X)
  | 0 => (isInitialThickeningTowerZero I).to X
  | (n + 1) => f.1 n

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The consecutive compatibility of the legs.** Above level `0` this is the family's own
condition, read through `thickeningTower_map_succ`; at level `0` there is nothing to prove, because
the source is initial. -/
theorem thickeningLeg_step (f : ThickeningFamilyLRS I X) (n : ℕ) :
    (thickeningTower I).map (homOfLE (Nat.le_succ n)) ≫ thickeningLeg I X f (n + 1) =
      thickeningLeg I X f n := by
  cases n with
  | zero => exact (isInitialThickeningTowerZero I).hom_ext _ _
  | succ k =>
    change (thickeningTower I).map (homOfLE (Nat.le_succ (k + 1))) ≫ f.1 (k + 1) = f.1 k
    rw [thickeningTower_map_succ]
    exact f.2 k

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Compatibility along every `m ≤ n`**, by `Nat.le_induction` from the consecutive case — the
first of the two things a `ThickeningFamilyLRS` does not already say and a section of the hom-tower
does. Mirrors `AdicCompletion.quotientTower_map`, which is the same induction one level down. -/
theorem thickeningLeg_comp (f : ThickeningFamilyLRS I X) {m n : ℕ} (hmn : m ≤ n) :
    (thickeningTower I).map (homOfLE hmn) ≫ thickeningLeg I X f n = thickeningLeg I X f m := by
  induction n, hmn using Nat.le_induction with
  | base =>
    have h : (thickeningTower I).map (homOfLE (le_refl m)) = 𝟙 _ := by
      rw [Subsingleton.elim (homOfLE (le_refl m)) (𝟙 m), CategoryTheory.Functor.map_id]
    rw [h, Category.id_comp]
  | succ n hmn ih =>
    rw [show homOfLE (hmn.trans (Nat.le_succ n)) = homOfLE hmn ≫ homOfLE (Nat.le_succ n) from
      Subsingleton.elim _ _, Functor.map_comp, Category.assoc, thickeningLeg_step, ih]

/-- **A compatible family is a section of the hom-tower.** Forwards, `thickeningLeg` inserts the
unique level-`0` morphism and `thickeningLeg_comp` upgrades the compatibility; backwards, a section
is read off at the levels `⟨n + 1⟩`. The round trip at level `0` is not `rfl` — it is
`IsInitial.hom_ext`, which is exactly where the initiality of `Spec (R ⧸ I⁰)` is spent. -/
def thickeningFamilySectionsEquivLRS :
    ThickeningFamilyLRS I X ≃ (homTowerLRS I X).sections where
  toFun f := ⟨fun j => thickeningLeg I X f j.unop,
    fun {_ _} φ => thickeningLeg_comp I X f (leOfHom φ.unop)⟩
  invFun u := ⟨fun n => u.1 ⟨n + 1⟩, fun n => by
    rw [← thickeningTower_map_succ I n]
    exact u.2 (homOfLE (Nat.le_succ (n + 1))).op⟩
  left_inv _ := rfl
  right_inv u := Subtype.ext (funext fun j => by
    obtain ⟨n⟩ := j
    cases n with
    | zero => exact (isInitialThickeningTowerZero I).hom_ext _ _
    | succ k => rfl)

/-- **The two presentations agree, for a general target**: a compatible family of morphisms out of
the thickenings is the same datum as a point of `lim_n Hom(Spec (R ⧸ Iⁿ), X)`.

Like its affine analogue `thickeningFamilyLimitEquiv` this is a composite, and like it, it is
pinned down from outside rather than unfolded: `limit_π_thickeningFamilyLimitEquivLRS` computes
every component and `eq_thickeningFamilyLimitEquivLRS` says the components determine the point. -/
def thickeningFamilyLimitEquivLRS :
    ThickeningFamilyLRS I X ≃ (limit (homTowerLRS I X) : Type u) :=
  (thickeningFamilySectionsEquivLRS I X).trans (Types.limitEquivSections (homTowerLRS I X)).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Component rule**, with the index shift: the `(n + 1)`-st leg of the cone attached to `f` is
`f`'s `n`-th member. Unlike the affine `limit_π_thickeningFamilyLimitEquiv` there is no `Spec` to
apply — the legs already are morphisms of locally ringed spaces. -/
theorem limit_π_thickeningFamilyLimitEquivLRS (f : ThickeningFamilyLRS I X) (n : ℕ) :
    limit.π (homTowerLRS I X) ⟨n + 1⟩ (thickeningFamilyLimitEquivLRS I X f) = f.1 n := by
  rw [thickeningFamilyLimitEquivLRS, Equiv.trans_apply, Types.limitEquivSections_symm_apply]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The level-`0` leg of the cone carries no information**: it lands in
`Hom(Spec (R ⧸ I⁰), X)`, and `Spec (R ⧸ I⁰)` is initial. This is why the index shift above loses
nothing. -/
theorem limitLRS_π_zero_eq (u v : (limit (homTowerLRS I X) : Type u)) :
    limit.π (homTowerLRS I X) ⟨0⟩ u = limit.π (homTowerLRS I X) ⟨0⟩ v :=
  (isInitialThickeningTowerZero I).hom_ext _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **An element of `lim_n Hom(Spec (R ⧸ Iⁿ), X)` is determined by its components at `⟨n + 1⟩`.**
The level-`0` obligation of `Types.limit_ext` is discharged by `limitLRS_π_zero_eq`. -/
theorem limitLRS_ext_succ {u v : (limit (homTowerLRS I X) : Type u)}
    (h : ∀ n : ℕ, limit.π (homTowerLRS I X) ⟨n + 1⟩ u =
      limit.π (homTowerLRS I X) ⟨n + 1⟩ v) : u = v := by
  refine Types.limit_ext _ u v fun j => ?_
  induction j using Opposite.rec with
  | op n =>
    cases n with
    | zero => exact limitLRS_π_zero_eq I X u v
    | succ m => exact h m

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The component rule characterises the equivalence**: any point of the limit whose legs at
`⟨n + 1⟩` are the members of `f` *is* the point attached to `f`. Together with
`limit_π_thickeningFamilyLimitEquivLRS` this determines it without unfolding the composite. -/
theorem eq_thickeningFamilyLimitEquivLRS (f : ThickeningFamilyLRS I X)
    (u : (limit (homTowerLRS I X) : Type u))
    (h : ∀ n : ℕ, limit.π (homTowerLRS I X) ⟨n + 1⟩ u = f.1 n) :
    u = thickeningFamilyLimitEquivLRS I X f :=
  limitLRS_ext_succ I X fun n => by rw [h n, limit_π_thickeningFamilyLimitEquivLRS]

section Cover

variable (hI : I.FG) {ι : Type u} (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤)
    (B : ι → Type u) [∀ i, CommRing (B i)]
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i)))

/-- **`Spf R` is the colimit of its infinitesimal thickenings, in `limit` form** (EGA I, 10.6.7),
for a target carrying an affine open cover:

```
(Spf R ⟶ X)  ≃  lim_n Hom(Spec (R ⧸ Iⁿ), X)
```

This is umbrella 97's headline statement in the umbrella's own words. The cover data is needed to
build the inverse and cannot influence it, see `spfHomLimitEquivLRS_eq_of_cover`; the component
rule is `limit_π_spfHomLimitEquivLRS`. -/
def spfHomLimitEquivLRS :
    (locallyRingedSpaceObj I ⟶ X) ≃ (limit (homTowerLRS I X) : Type u) :=
  (thickeningRestrictionEquivLRS I X hI U hU B e).trans (thickeningFamilyLimitEquivLRS I X)

/-- **Computation rule**: the `(n + 1)`-st leg of the cone attached to `g` is the restriction of
`g` to the `n`-th thickening. Cite this rather than unfolding the `Equiv`. -/
theorem limit_π_spfHomLimitEquivLRS (g : locallyRingedSpaceObj I ⟶ X) (n : ℕ) :
    limit.π (homTowerLRS I X) ⟨n + 1⟩ (spfHomLimitEquivLRS I X hI U hU B e g) =
      thickeningMap I n ≫ g := by
  rw [spfHomLimitEquivLRS, Equiv.trans_apply, limit_π_thickeningFamilyLimitEquivLRS,
    thickeningRestrictionEquivLRS_apply]

/-- **The bijection does not depend on the cover**, as an equality of `Equiv`s. Two arbitrary
choices of cover data — different index types, different opens, different affine identifications —
give the same equivalence, because an `Equiv` is determined by its forward map and this one is
`thickeningFamilyLimitEquivLRS ∘ restrictToThickeningsLRS`, in which no cover datum occurs. -/
theorem spfHomLimitEquivLRS_eq_of_cover {ι' : Type u} (U' : ι' → Opens X.toTopCat)
    (hU' : ⨆ i, U' i = ⊤) (B' : ι' → Type u) [∀ i, CommRing (B' i)]
    (e' : ∀ i, X.restrict (U' i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B' i))) :
    spfHomLimitEquivLRS I X hI U hU B e = spfHomLimitEquivLRS I X hI U' hU' B' e' :=
  Equiv.coe_fn_injective rfl

end Cover

section Affine

variable (B : Type u) [CommRing B]

/-- The comparison at level `j`, `Spec` on hom-sets: a ring map `B →+* R ⧸ Iⁿ` is the same datum as
a morphism `Spec (R ⧸ Iⁿ) ⟶ Spec B`, because `Spec.toLocallyRingedSpace` is fully faithful. -/
def homTowerAppLRS (j : ℕᵒᵖ) : (homTower I B).obj j ≃
    (homTowerLRS I (Spec.locallyRingedSpaceObj (CommRingCat.of B))).obj j :=
  (opEquiv (op ((AdicCompletion.quotientTower I).obj j)) (op (CommRingCat.of B))).symm.trans
    Spec.fullyFaithfulToLocallyRingedSpace.homEquiv

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The comparison is `Spec`, and nothing else. -/
theorem homTowerAppLRS_apply (j : ℕᵒᵖ) (g : (homTower I B).obj j) :
    homTowerAppLRS I B j g = Spec.locallyRingedSpaceMap g := rfl

/-- **The affine hom-tower is the general one at `X = Spec B`** — up to a natural isomorphism, not
on the nose: `homTower I B` has ring homomorphisms for objects and `homTowerLRS I (Spec B)` has
morphisms of locally ringed spaces, so unlike `thickeningFamily_eq_thickeningFamilyLRS` this cannot
be an equality. Naturality is contravariance of `Spec`. -/
def homTowerIsoLRS :
    homTower I B ≅ homTowerLRS I (Spec.locallyRingedSpaceObj (CommRingCat.of B)) :=
  NatIso.ofComponents (fun j => Equiv.toIso (homTowerAppLRS I B j)) (fun φ => by
    ext g
    exact Spec.locallyRingedSpaceMap_comp g ((AdicCompletion.quotientTower I).map φ))

/-- The induced identification of the two limits, `lim_n (B →+* R ⧸ Iⁿ) ≅
lim_n Hom(Spec (R ⧸ Iⁿ), Spec B)`. -/
def limitIsoLRS : (limit (homTower I B) : Type u) ≅
    (limit (homTowerLRS I (Spec.locallyRingedSpaceObj (CommRingCat.of B))) : Type u) :=
  HasLimit.isoOfNatIso (homTowerIsoLRS I B)

/-- **The affine and general equivalences agree**, transported along `limitIsoLRS`. Proved from the
two component rules through `eq_thickeningFamilyLimitEquivLRS`, so no `Equiv` is unfolded. Note
`f : ThickeningFamily I B` is accepted as a `ThickeningFamilyLRS I (Spec B)` without transport, by
`thickeningFamily_eq_thickeningFamilyLRS`. -/
theorem limitIsoLRS_hom_thickeningFamilyLimitEquiv (f : ThickeningFamily I B) :
    (limitIsoLRS I B).hom (thickeningFamilyLimitEquiv I B f) =
      thickeningFamilyLimitEquivLRS I (Spec.locallyRingedSpaceObj (CommRingCat.of B)) f :=
  eq_thickeningFamilyLimitEquivLRS I _ f _ fun n => by
    rw [limitIsoLRS, ← types_comp_apply (HasLimit.isoOfNatIso (homTowerIsoLRS I B)).hom
      (limit.π _ ⟨n + 1⟩), HasLimit.isoOfNatIso_hom_π, types_comp_apply]
    exact limit_π_thickeningFamilyLimitEquiv I B f n

/-- **All three presentations agree at an affine target.** For any cover data whatsoever, this
file's equivalence out of `Spf R ⟶ Spec B` is `specHomLimitEquiv` — the ring-side limit form of
`FormalSchemes/IndSchemeLimit.lean` — read through `limitIsoLRS`. -/
theorem spfHomLimitEquivLRS_specHomLimitEquiv (hI : I.FG) {ι : Type u}
    (U : ι → Opens (Spec.locallyRingedSpaceObj (CommRingCat.of B)).toTopCat) (hU : ⨆ i, U i = ⊤)
    (C : ι → Type u) [∀ i, CommRing (C i)]
    (e : ∀ i, (Spec.locallyRingedSpaceObj (CommRingCat.of B)).restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (C i)))
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) :
    spfHomLimitEquivLRS I _ hI U hU C e g = (limitIsoLRS I B).hom (specHomLimitEquiv I B g) := by
  rw [spfHomLimitEquivLRS, Equiv.trans_apply,
    thickeningRestrictionEquivLRS_eq_thickeningRestrictionEquiv,
    ← limitIsoLRS_hom_thickeningFamilyLimitEquiv, thickeningFamilyLimitEquiv, Equiv.trans_apply]
  exact congrArg _ (congrArg _ ((thickeningRestrictionEquiv I B).symm_apply_apply g))

end Affine

/-! ### A concrete witness

`[IsAdicRing I]` does **not** exclude `I = ⊥` — at `⊥` it degenerates to discreteness of `R`
(`is_bot_adic_iff`; see `FormalSchemes/AdicRing.lean`) and every thickening is `Spec R` — and a
cover of `X` by affine opens is satisfied by the one-piece cover of an affine `X`. Neither
degeneracy is present below. The witness is `Spf ℤ⟦X⟧ ⟶ Spec ℤ` with `Spec ℤ` covered by `D(2)`
and `D(3)`, the instantiation `FormalSchemes/SpfHomOfFamily.lean` supplies for the `∃!` form, and
its ideal is nonzero by `FormalSpectrum.formalLineIdeal_ne_bot`. -/

section Nonvacuity

open Polynomial

attribute [local instance] isAdicRing_formalLineIdeal

/-- **The headline equivalence at the formal-line witness**: morphisms `Spf ℤ⟦X⟧ ⟶ Spec ℤ` are
points of `lim_n Hom(Spec (ℤ⟦X⟧ ⧸ (X)ⁿ), Spec ℤ)`, with `Spec ℤ` presented by the two-piece cover
`D(2)`, `D(3)`. -/
def spfHomLimitEquivFormalLine :
    (locallyRingedSpaceObj formalLineIdeal ⟶ witnessTarget) ≃
      (limit (homTowerLRS formalLineIdeal witnessTarget) : Type) :=
  spfHomLimitEquivLRS formalLineIdeal witnessTarget (polyXIdeal_fg.map _) formalLineOpen
    iSup_formalLineOpen formalLineChartRing formalLineChartIso

/-- **Its components are the witness family**: the point of the limit attached to
`spfHomFormalLine` restricts on each thickening to `witnessFamily`. -/
theorem limit_π_spfHomLimitEquivFormalLine (n : ℕ) :
    limit.π (homTowerLRS formalLineIdeal witnessTarget) ⟨n + 1⟩
        (spfHomLimitEquivFormalLine spfHomFormalLine) = witnessFamily.1 n := by
  rw [spfHomLimitEquivFormalLine, limit_π_spfHomLimitEquivLRS, thickeningMap_comp_spfHomFormalLine]

end Nonvacuity

end FormalSpectrum
