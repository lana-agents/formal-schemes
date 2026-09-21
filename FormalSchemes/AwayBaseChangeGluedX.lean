import FormalSchemes.AwayCompletionUniversal
import FormalSchemes.GeneralFibreProductExposeXIdealCongr

set_option linter.style.header false

/-!
# The base change of a charted `X` along a tower, and along `R → R{1/f}`

`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`
(`FormalSchemes.GeneralFibreProductExposeXIdealCongr`) compares two adic bases `(R, I)` and
`(R', I')` acting on one chart family and concludes that the two glued formal schemes are
**equal**. It takes the agreement of the induced ideal families as a hypothesis, in the
function-level spelling

```
(fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i))
```

and `Ideal.map_algebraMap_family_eq_of_tower` (`FormalSchemes.AwayCompletionUniversal`) proves
exactly that statement whenever `I'` is the extension of `I` and the chart algebras carry
`IsScalarTower R R' (A i)`. Neither module imports the other and neither names the other. This
file is the edge between them:

* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_of_tower` is the
  congruence with that hypothesis discharged, at any `R'` over `R` and at `I' = I·R'`;
* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase` is its
  specialisation to `R' = R{1/f}`, where the `R{1/f}`-algebra structure on each chart is the
  universal one, `FormalSpectrum.awayCompletionLift`.

## Why `I' = I·R'` and not an arbitrary `(R', I')`

Because at an arbitrary `(R', I')` the ideal families need not agree, and the statement that they
do is refuted on this tree rather than open: `FormalSchemes.AdicOnSections` records the refutation
of the general adicity statement (issue 460) and
`FormalSpectrum.cofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonIso`) is its witness,
presenting one adic ring at two ideals of definition at once. `Ideal.IsCofinal` is what survives
there, and the transports it would need are not built. Under `I' = I·R'` the agreement is free and
is one application of the tower lemma — which is the whole content of the first result below.

## The shape of the `R{1/f}` case

`FormalSpectrum.awayCompletionLift` produces the ring map `R{1/f} →+* A` for any `R`-algebra `A`
that is `I·A`-adically complete and inverts `f`, and
`FormalSpectrum.isScalarTower_awayCompletionLift` makes `R → R{1/f} → A` a tower for the algebra
structure it defines. That instance is not synthesizable — it depends on the proof that `f` is a
unit — so it cannot be an instance binder in a statement that also mentions the primed transitions,
whose types depend on it. The result below takes the structure as an instance binder and the
identification of its structural map with the lift as an ordinary hypothesis, which keeps every
type in the statement elaborable while pinning the structure to the universal one.
`AlgebraicGeometry.AffineChartedFibreDatumX.isScalarTower_of_algebraMap_eq_awayCompletionLift`
turns that hypothesis into the tower.

## The primed transitions are produced, not assumed

`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase` takes `τ'`,
`σ'`, their three identities and the two `HEq`s as hypotheses. The second half of this file
produces all seven from `τ`, `σ` and the unprimed identities (issue 2038), in two steps that
compose:

* *Enlarging the scalars* from `R` to `R{1/f}` is
  `FormalSpectrum.awayCompletionChartAlgEquivBase` (`FormalSchemes.AwayCompletionUniversal`),
  which leaves the underlying function alone — `FormalSpectrum.awayCompletionAlgEquiv_apply` is
  `rfl`.
* *Moving the carriers* from `I·A_i` to `(I·R{1/f})·A_i` is `FormalSpectrum.awayTransport`, a
  transport along the very equation the tower lemma supplies, written by the same
  `subst`-on-a-variable-ideal idiom as `FormalSpectrum.awayRingEquiv_heq_of_coe_heq`
  (`FormalSchemes.GeneralFibreProductExposeXIdealCongr`); the heterogeneous equation it owes comes
  out by `HEq.rfl`.

**The identity that was expected to be a separate species is not one.**
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseOverlap_transition` compares composites with
`CompletedTensorAwayInterchange.furtherLocFst` and `CompletedTensorAwayInterchange.furtherLocSnd`
**of the primed ideal** — different terms from the ones the unprimed identity names. They are
nevertheless the *same* `AdicCompletion.mapCompletion` at ideals the tower lemma makes equal: the
localization map `IsLocalization.Away.awayToAwayRight` that
`CompletedTensorAwayInterchange.furtherLocFst` completes does not mention the base ring at all, so
the base enters only through the ideal and every other argument is a `Prop`. One `subst` on a
variable ideal closes it, which is `AdicCompletion.mapCompletion_heq` below. No conjugation
transport of the species of `FormalSpectrum.basicOpenChartOverlapIso_conj_heq` is needed.

**The primed `IsAdicRing` witnesses go the same way (issue 2042).** They are the last primed thing
the statement asked a caller for, and they were asked for as an *instance binder* rather than as a
hypothesis, which is why discharging the primed data left them standing. The chart ideal of the
away base is the chart ideal of the base, so the witness transports along that equality by `▸`;
that is `AlgebraicGeometry.AffineChartedFibreDatumX.isAdicRing_awayBaseChartIdeal`, and
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase'` is the congruence
with it applied. A `letI` is admissible there because it stands in the *conclusion*, after every
binder, rather than before the binders whose types depend on it.

## What is not proved here

**No datum is constructed.** `τ`, `σ` and their three identities over `R` are still inputs, and
so is the `R{1/f}`-algebra structure on each chart together with the equation pinning it to
`FormalSpectrum.awayCompletionLift`. What this file removes from a caller's obligations is the
primed half, not the unprimed one.

**No separation statement.** Nothing here mentions
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`, fibre products or diagonals. The conclusion
is an equality of glued objects and stops there.

## Placement

Over `FormalSchemes.AwayCompletionUniversal` and
`FormalSchemes.GeneralFibreProductExposeXIdealCongr`: forward closure **93**, reverse closure
**3**, whose three members are `FormalSchemes.AwayBaseChangeChartTransition` (issue 2070),
`FormalSchemes.AwayBaseChangeSeparated` (issue 1998) and
`FormalSchemes.AwayBaseFactorisationRange` (issue 2139), all of which arrived later. The two
parents are import-incomparable, so the statement costs either an import edge or a module of its
own, and the edge was rejected in both directions: each parent was itself a leaf, so an edge either
way puts one of them inside the other's subtree and makes every later consumer of that parent pay
for the other. A module of its own keeps both parents at the cost they were landed at, and
`FormalSchemes.AwayBaseChangeGluedX`'s own reverse closure is **3**, so three modules pay for it.

`FormalSchemes.AwayCompletionUniversal`'s reverse closure is **4**, and
`FormalSchemes.GeneralFibreProductExposeXIdealCongr`'s reverse closure is **5**; the figures
recorded in the modules this one reaches moved by one each when it landed, and every delta is
measured in the pull request that added this module (issue 2028).

The construction of the primed data (issue 2038) is added **in place** rather than in a module of
its own: `FormalSchemes.AwayBaseChangeGluedX`'s reverse closure is **3**, so extending this file
re-elaborates this file, its three consumers and the root module list and nothing else, and moves
no stated figure anywhere on the tree. The general transports the construction introduces —
`FormalSpectrum.awayTransport`, `FormalSpectrum.awayTransportRingHom` and
`AdicCompletion.mapCompletion_heq` — are each consumed by exactly one module, this one, and each
has a natural home earlier in the tree. Both sides of that ratio, since a ratio with one side is
not a measurement: `FormalSchemes.Completion`, where `AdicCompletion.mapCompletion` is defined,
has reverse closure **469**; `FormalSchemes.AdicCompletionCongrIdealAlg`, the alternative home for
the `AdicCompletion`-level transport, has reverse closure **195**; and
`FormalSchemes.AwayCompletionUniversal`, where the two `awayTransport` statements would go, has
reverse closure **4**. `FormalSchemes.AwayBaseChangeGluedX`'s own reverse closure is **3**, and
every one of the three homes above carries a larger one, so moving a transport would put a
statement this file alone reads into the environment of modules that do not read it. They are
kept here on that ratio, which is the disposition
`FormalSchemes.GeneralFibreProductExposeXIdealCongr` took for its own three transports — and the
count there is of consuming modules too: two of its three transports are read by two declarations
in that file, the third by one, and none of the three is read outside it.

## Main results

* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_of_tower`: the glued `X`
  of a smart-constructor datum is unchanged by a change of base along `R → R'` carrying `I` to
  `I·R'`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.isScalarTower_of_algebraMap_eq_awayCompletionLift`:
  an `R{1/f}`-algebra structure on a chart whose structural map is the universal lift is a tower
  over `R`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase`: the same
  congruence at `R' = R{1/f}`, `I' = I·R{1/f}`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition` and
  `AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseOverlap`: the primed transition data,
  constructed from the unprimed data, with their three identities and their two `HEq`s.
* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase`: the congruence at
  `R' = R{1/f}` with the primed data discharged.
* `AlgebraicGeometry.AffineChartedFibreDatumX.isAdicRing_awayBaseChartIdeal` and
  `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase'`: the same
  congruence with the primed *adicity* discharged as well, which is the form a caller holding only
  an `(R, I)`-presentation can apply.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.12.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AdicCompletion

/-- **Two completions of one ring map at equal ideals are heterogeneously equal.** The ideals are
*variables* here and the caller instantiates them at the two families being compared; that is the
whole reason this lemma exists, since `Ideal.map` of an `algebraMap` is an application and `subst`
cannot reach it. The two remaining arguments of `AdicCompletion.mapCompletion` are `Prop`s, so
nothing else can differ. -/
theorem mapCompletion_heq {P Q : Type u} [CommRing P] [CommRing Q] {K K' : Ideal P}
    {L L' : Ideal Q} (hK : K = K') (hL : L = L') (ρ : P →+* Q) (h : K.map ρ ≤ L)
    (h' : K'.map ρ ≤ L') (fgL : L.FG) (fgL' : L'.FG) :
    HEq (AdicCompletion.mapCompletion ρ h fgL) (AdicCompletion.mapCompletion ρ h' fgL') := by
  subst hK
  subst hL
  rfl

end AdicCompletion

namespace FormalSpectrum

/-! ### Transporting away completions along an equality of ideals -/

section Transport

variable {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]

/-- **Transport a ring homomorphism of away completions along equalities of the two ideals.**
Both ideals are variables, so `subst` moves them; that is the only reason this is a definition
rather than a `rw`. -/
def awayTransportRingHom {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} (h₁ : K₁ = L₁) (h₂ : K₂ = L₂)
    {s₁ : A₁} {s₂ : A₂} (φ : awayCompletion L₁ s₁ →+* awayCompletion L₂ s₂) :
    awayCompletion K₁ s₁ →+* awayCompletion K₂ s₂ := by
  subst h₁
  subst h₂
  exact φ

/-- The transport is functorial in the obvious sense. -/
theorem awayTransportRingHom_comp {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} {K₃ L₃ : Ideal A₃}
    (h₁ : K₁ = L₁) (h₂ : K₂ = L₂) (h₃ : K₃ = L₃) {s₁ : A₁} {s₂ : A₂} {s₃ : A₃}
    (φ : awayCompletion L₁ s₁ →+* awayCompletion L₂ s₂)
    (ψ : awayCompletion L₂ s₂ →+* awayCompletion L₃ s₃) :
    (awayTransportRingHom h₂ h₃ ψ).comp (awayTransportRingHom h₁ h₂ φ) =
      awayTransportRingHom h₁ h₃ (ψ.comp φ) := by
  subst h₁
  subst h₂
  subst h₃
  rfl

/-- **A heterogeneous equality of ring homomorphisms of away completions is an equality with the
transport.** This is the step that turns `AdicCompletion.mapCompletion_heq` into something a
`rw` can use. -/
theorem eq_awayTransportRingHom_of_heq {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} (h₁ : K₁ = L₁)
    (h₂ : K₂ = L₂) {s₁ : A₁} {s₂ : A₂} {φ : awayCompletion K₁ s₁ →+* awayCompletion K₂ s₂}
    {ψ : awayCompletion L₁ s₁ →+* awayCompletion L₂ s₂} (h : HEq φ ψ) :
    φ = awayTransportRingHom h₁ h₂ ψ := by
  subst h₁
  subst h₂
  exact eq_of_heq h

end Transport

section TransportEquiv

variable {S : Type u} [CommRing S]
variable {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
variable [Algebra S A₁] [Algebra S A₂] [Algebra S A₃]

/-- **Transport an algebra equivalence of away completions along equalities of the two ideals.**
This is the carrier half of the base change of a chart transition: the scalars are enlarged by
`FormalSpectrum.awayCompletionChartAlgEquivBase` and the ideals are moved here. -/
def awayTransport {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} (h₁ : K₁ = L₁) (h₂ : K₂ = L₂) {s₁ : A₁}
    {s₂ : A₂} (e : awayCompletion L₁ s₁ ≃ₐ[S] awayCompletion L₂ s₂) :
    awayCompletion K₁ s₁ ≃ₐ[S] awayCompletion K₂ s₂ := by
  subst h₁
  subst h₂
  exact e

/-- **The transport does not move the underlying function**, which is what the `HEq` hypotheses of
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr` ask for. -/
theorem awayTransport_coe_heq {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} (h₁ : K₁ = L₁) (h₂ : K₂ = L₂)
    {s₁ : A₁} {s₂ : A₂} (e : awayCompletion L₁ s₁ ≃ₐ[S] awayCompletion L₂ s₂) :
    HEq (⇑(awayTransport (S := S) h₁ h₂ e)) (⇑e) := by
  subst h₁
  subst h₂
  exact HEq.rfl

/-- The transport commutes with `AlgEquiv.symm`, with the two ideal equalities exchanged. -/
theorem awayTransport_symm {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} (h₁ : K₁ = L₁) (h₂ : K₂ = L₂)
    {s₁ : A₁} {s₂ : A₂} (e : awayCompletion L₁ s₁ ≃ₐ[S] awayCompletion L₂ s₂) :
    (awayTransport (S := S) h₁ h₂ e).symm = awayTransport h₂ h₁ e.symm := by
  subst h₁
  subst h₂
  rfl

/-- The transport commutes with `AlgEquiv.trans`. -/
theorem awayTransport_trans {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} {K₃ L₃ : Ideal A₃}
    (h₁ : K₁ = L₁) (h₂ : K₂ = L₂) (h₃ : K₃ = L₃) {s₁ : A₁} {s₂ : A₂} {s₃ : A₃}
    (e : awayCompletion L₁ s₁ ≃ₐ[S] awayCompletion L₂ s₂)
    (e' : awayCompletion L₂ s₂ ≃ₐ[S] awayCompletion L₃ s₃) :
    (awayTransport (S := S) h₁ h₂ e).trans (awayTransport h₂ h₃ e') =
      awayTransport h₁ h₃ (e.trans e') := by
  subst h₁
  subst h₂
  subst h₃
  rfl

/-- The transport of the identity is the identity. -/
theorem awayTransport_refl {K L : Ideal A₁} (h : K = L) {s : A₁} :
    awayTransport (S := S) h h (AlgEquiv.refl (A₁ := awayCompletion L s)) = AlgEquiv.refl := by
  subst h
  rfl

/-- The transport read as a ring homomorphism, in the form the composite identities need. -/
theorem awayTransport_symm_toRingHom {K₁ L₁ : Ideal A₁} {K₂ L₂ : Ideal A₂} (h₁ : K₁ = L₁)
    (h₂ : K₂ = L₂) {s₁ : A₁} {s₂ : A₂} (e : awayCompletion L₁ s₁ ≃ₐ[S] awayCompletion L₂ s₂) :
    (awayTransport (S := S) h₁ h₂ e).symm.toAlgHom.toRingHom =
      awayTransportRingHom h₂ h₁ e.symm.toAlgHom.toRingHom := by
  subst h₁
  subst h₂
  rfl

end TransportEquiv

/-! ### The base re-reading is compatible with the groupoid structure -/

section ChartBase

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R) (hI : I.FG)
variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
variable [Algebra R A] [Algebra R A'] [Algebra R A'']
variable [Algebra (awayCompletion I f) A] [Algebra (awayCompletion I f) A']
  [Algebra (awayCompletion I f) A'']
variable [IsScalarTower R (awayCompletion I f) A] [IsScalarTower R (awayCompletion I f) A']
  [IsScalarTower R (awayCompletion I f) A'']

/-- Reading a chart transition over `R{1/f}` commutes with `AlgEquiv.symm`. -/
theorem awayCompletionChartAlgEquivBase_symm {s : A} {s' : A'}
    (e : awayCompletion (I.map (algebraMap R A)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A')) s') :
    (awayCompletionChartAlgEquivBase I f hI e).symm =
      awayCompletionChartAlgEquivBase I f hI e.symm :=
  AlgEquiv.ext fun _ => rfl

/-- Reading a chart transition over `R{1/f}` commutes with `AlgEquiv.trans`. -/
theorem awayCompletionChartAlgEquivBase_trans {s : A} {s' : A'} {s'' : A''}
    (e : awayCompletion (I.map (algebraMap R A)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A')) s')
    (e' : awayCompletion (I.map (algebraMap R A')) s' ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A'')) s'') :
    (awayCompletionChartAlgEquivBase I f hI e).trans
        (awayCompletionChartAlgEquivBase I f hI e') =
      awayCompletionChartAlgEquivBase I f hI (e.trans e') :=
  AlgEquiv.ext fun _ => rfl

/-- Reading the identity over `R{1/f}` gives the identity. -/
theorem awayCompletionChartAlgEquivBase_refl {s : A} :
    awayCompletionChartAlgEquivBase I f hI
        (AlgEquiv.refl (R := R) (A₁ := awayCompletion (I.map (algebraMap R A)) s)) =
      AlgEquiv.refl :=
  AlgEquiv.ext fun _ => rfl

/-- The base re-reading does not move the underlying ring homomorphism. -/
theorem awayCompletionChartAlgEquivBase_symm_toRingHom {s : A} {s' : A'}
    (e : awayCompletion (I.map (algebraMap R A)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A')) s') :
    (awayCompletionChartAlgEquivBase I f hI e).symm.toAlgHom.toRingHom =
      e.symm.toAlgHom.toRingHom := rfl

end ChartBase

end FormalSpectrum

namespace CompletedTensorAwayInterchange

/-! ### The further localizations of two bases at one chart -/

section TwoBases

variable {R R' : Type u} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
variable {A : Type u} [CommRing A] [Algebra R A] [Algebra R' A]

/-- **The first further localization does not depend on the base ring beyond its induced ideal.**
`CompletedTensorAwayInterchange.furtherLocFst` completes `IsLocalization.Away.awayToAwayRight`,
which does not mention the base ring; everything else it is given is a `Prop`. So the two legs
differ in an ideal and in nothing else, and `AdicCompletion.mapCompletion_heq` closes it. -/
theorem furtherLocFst_toRingHom_heq (hI : I.FG) (hI' : I'.FG) (g₁ g₂ : A)
    (hK : I'.map (algebraMap R' A) = I.map (algebraMap R A)) :
    HEq (furtherLocFst I' g₁ g₂ hI').toRingHom (furtherLocFst I g₁ g₂ hI).toRingHom := by
  refine AdicCompletion.mapCompletion_heq (by rw [hK]) (by rw [hK]) _ ?_ ?_
    ((hI'.map (algebraMap R' A)).map _) ((hI.map (algebraMap R A)).map _) <;>
    exact le_of_eq (by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => IsLocalization.Away.awayToAwayRight_eq g₁ g₂ a)

/-- **The second further localization does not depend on the base ring beyond its induced ideal**,
for the same reason as `CompletedTensorAwayInterchange.furtherLocFst_toRingHom_heq`. -/
theorem furtherLocSnd_toRingHom_heq (hI : I.FG) (hI' : I'.FG) (g₁ g₂ : A)
    (hK : I'.map (algebraMap R' A) = I.map (algebraMap R A)) :
    HEq (furtherLocSnd I' g₁ g₂ hI').toRingHom (furtherLocSnd I g₁ g₂ hI).toRingHom := by
  refine AdicCompletion.mapCompletion_heq (by rw [hK]) (by rw [hK]) _ ?_ ?_
    ((hI'.map (algebraMap R' A)).map _) ((hI.map (algebraMap R A)).map _) <;>
    exact le_of_eq (by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => IsLocalization.Away.awayToAwayLeft_eq g₂ g₁ a)

end TwoBases

end CompletedTensorAwayInterchange

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

section Tower

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} (hI : I.FG)
variable {B : Type u} [CommRing B] [Algebra R B]
variable {B' : Type u} [CommRing B'] [Algebra R' B']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable (g : ∀ (i : J), J → A i)
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable [isAdicA : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable [isAdicA' : ∀ i : J,
  IsAdicRing ((I.map (algebraMap R R')).map (algebraMap R' (A i)))]

/-- **The glued `X` of a smart-constructor datum does not move along a tower.** For `R'` an
`R`-algebra, `I'` the extension `I·R'`, and a chart family that is an algebra over both compatibly,
the two glued formal schemes built by
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` are **equal**.

This is `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr` with its
ideal-family hypothesis discharged by `Ideal.map_algebraMap_family_eq_of_tower`, whose conclusion
is that hypothesis verbatim. The transitions are still inputs on both sides: only the agreement of
the *ideals* is free under a tower, and the agreement of the *transitions* is not. -/
theorem ofAlgebraData_xGlued_congr_of_tower
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (τ' : ∀ (i j : J), i ≠ j →
      (awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A i))) (g i j) ≃ₐ[R']
        awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A j))) (g j i)))
    (τ'_symm : ∀ (i j : J) (h : i ≠ j), τ' j i h.symm = (τ' i j h).symm)
    (σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A i))) (g i j * g i k) ≃ₐ[R']
        awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A j))) (g j k * g j i)))
    (hστ' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd (I.map (algebraMap R R'))
            (g j k) (g j i) (hI.map _)) =
        (CompletedTensorAwayInterchange.furtherLocFst (I.map (algebraMap R R'))
            (g i j) (g i k) (hI.map _)).comp (τ' i j hij).symm.toAlgHom)
    (hσc' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).trans ((σ' j k i hjk hij.symm hik.symm).trans
        (σ' k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R')
          (A₁ := awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A i)))
            (g i j * g i k)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk))) :
    (AffineChartedFibreDatumX.ofAlgebraData (B := B') (hI.map (algebraMap R R'))
        A g τ' τ'_symm σ' hστ' hσc').xGlued =
      (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued :=
  ofAlgebraData_xGlued_congr hI (hI.map (algebraMap R R')) A g τ τ_symm σ hστ hσc
    τ' τ'_symm σ' hστ' hσc' (Ideal.map_algebraMap_family_eq_of_tower A I) hτ hσ

end Tower


section AwayBase

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable {B : Type u} [CommRing B] [Algebra R B]
variable {B' : Type u} [CommRing B'] [Algebra (awayCompletion I f) B']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable [isAdicA : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable (hf : ∀ i, IsUnit (algebraMap R (A i) f))
variable [∀ i, Algebra (awayCompletion I f) (A i)]
variable (g : ∀ (i : J), J → A i)
variable [isAdicA' : ∀ i : J,
  IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
    (algebraMap (awayCompletion I f) (A i)))]

omit isAdicA' in
/-- **A chart whose `R{1/f}`-structure is the universal lift is a tower over `R`.** The algebra
structure is an instance binder rather than `RingHom.toAlgebra` of
`FormalSpectrum.awayCompletionLift`, because the types of the primed transitions in
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase` depend on it and a
`letI` in the statement would put them out of reach of instance synthesis. The hypothesis
identifying the structural map with the lift is what ties it back to the universal one, and it is
all `FormalSpectrum.isScalarTower_awayCompletionLift` needs. -/
theorem isScalarTower_of_algebraMap_eq_awayCompletionLift
    (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i)) (i : J) :
    IsScalarTower R (awayCompletion I f) (A i) :=
  letI := (isAdicA i).toIsAdicComplete
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg i, ← awayCompletionHom_eq_algebraMap]
    exact (awayCompletionLift_awayCompletionHom I f (hf i) r).symm

/-- **The glued `X` of a smart-constructor datum does not move to a basic open of its base.** At
`R' = R{1/f}` and `I' = I·R{1/f}` — the case issue 2007 built every input for, and the only case in
which the ideal-family agreement is free rather than refuted — the two glued formal schemes are
**equal**.

Each chart carries the `R{1/f}`-algebra structure whose structural map is
`FormalSpectrum.awayCompletionLift`, which exists because the chart inverts `f` and is
`I·A_i`-adically complete; the completeness is read off the datum's own adicity witness and is not
a separate hypothesis. -/
theorem ofAlgebraData_xGlued_congr_awayBase
    (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i))
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (τ' : ∀ (i j : J), i ≠ j →
      (awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A i))) (g i j) ≃ₐ[awayCompletion I f]
        awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A j))) (g j i)))
    (τ'_symm : ∀ (i j : J) (h : i ≠ j), τ' j i h.symm = (τ' i j h).symm)
    (σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A i))) (g i j * g i k) ≃ₐ[awayCompletion I f]
        awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A j))) (g j k * g j i)))
    (hστ' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd (I.map (algebraMap R (awayCompletion I f)))
            (g j k) (g j i) (hI.map _)) =
        (CompletedTensorAwayInterchange.furtherLocFst (I.map (algebraMap R (awayCompletion I f)))
            (g i j) (g i k) (hI.map _)).comp (τ' i j hij).symm.toAlgHom)
    (hσc' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).trans ((σ' j k i hjk hij.symm hik.symm).trans
        (σ' k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := awayCompletion I f)
          (A₁ := awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
            (algebraMap (awayCompletion I f) (A i))) (g i j * g i k)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk))) :
    (AffineChartedFibreDatumX.ofAlgebraData (B := B')
        (hI.map (algebraMap R (awayCompletion I f))) A g τ' τ'_symm σ' hστ' hσc').xGlued =
      (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued :=
  haveI : ∀ i, IsScalarTower R (awayCompletion I f) (A i) :=
    isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
  ofAlgebraData_xGlued_congr_of_tower hI A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ' hσc' hτ hσ

end AwayBase


/-!
### The primed transitions, constructed
-/

section AwayBaseData

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, Algebra (awayCompletion I f) (A i)]
variable (tower : ∀ i, IsScalarTower R (awayCompletion I f) (A i))
variable (g : ∀ (i : J), J → A i)

include tower in
/-- **The chart ideal of the away base is the chart ideal of the base**, at one chart. This is
`Ideal.map_algebraMap_family_eq_of_tower` read at a single index, and it is the equality every
transport below runs along. -/
theorem awayBaseChartIdeal (i : J) :
    (I.map (algebraMap R (awayCompletion I f))).map (algebraMap (awayCompletion I f) (A i)) =
      I.map (algebraMap R (A i)) :=
  congrFun (Ideal.map_algebraMap_family_eq_of_tower A I) i

/-- **The transition of a charted presentation, read over `R{1/f}`.** The scalars are enlarged by
`FormalSpectrum.awayCompletionChartAlgEquivBase` and the carriers are moved by
`FormalSpectrum.awayTransport` along
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseChartIdeal`. -/
def awayBaseTransition
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (i j : J) (h : i ≠ j) :
    awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A i))) (g i j) ≃ₐ[awayCompletion I f]
      awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A j))) (g j i) :=
  awayTransport (awayBaseChartIdeal f A tower i) (awayBaseChartIdeal f A tower j)
    (awayCompletionChartAlgEquivBase I f hI (τ i j h))

/-- **The double-overlap datum of a charted presentation, read over `R{1/f}`**, by the same two
steps as `AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition`. -/
def awayBaseOverlap
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A i))) (g i j * g i k) ≃ₐ[awayCompletion I f]
      awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A j))) (g j k * g j i) :=
  awayTransport (awayBaseChartIdeal f A tower i) (awayBaseChartIdeal f A tower j)
    (awayCompletionChartAlgEquivBase I f hI (σ i j k hij hik hjk))

/-- The primed transition has the same underlying function as the unprimed one, which is the `hτ`
hypothesis of `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase`. -/
theorem awayBaseTransition_coe_heq
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (i j : J) (h : i ≠ j) :
    HEq (⇑(awayBaseTransition hI f A tower g τ i j h)) (⇑(τ i j h)) :=
  awayTransport_coe_heq _ _ _

/-- The primed double overlap has the same underlying function as the unprimed one, which is the
`hσ` hypothesis of
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase`. -/
theorem awayBaseOverlap_coe_heq
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    HEq (⇑(awayBaseOverlap hI f A tower g σ i j k hij hik hjk)) (⇑(σ i j k hij hik hjk)) :=
  awayTransport_coe_heq _ _ _

/-- **The primed transitions are symmetric**, because the transport and the base re-reading each
commute with `AlgEquiv.symm`. -/
theorem awayBaseTransition_symm
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (i j : J) (h : i ≠ j) :
    awayBaseTransition hI f A tower g τ j i h.symm =
      (awayBaseTransition hI f A tower g τ i j h).symm := by
  simp only [awayBaseTransition, awayTransport_symm, τ_symm i j h,
    awayCompletionChartAlgEquivBase_symm]

/-- **The primed double overlap satisfies the cocycle identity**, because the transport and the
base re-reading each commute with `AlgEquiv.trans` and each send the identity to the identity. -/
theorem awayBaseOverlap_cocycle
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (awayBaseOverlap hI f A tower g σ i j k hij hik hjk).trans
        ((awayBaseOverlap hI f A tower g σ j k i hjk hij.symm hik.symm).trans
          (awayBaseOverlap hI f A tower g σ k i j hik.symm hjk.symm hij)) =
      AlgEquiv.refl := by
  simp only [awayBaseOverlap, awayTransport_trans, awayCompletionChartAlgEquivBase_trans,
    hσc i j k hij hik hjk, awayCompletionChartAlgEquivBase_refl, awayTransport_refl]

/-- **The primed double overlap is compatible with the primed transition**, which is the identity
the module docstring calls the one expected to be hard.

Both composites are transports of the unprimed composites: the two further localizations of the
primed ideal are the unprimed ones transported
(`CompletedTensorAwayInterchange.furtherLocFst_toRingHom_heq` and its companion), and the
transport is functorial, so the identity follows from the unprimed one by cancelling a
transport. -/
theorem awayBaseOverlap_transition
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (awayBaseOverlap hI f A tower g σ i j k hij hik hjk).symm.toAlgHom.comp
        (CompletedTensorAwayInterchange.furtherLocSnd (I.map (algebraMap R (awayCompletion I f)))
          (g j k) (g j i) (hI.map _)) =
      (CompletedTensorAwayInterchange.furtherLocFst (I.map (algebraMap R (awayCompletion I f)))
          (g i j) (g i k) (hI.map _)).comp
        (awayBaseTransition hI f A tower g τ i j hij).symm.toAlgHom := by
  refine AlgHom.coe_ringHom_injective ?_
  have hi := awayBaseChartIdeal f A tower i
  have hj := awayBaseChartIdeal f A tower j
  have hsnd : (CompletedTensorAwayInterchange.furtherLocSnd
        (I.map (algebraMap R (awayCompletion I f))) (g j k) (g j i) (hI.map _)).toRingHom =
      awayTransportRingHom hj hj
        (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI).toRingHom :=
    eq_awayTransportRingHom_of_heq hj hj
      (CompletedTensorAwayInterchange.furtherLocSnd_toRingHom_heq hI (hI.map _) (g j k) (g j i) hj)
  have hfst : (CompletedTensorAwayInterchange.furtherLocFst
        (I.map (algebraMap R (awayCompletion I f))) (g i j) (g i k) (hI.map _)).toRingHom =
      awayTransportRingHom hi hi
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).toRingHom :=
    eq_awayTransportRingHom_of_heq hi hi
      (CompletedTensorAwayInterchange.furtherLocFst_toRingHom_heq hI (hI.map _) (g i j) (g i k) hi)
  have hσ' : (awayBaseOverlap hI f A tower g σ i j k hij hik hjk).symm.toAlgHom.toRingHom =
      awayTransportRingHom hj hi (σ i j k hij hik hjk).symm.toAlgHom.toRingHom := by
    rw [awayBaseOverlap, awayTransport_symm_toRingHom,
      awayCompletionChartAlgEquivBase_symm_toRingHom]
  have hτ' : (awayBaseTransition hI f A tower g τ i j hij).symm.toAlgHom.toRingHom =
      awayTransportRingHom hj hi (τ i j hij).symm.toAlgHom.toRingHom := by
    rw [awayBaseTransition, awayTransport_symm_toRingHom,
      awayCompletionChartAlgEquivBase_symm_toRingHom]
  simp only [AlgHom.comp_toRingHom]
  simp only [← AlgHom.toRingHom_eq_coe]
  rw [hσ', hsnd, hτ', hfst, awayTransportRingHom_comp, awayTransportRingHom_comp]
  congr 1
  exact congrArg AlgHom.toRingHom (hστ i j k hij hik hjk)

end AwayBaseData

/-!
### The congruence with the primed data discharged
-/

section AwayBaseCorollary

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable {B : Type u} [CommRing B] [Algebra R B]
variable {B' : Type u} [CommRing B'] [Algebra (awayCompletion I f) B']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable [isAdicA : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable (hf : ∀ i, IsUnit (algebraMap R (A i) f))
variable [∀ i, Algebra (awayCompletion I f) (A i)]
variable (g : ∀ (i : J), J → A i)
variable [isAdicA' : ∀ i : J,
  IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
    (algebraMap (awayCompletion I f) (A i)))]

/-- **The glued `X` of a smart-constructor datum does not move to a basic open of its base, with
nothing primed supplied by the caller.** This is
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase` at the primed data
built above: the caller gives the presentation over `(R, I)`, the `R{1/f}`-algebra structure on
each chart, and the equation identifying that structure with
`FormalSpectrum.awayCompletionLift`. -/
theorem ofAlgebraData_xGlued_eq_awayBase
    (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i))
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k))) :
    (AffineChartedFibreDatumX.ofAlgebraData (B := B')
        (hI.map (algebraMap R (awayCompletion I f))) A g
        (awayBaseTransition hI f A
          (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ)
        (awayBaseTransition_symm hI f A
          (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ τ_symm)
        (awayBaseOverlap hI f A
          (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g σ)
        (awayBaseOverlap_transition hI f A
          (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ σ hστ)
        (awayBaseOverlap_cocycle hI f A
          (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g σ hσc)).xGlued =
      (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued :=
  ofAlgebraData_xGlued_congr_awayBase hI f A hf g halg τ τ_symm σ hστ hσc _ _ _ _ _
    (awayBaseTransition_coe_heq hI f A
      (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ)
    (awayBaseOverlap_coe_heq hI f A
      (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g σ)

omit isAdicA' in
/-- **The primed adicity is not a hypothesis, it is a transport.** The chart ideal of the away base
*is* the chart ideal of the base — that is
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseChartIdeal` — and `IsAdicRing` is a `Prop`
class over a fixed topology on the chart, so the witness moves along that equality with nothing but
`▸`. This is the whole content of the primed `IsAdicRing` instance binder the section above
carries, and it is what lets the corollary below drop it. -/
theorem isAdicRing_awayBaseChartIdeal
    (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i)) (i : J) :
    IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
      (algebraMap (awayCompletion I f) (A i))) :=
  awayBaseChartIdeal f A (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) i ▸
    isAdicA i

omit isAdicA' in
/-- **The congruence at `R' = R{1/f}` with nothing primed in the context either.** This is
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase` with its last primed
obligation removed: that theorem discharges the primed transition *data* but still reads the primed
adicity off an instance binder, which a caller holding only a presentation over `(R, I)` has to
manufacture. Here it is produced by
`AlgebraicGeometry.AffineChartedFibreDatumX.isAdicRing_awayBaseChartIdeal` instead.

**Reach for this one.** The two statements have the same conclusion and the same hypotheses; the
only difference is where the primed `IsAdicRing` witnesses come from, and this one asks the caller
for nothing that the unprimed presentation does not already give. The instance-bearing form stays
because this proof consumes it, and because a caller who already holds the primed witnesses — for
instance one that built them some other way — can still use it directly.

The two `letI`s are in the *conclusion*, after every binder, which is why they do not run into the
difficulty the `## The shape of the `R{1/f}` case` section above describes: that one is about a
`letI` standing *before* the binders whose types depend on it. -/
theorem ofAlgebraData_xGlued_eq_awayBase'
    (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i))
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k))) :
    letI tower := isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
    letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A i))) :=
      isAdicRing_awayBaseChartIdeal f A hf halg
    (AffineChartedFibreDatumX.ofAlgebraData (B := B')
        (hI.map (algebraMap R (awayCompletion I f))) A g
        (awayBaseTransition hI f A tower g τ)
        (awayBaseTransition_symm hI f A tower g τ τ_symm)
        (awayBaseOverlap hI f A tower g σ)
        (awayBaseOverlap_transition hI f A tower g τ σ hστ)
        (awayBaseOverlap_cocycle hI f A tower g σ hσc)).xGlued =
      (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued := by
  letI tower := isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
  letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
      (algebraMap (awayCompletion I f) (A i))) :=
    isAdicRing_awayBaseChartIdeal f A hf halg
  exact ofAlgebraData_xGlued_eq_awayBase hI f A hf g halg τ τ_symm σ hστ hσc

end AwayBaseCorollary

end AffineChartedFibreDatumX

end AlgebraicGeometry
