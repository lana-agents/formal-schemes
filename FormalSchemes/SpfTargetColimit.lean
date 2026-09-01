import FormalSchemes.IndSchemeColimitEquivLRS
import FormalSchemes.SpfFullyFaithful
import FormalSchemes.ThickeningHomExt
import FormalSchemes.TwoAdicWitness

set_option linter.style.header false

/-!
# The colimit property of `Spf R` at a **formal-affine** target: what is free and what is not

`FormalSchemes/IndSchemeColimitEquivLRS.lean` proves EGA I 10.6.10 as a bijection

```
(Spf R ⟶ X)  ≃  ThickeningFamilyLRS I X
```

for `X : LocallyRingedSpace` **equipped with a cover by opens `U i` and isomorphisms
`X|_{U i} ≅ Spec (B i)`**. The affineness datum on the target is `Spec`-shaped. Issue 62m asks for
the `Spf`-shaped analogue: the same theorem with `X|_{U i} ≅ Spf (J i)`. The smallest instance of
that question — and the one the general proof would have to run on each chart — is the target
`X = Spf L` itself.

This file settles the half of that instance which is free, records the other half as a single
`Function.Surjective` statement, and states the reason the obvious route to it does not close.

## The split: injective is free, surjective is the whole content

`FormalSpectrum.restrictToThickeningsLRS I X` is defined for **every** locally ringed space `X`,
with no hypothesis; only the inverse of `thickeningRestrictionEquivLRS` needs the cover. And
`FormalSpectrum.hom_ext_thickeningMap_lrs` (`FormalSchemes/ThickeningHomExt.lean`) has **no**
hypothesis on `X` either. So:

* `FormalSpectrum.injective_restrictToThickeningsLRS` — restriction to the thickenings is injective
  for an arbitrary target, unconditionally.
* `FormalSpectrum.existsUnique_hom_thickeningMap_of_exists` — for an arbitrary target the `∃!` of
  EGA I 10.6.10 follows from the bare `∃`. A successor proving existence at a formal-affine target
  does not have to prove uniqueness as well, and does not even need the compatibility hypothesis to
  get it.
* `FormalSpectrum.thickeningRestrictionEquivSpf` — the bijection at the formal-affine target
  `Spf L`, **given** surjectivity. So the entire remaining content of the `Spf`-target colimit
  property, at an affine target, is
  ```lean
  Function.Surjective (restrictToThickeningsLRS I (locallyRingedSpaceObj L))
  ```
  and nothing else in EGA I 10.6.7's affine step is missing. **That statement is now proved**, for
  `L` finitely generated, as `FormalSpectrum.surjective_restrictToThickeningsLRS_spf`
  (`FormalSchemes/SpfTargetSurjective.lean`); the unconditional bijection and `∃!` are
  `FormalSpectrum.thickeningRestrictionEquivSpfOfFG` and
  `FormalSpectrum.existsUnique_hom_thickeningMap_spf` in the same file.
* `FormalSpectrum.surjective_restrictToThickeningsLRS` — the same `Function.Surjective` statement is
  what the landed `Spec`-cover theorem supplies, so the split above is a factorisation of
  `thickeningRestrictionEquivLRS` and not a re-phrasing: injectivity plus that surjectivity rebuild
  it through `Equiv.ofBijective`.

## The crux: `AdicRingCat.spfHomEquiv` does **not** substitute for `FormalSpectrum.specHomEquiv`

Issue 62m's step 3 is `FormalSpectrum.chartSpfHom` (`FormalSchemes/ThickeningChartSpfHom.lean`),
which is `(thickeningRestrictionEquiv (awayCompletionIdeal I r) B).symm` applied to the chart's
family. Unwinding one level further than the row did: that `Equiv`'s inverse is
`FormalSpectrum.existsUnique_thickeningMap_comp_of_specHom`
(`FormalSchemes/IndSchemeExistenceGeometric.lean`), whose inverse is
`FormalSpectrum.existsUnique_thickeningMap_comp` (`FormalSchemes/IndSchemeExistence.lean`), and it
is *there* that `specHomEquiv` is used: the compatible family of ring maps `B →+* R ⧸ Iⁿ⁺¹` has a
limit `ψ : B →+* R` by completeness, and the morphism is `(specHomEquiv I B).symm ψ`.

Now compare the two correspondences at exactly that point.

```lean
FormalSpectrum.specHomEquiv I B : (Spf R ⟶ Spec B) ≃ (B →+* R)
AdicRingCat.spfHomEquiv C S hC hS :
    (C ⟶ S) ≃ { f : Spf S ⟶ Spf C // C.ideal ≤ S.ideal.comap (globalSectionsMap _ _ f) }
```

`specHomEquiv`'s right-hand side is **all** ring homomorphisms `B →+* R`. `spfHomEquiv`'s is the
**continuous** ones on the left (`AdicRingCat` morphisms are continuous by definition,
`AdicRingCat.homRingHomEquiv`) and a **subtype** cut out by a continuity condition on the right.
Substituting it for `specHomEquiv` at the point above therefore needs the limit homomorphism
`ψ : C →+* R` to satisfy `L ≤ I.comap ψ`, and **the input does not supply that.** The input is a
compatible family of morphisms of *locally ringed spaces* `Spec (R ⧸ Iⁿ⁺¹) ⟶ Spf L`; the structure
sheaves carry no ambient topology, which is precisely the issue-156 phenomenon that forced
`spfHomEquiv` to be stated on a subtype in the first place
(`FormalSchemes/SpfFullyFaithful.lean`'s module docstring says so).

**So the answer to goal 1 is no**, and the obstruction is not a missing naturality lemma that a
successor can grind out: it is that the two `Equiv`s have different right-hand sides, and the
difference is exactly the hypothesis that is unavailable. Both signatures are `#check`ed in the
`Crux` section below, so the comparison can be read off the tree instead of off this docstring.

The negative answer stands — the two `Equiv`s really do have different right-hand sides — but it is
**not** the obstruction it was taken to be: `FormalSchemes/SpfTargetSurjective.lean` proves the
affine case without substituting `AdicRingCat.spfHomEquiv` anywhere, by route 2 below. See the
correction to that route.

`FormalSpectrum.existsUnique_hom_thickeningMap_spf_of_continuous` below is what survives *of the
`AdicRingCat.spfHomEquiv` route*, and it is weaker than its name suggests. Its family is
`FormalSpectrum.spfTargetFamily`, which is **defined** as the restriction of `Spf ψ`, so the
theorem presupposes not merely a continuity
witness but a `ψ` whose induced family *is* the given one — strictly more than continuity, and
producing such a `ψ` from a bare family is route 1 below, which does not invert. It is stated to
make the shape of the missing input explicit, not to reduce the gap to continuity.
`FormalSpectrum.existsUnique_hom_thickeningMap_spf`
(`FormalSchemes/SpfTargetSurjective.lean`) is the unconditional statement and needs neither a `ψ`
nor a continuity witness; a successor should cite that one.

## Two routes that were considered, and the correction to the second

Neither is cited by any proof *in this file*. **Route 2 is the one that closed the problem**, in
`FormalSchemes/SpfTargetSurjective.lean`, and the paragraph below stating that it inherits issue
62k's open problem was wrong; the correction is spelled out there and repeated at the end of the
route.

1. *Compose with `ι : Spf L ⟶ Spec C` and use the `Spec`-target theorem.* This produces a
   `g : Spf R ⟶ Spec C` and a `ψ : C →+* R`, but it cannot be inverted, because `ι` is not
   expected to be a monomorphism: on a basic open, `ι` presents `𝒪_{Spec C}(D(c)) = C_c` where
   `𝒪_{Spf L}` has the completion `C{1/c}`, so a morphism into `Spf L` carries strictly more data
   than its composite with `ι`. **Not checked, and not used.**
2. *Recover continuity from the family.* The base map of the family lands in `V(L)`, which on the
   ring side gives only `L.map ψ ≤ (I).radical` — a containment up to radical, not the equality
   `L ≤ I.comap ψ` that `AdicRingCat.spfHomEquiv` wants. **This route works, and the sentence that
   used to follow here — that it inherits issue 62k's open problem — was false.** Issue 62k
   (`FormalSchemes/AdicCofinalOpenImmersion.lean`) is open in its *openness* half, `J ≤ √(I · B)`;
   what this route needs is the *nilpotence* half, `L.map ψ ≤ (I).radical`, which #418 proved
   unconditionally as `FormalSpectrum.map_le_radical_of_hom`. With `L` finitely generated the
   radical containment is `L ^ k ≤ I.comap ψ`, and the resulting `Spf (L ^ k)`-versus-`Spf L`
   slack is absorbed
   by `FormalSpectrum.cofinalSpfIso`, which is a theorem and not a gap. See
   `FormalSchemes/SpfTargetSurjective.lean`.

A third route, which this file also does not take, is the only one that avoids a ring homomorphism
entirely: build the morphism `Spf R ⟶ Spf L` directly out of its sheaf map, using that sections of
`𝒪_{Spf R}` over an open are the limit of the sections of the `𝒪_{Spec (R ⧸ Iⁿ⁺¹)}` over it —
which is what `sectionsLimitIso` says, and what the proof of `hom_ext_thickeningMap_lrs` already
exploits for the uniqueness half. It is a suggestion, not a plan, and the reason for preferring it
is negative: routes 1 and 2 both fail at a ring homomorphism, and this one has none.
`FormalSchemes/AdicCofinalOpenImmersion.lean`'s module docstring carries a similarly-shaped
sheaf-theoretic sketch — also explicitly unformalised, and for the *different* problem of issue 62k
— which is worth reading first for the shape of the argument, not for its statement.

## Which of `ThickeningChartSpfHom.lean`'s declarations survive a change of target

Read off its statements, not guessed from its proofs. `X` there is **already** a bare
`LocallyRingedSpace`. Of the thirteen declarations before its witness section, **five** mention
neither `B` nor `e` and survive verbatim; the other **eight** carry the target datum in their
statements, and of those only **four** — `chartSpfHom`, `thickeningMap_comp_chartSpfHom` and the
two `…Ambient` declarations that go through them — are actually blocked.

* `LocallyRingedSpace.restrictLE` and `restrictLE_comp_ofRestrict`: **verbatim** — they mention no
  target at all.
* `chartInclusion`, `chartInclusion_comp_ofRestrict`, `chartStepLRS_comp_chartInclusion`:
  **verbatim** — they are about the *source*'s thickenings.
* `chartFamily`, `chartFamily_step`: **restate**, with the target `Spec (CommRingCat.of B)` replaced
  by `locallyRingedSpaceObj (J i)`. `chartFamily_step`'s proof mentions neither `B` nor `e`.
* `chartThickeningFamily`: **restate** at `ThickeningFamilyLRS`, which *equals* `ThickeningFamily`
  at an affine target (`thickeningFamily_eq_thickeningFamilyLRS`).
* `chartSpfHom` and `thickeningMap_comp_chartSpfHom`: were **blocked** on the crux above. They are
  no longer blocked — `FormalSpectrum.thickeningRestrictionEquivSpfOfFG`
  (`FormalSchemes/SpfTargetSurjective.lean`) is exactly the `Equiv` whose `.symm` `chartSpfHom` is
  built from, at a formal-affine target. **The `Spf`-shaped analogues have not been written**, so
  this is an unblocking, not a delivery.
* `chartSpfHom_uniq`: **available now**, from `injective_restrictToThickeningsLRS`.
* `chartSpfHomAmbient` and `thickeningMap_comp_chartSpfHomAmbient`: were blocked only *through*
  `chartSpfHom`; their own proofs are target-agnostic, so they are unblocked with it.
* The whole `Witness` section: needs a new witness with a genuine formal-affine cover (goal 4).

## Non-vacuity

`[IsAdicRing I]` holds at `I = ⊥`, where every thickening is `Spec R` and every statement here is
about a constant tower. The witness section runs the two theorems at the `2`-adic integers on both
sides, where `FormalSpectrum.twoAdicIdeal_ne_bot` (`FormalSchemes/TwoAdicWitness.lean`) excludes
that.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7–10.6.10).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Restriction to the thickenings is injective, for an arbitrary target.** No hypothesis on `X`:
this is `hom_ext_thickeningMap_lrs` read as a statement about `restrictToThickeningsLRS`, and it is
the half of `thickeningRestrictionEquivLRS` that does not need the target to be covered by affines.

Consequently, for any target whatever, the colimit property of `Spf R` is *exactly* surjectivity of
this map; see `thickeningRestrictionEquivSpf` for the formal-affine case. -/
theorem injective_restrictToThickeningsLRS (X : LocallyRingedSpace.{u}) :
    Function.Injective (restrictToThickeningsLRS I X) := fun _ _ h =>
  hom_ext_thickeningMap_lrs _ _ fun n => congrFun (congrArg (fun t => t.1) h) n

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Uniqueness is free: for an arbitrary target the `∃!` of EGA I 10.6.10 follows from the bare
`∃`.** Note that the compatibility of the family is not needed — it is needed to *produce* the
morphism, not to pin it down once produced.

A successor proving the existence half at a formal-affine target should discharge its `∃!` through
this rather than rebuilding the uniqueness clause. -/
theorem existsUnique_hom_thickeningMap_of_exists {X : LocallyRingedSpace.{u}}
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (h : ∃ g : locallyRingedSpaceObj I ⟶ X, ∀ n : ℕ, thickeningMap I n ≫ g = f n) :
    ∃! g : locallyRingedSpaceObj I ⟶ X, ∀ n : ℕ, thickeningMap I n ≫ g = f n := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg, fun g' hg' => hom_ext_thickeningMap_lrs g' g fun n => (hg' n).trans (hg n).symm⟩

/-- **Surjectivity is what the landed theorem supplies.** At a target carrying a `Spec`-shaped
cover, `thickeningRestrictionEquivLRS` is a bijection whose forward map is
`restrictToThickeningsLRS` on the nose, so it gives surjectivity. Recording it separately is what
makes "surjectivity is the entire remaining content" a factorisation of the landed theorem rather
than a new phrasing of it: together with `injective_restrictToThickeningsLRS` it rebuilds
`thickeningRestrictionEquivLRS` up to `Equiv.ofBijective`. -/
theorem surjective_restrictToThickeningsLRS (X : LocallyRingedSpace.{u}) (hI : I.FG)
    {ι : Type u} (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤) (B : ι → Type u)
    [∀ i, CommRing (B i)]
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i))) :
    Function.Surjective (restrictToThickeningsLRS I X) :=
  (thickeningRestrictionEquivLRS I X hI U hU B e).surjective

section SpfTarget

variable {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]

/-- **The bijection at a formal-affine target, given surjectivity.** Injectivity is
`injective_restrictToThickeningsLRS`, so this records that surjectivity of
`restrictToThickeningsLRS I (Spf L)` is the *entire* remaining content of the `Spf`-target colimit
property at an affine target — and hence the exact statement issue 62m's goal 2 has to prove.

Compare `thickeningRestrictionEquivLRS`, which obtains surjectivity from a `Spec`-shaped cover of
the target. `Spf L` has no such cover, which is why the hypothesis appears here as an argument. -/
def thickeningRestrictionEquivSpf
    (hsurj : Function.Surjective (restrictToThickeningsLRS I (locallyRingedSpaceObj L))) :
    (locallyRingedSpaceObj I ⟶ locallyRingedSpaceObj L) ≃
      ThickeningFamilyLRS I (locallyRingedSpaceObj L) :=
  Equiv.ofBijective _ ⟨injective_restrictToThickeningsLRS I _, hsurj⟩

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace C] [IsAdicRing L] in
/-- **Computation rule.** The forward map is restriction to the thickenings, as for every other
member of this family of bijections. -/
theorem thickeningRestrictionEquivSpf_apply
    (hsurj : Function.Surjective (restrictToThickeningsLRS I (locallyRingedSpaceObj L)))
    (g : locallyRingedSpaceObj I ⟶ locallyRingedSpaceObj L) (n : ℕ) :
    (thickeningRestrictionEquivSpf I L hsurj g).1 n = thickeningMap I n ≫ g :=
  rfl

variable (ψ : C →+* R) (hψ : L ≤ I.comap ψ)

/-- **The family attached to a continuous ring homomorphism**: the restrictions of `Spf ψ` to the
thickenings of `Spf R`. This is the only way currently available on the tree of producing a member
of `ThickeningFamilyLRS I (Spf L)` that is known to come from a morphism, and it is what makes the
`Spf`-target statements below non-vacuous. -/
def spfTargetFamily : ThickeningFamilyLRS I (locallyRingedSpaceObj L) :=
  restrictToThickeningsLRS I _ (locallyRingedSpaceMap L I ψ hψ)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace C] [IsAdicRing L] in
/-- **Computation rule for `spfTargetFamily`.** -/
theorem spfTargetFamily_apply (n : ℕ) :
    (spfTargetFamily I L ψ hψ).1 n = thickeningMap I n ≫ locallyRingedSpaceMap L I ψ hψ :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace C] [IsAdicRing L] in
/-- **The `Spf`-target colimit property, on the families that a continuity witness is available
for.** This is what survives of `AdicRingCat.spfHomEquiv` at the point issue 62m's step 3 needs it:
the existence half is `locallyRingedSpaceMap` and needs `hψ`, the uniqueness half is
`hom_ext_thickeningMap_lrs` — which is stated for an arbitrary target — and needs nothing.

Note what this does *not* say. The family is `spfTargetFamily I L ψ hψ`, which is defined as the
restriction of `Spf ψ`, so the theorem applies only to families already known to come from a
continuous `ψ`. A compatible family of morphisms of locally ringed spaces
`Spec (R ⧸ Iⁿ⁺¹) ⟶ Spf L` comes with neither the `ψ` nor the continuity witness, and recovering a
`ψ` from one is route 1 of this file's module docstring, which does not invert. So this theorem is
not a proof of the general statement and must not be cited as one. -/
theorem existsUnique_hom_thickeningMap_spf_of_continuous :
    ∃! g : locallyRingedSpaceObj I ⟶ locallyRingedSpaceObj L,
      ∀ n : ℕ, thickeningMap I n ≫ g = (spfTargetFamily I L ψ hψ).1 n :=
  existsUnique_hom_thickeningMap_of_exists I _ ⟨locallyRingedSpaceMap L I ψ hψ, fun _ => rfl⟩

end SpfTarget

section Crux

/-! ### The crux, as two types rather than as prose

The module docstring's answer to issue 62m's goal 1 is a comparison of two right-hand sides. Both
are `#check`ed here so that the comparison is read off the tree rather than taken on trust. -/

/-- `specHomEquiv`'s right-hand side is **all** ring homomorphisms `B →+* R`. This is the
correspondence `existsUnique_thickeningMap_comp` uses to turn the limit of a compatible family of
ring maps into a morphism, and it is the point issue 62m's step 3 depends on. -/
example (B : Type u) [CommRing B] :
    (locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) ≃ (B →+* R) :=
  specHomEquiv I B

/-- `spfHomEquiv`'s right-hand side is a **subtype**, cut out by continuity of the global-sections
map — and its left-hand side is `AdicRingCat` morphisms, which are continuous by definition. Neither
side is the unrestricted hom-set that the previous example has, which is why it cannot be
substituted for `specHomEquiv` at that point: a compatible family of morphisms of locally ringed
spaces supplies no continuity witness. -/
example (A A' : AdicRingCat.{u}) (hA : A.ideal.FG) (hA' : A'.ideal.FG) :
    (A ⟶ A') ≃
      { f : AdicRingCat.spfFunctor.obj (op A') ⟶ AdicRingCat.spfFunctor.obj (op A) //
        A.ideal ≤ A'.ideal.comap (globalSectionsMap A.ideal A'.ideal f.toLRSHom) } :=
  AdicRingCat.spfHomEquiv A A' hA hA'

end Crux

section Witness

/-! ### Non-vacuity

Everything above is stated under `[IsAdicRing I]`, which is satisfied at `I = ⊥` — where the tower
of thickenings is constant and the statements say nothing. The `2`-adic integers rule that out:
`twoAdicIdeal_ne_bot` (`FormalSchemes/TwoAdicWitness.lean`). Both the source and the target are
formal-affine and genuinely adic here, which is the configuration issue 62m is about; the `Spec`
witnesses of `IndSchemeExistenceGeometric.lean` and `ThickeningChartSpfHom.lean` have an affine
*scheme* on the right and so exercise nothing of this file. -/

attribute [local instance] isAdicRing_twoAdicIdeal

/-- **A member of `ThickeningFamilyLRS` at a formal-affine, genuinely adic target**: the
restrictions of the identity of `Spf ℤ₂` to the thickenings. -/
example : ThickeningFamilyLRS twoAdicIdeal (locallyRingedSpaceObj twoAdicIdeal) :=
  spfTargetFamily twoAdicIdeal twoAdicIdeal (RingHom.id _) le_rfl

/-- **…and it comes from a unique morphism `Spf ℤ₂ ⟶ Spf ℤ₂`**, with `twoAdicIdeal ≠ ⊥`. -/
example : ∃! g : locallyRingedSpaceObj twoAdicIdeal ⟶ locallyRingedSpaceObj twoAdicIdeal,
    ∀ n : ℕ, thickeningMap twoAdicIdeal n ≫ g =
      (spfTargetFamily twoAdicIdeal twoAdicIdeal (RingHom.id _) le_rfl).1 n :=
  existsUnique_hom_thickeningMap_spf_of_continuous twoAdicIdeal twoAdicIdeal (RingHom.id _) le_rfl

/-- Restriction to the thickenings is injective at that same target — the half of the colimit
property that this file settles unconditionally. -/
example : Function.Injective
    (restrictToThickeningsLRS twoAdicIdeal (locallyRingedSpaceObj twoAdicIdeal)) :=
  injective_restrictToThickeningsLRS twoAdicIdeal _

end Witness

end FormalSpectrum

end
