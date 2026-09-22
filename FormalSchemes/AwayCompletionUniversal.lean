import FormalSchemes.AwayBaseChangeTopFiniteType
import FormalSchemes.AwayCompletionRestrictUnique
import FormalSchemes.AwayTopFiniteType

set_option linter.style.header false

/-!
# `R{1/f}` as a base ring: its universal property, and what becomes `R{1/f}`-linear

`FormalSpectrum.awayCompletion I f` — the completed localization `R{1/f}` — is built in
`FormalSchemes.BasicOpenChart` as the ring of the basic-open chart of `Spf (R, I)`, and reading it
as a **base ring in its own right** is not new here: `FormalSpectrum.awayBaseAlgebra`
(`FormalSchemes.AwayBaseChangeTopFiniteType`) already makes `A{1/(c·A)}^` an `R{1/c}^`-algebra.
What this file adds is the shape of the map that installs such a structure. That one is
`FormalSpectrum.awayBaseHom`, an `AdicCompletion.mapCompletion` (`FormalSchemes.Completion`)
transported from a localization map, and its target is again an away completion over `R`; the maps
below go **out of** `R{1/f}` into an *arbitrary* adically complete `R`-algebra, and are *produced*
by a universal property rather than transported. The contrast is one of shape and not of content:
where both constructions apply they are the same map, which is
`FormalSpectrum.awayBaseHom_eq_awayCompletionLift` below. Read as a base ring, `R{1/f}` is the
affine base a morphism `X ⟶ Spf (R, I)` acquires when it factors through the basic open `D(f)`, and
the question this file answers is what of an affine-chart presentation of `X` over `(R, I)`
survives that change of base.

Three things do — an `R{1/f}`-algebra structure on each chart algebra, the ideal it induces
there, and the `R{1/f}`-linearity of the transitions between charts — and they are the three
outputs the change of base needs. Nothing here is about formal schemes; it is all commutative
algebra, which is the point: the geometry contributes only the hypothesis that `f` is invertible on
each chart.

## The universal property

`R{1/f}` is the `I`-adic completion of `Localization.Away f`, so a ring map out of it into an
`L`-adically complete target is determined by, and can be built from, a ring map out of
`Localization.Away f`; and a ring map out of that is a ring map out of `R` inverting `f`. Putting
the two together:

* `FormalSpectrum.awayCompletionLift`: an `R`-algebra `A` which is `I·A`-adically complete and in
  which the image of `f` is a unit receives a canonical `R{1/f} →+* A` under `R`.
* `FormalSpectrum.eq_awayCompletionLift`: the lift is the *only* such map. Uniqueness is
  `FormalSpectrum.awayCompletion_hom_ext'` (`FormalSchemes.AwayCompletionRestrictUnique`), the
  rigidity principle at an arbitrary complete target. That statement is not new here: it is the
  old `FormalSpectrum.awayCompletion_hom_ext` with the target released from `R{1/g}` to an
  arbitrary complete ring, generalised in place in the file that owned it, with the old form kept
  as the one-line case `(A, L) = (R{1/g}, awayCompletionIdeal I g)`. Nothing below re-proves it.

## The continuity question, which is this file's first finding

Recovering a ring map from a geometric factorisation and then asking whether it is continuous is
the shape the Spf–Γ round trip `FormalSpectrum.spfGammaEquiv` (`FormalSchemes.SpfGammaRoundTrip`)
imposes: it is a bijection between morphisms of formal spectra and ring maps **already known** to
carry one ideal of definition into the other, so continuity is one of its inputs and never one of
its conclusions.

**Over a basic open of the base that question does not arise at all.** The ideal of definition of
`R{1/f}` *is* the extension of `I` along the structural map — that is
`FormalSpectrum.map_awayCompletionHom` (`FormalSchemes.BasicOpenChart`) — so any ring map
`R{1/f} →+* A` which is a map **under `R`** carries it into `I·A` by `Ideal.map_map` and nothing
else. That is `FormalSpectrum.le_comap_of_comp_awayCompletionHom_eq_algebraMap`, a two-line
consequence, and it is what discharges the hypotheses of both
`FormalSpectrum.awayCompletion_hom_ext'` and `FormalSpectrum.eq_awayCompletionLift` at every use
site in this file. For a general adic base `(R', I')` the question is a real one, this file does
not settle it, and its on-the-nose form is refuted elsewhere on the tree — see *What is not proved
here* below; for `(R', I') = (R{1/f}, I·R{1/f})` it is empty.

## The two outputs that follow

* **The induced ideals do not move.** `Ideal.map_algebraMap_family_eq_of_tower` says that for a
  family `A` of `R{1/f}`-algebras over `R`, the family `fun i => I'·A i` computed over the new
  base is *equal*, as a function, to `fun i => I·A i` computed over the old one. It is
  `Ideal.map_algebraMap_of_tower` (`FormalSchemes.AwayTopFiniteType`) under a `funext`, and the
  function-level spelling is not decoration — see that lemma's docstring for the three spellings
  and which one a consumer can actually use.
* **`R`-linear becomes `R{1/f}`-linear, for free.** `FormalSpectrum.awayCompletionAlgEquiv`
  upgrades an `R`-algebra equivalence between two complete `R{1/f}`-algebras to an
  `R{1/f}`-algebra equivalence, with no hypothesis beyond finite generation of `I` and
  completeness of the target — the two composites `R{1/f} → S → T` and `R{1/f} → T` are then maps
  under `R` into a complete target, so rigidity identifies them.
  `FormalSpectrum.awayCompletionChartAlgEquivBase` is the same statement at the shape the chart
  transitions actually have, `A{1/s}^ ≃ₐ[R] A'{1/s'}^`, where that completeness is automatic.

## Main definitions

* `FormalSpectrum.awayLocLift`, `FormalSpectrum.awayLocLiftₐ`: the localization half of the lift.
* `FormalSpectrum.awayCompletionLift`: the universal property of `R{1/f}`.
* `FormalSpectrum.awayCompletionAlgEquiv`, `FormalSpectrum.awayCompletionChartAlgEquivBase`: an
  `R`-algebra equivalence read over the base `R{1/f}`.
* `FormalSpectrum.awayCompletionChartEquivOfLe` and its `R`-algebra forms
  `FormalSpectrum.awayCompletionChartAlgEquivOfLe`,
  `FormalSpectrum.awayCompletionNestedAlgEquivOfLe`: the nested chart identification
  `A{1/g} ≃ A{1/f}{1/ĝ}` at a containment `D(g) ≤ D(f)` of basic opens of `Spf (A, J)`.

## Main results

* `FormalSpectrum.awayCompletionLift_comp_awayCompletionHom` and
  `FormalSpectrum.map_awayCompletionLift`: the lift is a map under `R` and carries the ideal of
  definition *onto* `I·A`.
* `FormalSpectrum.le_comap_of_comp_awayCompletionHom_eq_algebraMap`: continuity is free under `R`.
* `FormalSpectrum.eq_awayCompletionLift`: uniqueness of the lift.
* `FormalSpectrum.isScalarTower_awayCompletionLift`: the lift makes `R → R{1/f} → A` a tower.
* `Ideal.map_algebraMap_family_eq_of_tower`: the induced ideal families agree, as functions.
* `FormalSpectrum.algEquiv_commutes_awayCompletion`: an `R`-algebra map between complete
  `R{1/f}`-algebras is `R{1/f}`-linear.
* `FormalSpectrum.awayBaseHom_eq_awayCompletionLift`: the structural map of the away base change is
  the lift, so the transported and the universal `R{1/f} → A{1/(f·A)}^` are one map.
* `FormalSpectrum.awayCompletionChartInvOfLe_comp_homOfLe` and
  `FormalSpectrum.awayCompletionChartHomOfLe_comp_invOfLe`: both composites of that identification
  are identities, by rigidity and nothing else.

## The identification at a containment, and what it replaces

`FormalSpectrum.awayCompletionChartEquiv` (`FormalSchemes.AwayCompletionInterchange`) identifies
`A{1/g}` with `A{1/f}{1/ĝ}` under `IsUnit (algebraMap A (Localization.Away g) f)`. That is an
inclusion of basic opens of `Spec A`, and it is **strictly stronger** than the corresponding
inclusion in `Spf (A, J)`, which is a congruence modulo `J`:
`FormalSchemes.AwayCompletionRestrict`'s own docstring opens by saying so, and the separation is
witnessed at `A = ℤ`, `J = (2)`, `f = 3`, `g = 5`, where `D(5) ≤ D(3)` holds and `3` is not a unit
of `ℤ[1/5]`.

The last section supplies the same identification keyed on the containment alone, and it does so
without reproving anything: the localization transitivity
`FormalSpectrum.awayAwayLocEquiv` (`FormalSchemes.AwayCompletionAway`) is what genuinely needs the
stronger hypothesis, and it is not used. Both maps are `FormalSpectrum.awayCompletionLift` — once
at `A{1/g}` over `A`, once at `A{1/f}{1/ĝ}` over `A{1/f}` — and both composites are identities by
`FormalSpectrum.awayCompletion_hom_ext'`. All the containment contributes is the `A{1/f}`-algebra
structure on `A{1/g}`, which is `FormalSpectrum.awayCompletionRestrict` together with
`FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le`: `f` is invertible in the **completion**
`A{1/g}` even where it is not in `Localization.Away g`. That is why the weaker hypothesis suffices,
and it is the reason this construction is a universal-property argument rather than a transitivity
one.

## What is *not* proved here

**The general affine base is untouched.** Nothing below produces an `R'`-algebra structure on a
chart from a factorisation through an arbitrary `Spf (R', I')`; the input is always an inverted
element of `R`, and `FormalSpectrum.awayCompletionLift` is the only construction offered. The map
`R' →+* A` that `FormalSpectrum.globalSectionsMap` (`FormalSchemes.SpfGamma`) supplies carries no
continuity hypothesis, and that it should carry `I'` into `I·A` is not an open question but one
this tree refutes: the refutation is recorded in `FormalSchemes.AdicOnSections`, and its witness is
`FormalSpectrum.cofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonIso`), which presents one adic
ring at two ideals of definition at once — so even an isomorphism of formal spectra can match
incompatible levels of the two filtrations. What makes the question empty below is therefore not
the universal property but the fact that the ideal of definition of `R{1/f}` is the extension of
`I`; where the base ideal is merely cofinal with the extension the containment is false, and
`Ideal.IsCofinal` is the form that survives (`FormalSchemes.AdicCofinalOpenImmersion`).

**No datum is base-changed.** `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData`
(`FormalSchemes.GeneralFibreProductExposeXAlgebraData`) is not used below and that module is not
imported here; assembling these three outputs into a datum over `R{1/f}` needs a congruence for
that constructor along the ideal-family equality. That congruence is **not** missing: it is
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`
(`FormalSchemes.GeneralFibreProductExposeXIdealCongr`), its conclusion is an equality of formal
schemes, and the hypothesis it takes is output 2 below in the same function-level spelling. What is
absent here is the assembly, not the comparison. Nothing here says anything about
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`, fibre products or diagonals.

**The `σ`-cocycle and the `τ`-symmetry identities are not restated over `R{1/f}`.**
`FormalSpectrum.awayCompletionAlgEquiv` does not change the underlying function of an equivalence
(`FormalSpectrum.awayCompletionAlgEquiv_apply` is `rfl`), so any identity between composites of
transitions transports along it by `AlgEquiv.ext`; but that transport is performed where the
identities live, not here.

## Placement

Over `FormalSchemes.AwayCompletionRestrictUnique`, `FormalSchemes.AwayTopFiniteType` and
`FormalSchemes.AwayBaseChangeTopFiniteType`: forward closure **55**, reverse closure **4**. Nothing
below mentions formal geometry, so an earlier home would be available on its own for each
declaration of the universal property; what keeps them in one file is that they are one argument —
the universal property, its uniqueness, and the two consequences that follow from it. The consumer
they were written for, the change of base of an affine-chart presentation to a basic open of its
base, is `FormalSchemes.AwayBaseChangeGluedX` (issue 2028), the nearest of the four modules above
this one — `FormalSchemes.AwayBaseChangeChartTransition` (issue 2070),
`FormalSchemes.AwayBaseChangeSeparated` (issue 1998) and
`FormalSchemes.AwayBaseFactorisationRange` (issue 2139) are the others, and each reaches this file
only through it.

The identification at the end has no earlier home at all: its two ingredients,
`FormalSpectrum.awayBaseHom` and `FormalSpectrum.awayCompletionLift`, live in modules neither of
which is in the other's closure, so stating it costs an import edge whichever way it is taken. The
edge runs this way because the other one, `FormalSchemes.AwayCompletionUniversal` imported into
`FormalSchemes.AwayBaseChangeTopFiniteType`, brings a much larger subtree into a file that has
consumers, and a new leaf over both would pay the leaf tax on every module in its own closure. The
deltas are measured in the pull request that added the edge (issue 2019).

**The identification at a containment is placed here on a rebuild ratio, and the alternatives are
measured.** Its subject matter is `FormalSchemes.AwayCompletionNested`, which carries the same
identification at the stronger hypothesis; but that module does not import this one, and taking
the edge would add **35** modules to what it transitively imports, against
`FormalSchemes.AwayCompletionNested`'s reverse closure of **16**. A new leaf over this file costs
no edge and re-elaborates the leaf and the root aggregator, and then pays the leaf tax: every
import-count figure quoted in the modules it transitively imports moves by one. On the head that
added `FormalSchemes.RefinedOverlapRestrict` that was **18** figures in **14** files. Stating it
here adds no module, no edge and no figure repair, and re-elaborates this file's reverse closure
of **4**. The
proof is two applications of `FormalSpectrum.awayCompletionLift` and two of
`FormalSpectrum.awayCompletion_hom_ext'`, both of which are this file's own subject, so the ratio
and the subject matter pull apart less than the module name suggests. Re-cost the move if a second
module asks for the identification.

The one edit to a declaration outside this file is the generalisation of
`FormalSpectrum.awayCompletion_hom_ext` to `FormalSpectrum.awayCompletion_hom_ext'`, taken **in
place** in `FormalSchemes.AwayCompletionRestrictUnique`, whose reverse closure is **33**. Besides
this module's own line in the root module list `FormalSchemes.lean`, which `lake exe mk_all`
maintains and which adding any module forces, the rest of the diff that created this module is
prose: the figures a new leaf moves in the modules above it, and the sentence in
`FormalSchemes.AwayTopFiniteType` recording `Ideal.map_algebraMap_of_tower` as unused, which output
2 below made false. Restating the general form here instead would have cost no rebuild and was
declined on two grounds: it would leave two near-duplicate rigidity statements in the tree, which
is the shape the duplicate statement scan under `scripts/` exists to catch; and the general form is
the true one, the old special form being recovered from it in a single line. The old name,
statement and binder order are unchanged, so no call site moved — its one consumer outside its own
file is `FormalSchemes.BasicOpenChartOpensSections`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.6 and Ch. I, §10.1.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

universe u

/-- **The induced ideal families of a change of base agree, as functions.** For `R'` an
`R`-algebra with `I' = I·R'` and a family `A` of `R'`-algebras over `R`, extending `I'` to `A i`
along `R' → A i` gives the same ideal as extending `I` along `R → A i`.

The pointwise statement is `Ideal.map_algebraMap_of_tower` (`FormalSchemes.AwayTopFiniteType`) at
`(J, K) = (I, I·R')`, whose hypothesis is then `rfl`. The content this adds is the **function-level
spelling**, and it is not decoration. A family of ideals indexed by the charts occurs inside the
`Ideal.FG` proof arguments of the chart data, where a rewrite fails on a non-type-correct motive;
the tactic that does move such a family is `subst`, and `subst` requires one side of the equation
to be a *variable*. Of the three spellings, only the last is accepted: `∀ i, K i = I·A i` is
refused because `K i` is an application, `(fun i => K i) = fun i => I·A i` is refused for the same
reason once the binder is peeled, and `K = fun i => I·A i` with `K : ∀ i, Ideal (A i)` a variable
goes through. So the equation a consumer needs is one it can generalize into that last shape,
which is this one and is not the pointwise one. -/
theorem Ideal.map_algebraMap_family_eq_of_tower {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] {J : Type*} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)] (I : Ideal R) :
    (fun i => (I.map (algebraMap R R')).map (algebraMap R' (A i))) =
      fun i => I.map (algebraMap R (A i)) :=
  funext fun _ => (Ideal.map_algebraMap_of_tower I _ rfl).symm

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R)

/-!
### The universal property of `R{1/f}`
-/

section Lift

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The localization half of the lift**: the ring map `Localization.Away f →+* A` attached to
an `R`-algebra `A` in which the image of `f` is a unit, by the universal property of
`Localization.Away f`. -/
def awayLocLift (hf : IsUnit (algebraMap R A f)) : Localization.Away f →+* A :=
  IsLocalization.Away.lift (S := Localization.Away f) f hf

/-- The localization lift is a map under `R`. -/
theorem awayLocLift_comp (hf : IsUnit (algebraMap R A f)) :
    (awayLocLift f hf).comp (algebraMap R (Localization.Away f)) = algebraMap R A :=
  IsLocalization.Away.lift_comp _ _

/-- `FormalSpectrum.awayLocLift` as an `R`-algebra homomorphism. It exists only to feed
`Ideal.map_algebraMap_pow_le_comap` (`FormalSchemes.AdicExtend`), which is stated for an
`AlgHom`. -/
def awayLocLiftₐ (hf : IsUnit (algebraMap R A f)) : Localization.Away f →ₐ[R] A :=
  { awayLocLift f hf with
    commutes' := fun r => RingHom.congr_fun (awayLocLift_comp f hf) r }

/-- **Continuity of the localization lift**, in the filtration form
`AdicCompletion.extendRingHom` (`FormalSchemes.AdicExtend`) consumes: it carries the `m`-th power
of `I` extended to `Localization.Away f` into the `m`-th power of `I·A`, for every `m`, because it
is a map of `R`-algebras. -/
theorem awayLocLift_pow_le (hf : IsUnit (algebraMap R A f)) (m : ℕ) :
    (I.map (algebraMap R (Localization.Away f))) ^ m ≤
      ((I.map (algebraMap R A)) ^ m).comap (awayLocLift f hf) :=
  Ideal.map_algebraMap_pow_le_comap I _ le_rfl (awayLocLiftₐ f hf) m

variable [IsAdicComplete (I.map (algebraMap R A)) A]

/-- **The universal property of `R{1/f}`.** An `R`-algebra `A` which is `I·A`-adically complete
and in which the image of `f` is a unit receives a canonical ring map `R{1/f} →+* A`: invert `f`
by `FormalSpectrum.awayLocLift`, then pass to the completion by `AdicCompletion.extendRingHom`
(`FormalSchemes.AdicExtend`).

The completeness hypothesis is what makes the second step possible and the finite generation of
`I` is *not* needed for it — that enters only in the uniqueness statement
`FormalSpectrum.eq_awayCompletionLift`. -/
def awayCompletionLift (hf : IsUnit (algebraMap R A f)) : awayCompletion I f →+* A :=
  AdicCompletion.extendRingHom _ (I.map (algebraMap R A)) (awayLocLift f hf)
    (awayLocLift_pow_le I f hf)

/-- **The lift is a map under `R`**: composed with the structural map `R → R{1/f}` it is the
structure map of `A`. -/
theorem awayCompletionLift_comp_awayCompletionHom (hf : IsUnit (algebraMap R A f)) :
    (awayCompletionLift I f hf).comp (awayCompletionHom I f) = algebraMap R A := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, awayCompletionHom, RingHom.comp_apply,
    show (algebraMap (Localization.Away f) (awayCompletion I f))
        (algebraMap R (Localization.Away f) r) =
      AdicCompletion.of (I.map (algebraMap R (Localization.Away f))) (Localization.Away f)
        (algebraMap R (Localization.Away f) r) from rfl,
    awayCompletionLift, AdicCompletion.extendRingHom_of]
  exact RingHom.congr_fun (awayLocLift_comp f hf) r

/-- The applied form of `FormalSpectrum.awayCompletionLift_comp_awayCompletionHom`. -/
theorem awayCompletionLift_awayCompletionHom (hf : IsUnit (algebraMap R A f)) (r : R) :
    awayCompletionLift I f hf (awayCompletionHom I f r) = algebraMap R A r :=
  RingHom.congr_fun (awayCompletionLift_comp_awayCompletionHom I f hf) r

/-- **The lift makes `R → R{1/f} → A` a scalar tower**, for the algebra structure it defines. The
`letI` in the statement is unavoidable: the `Algebra` instance is the conclusion's own subject and
is not synthesizable, since it depends on the proof `hf`. -/
theorem isScalarTower_awayCompletionLift (hf : IsUnit (algebraMap R A f)) :
    letI := (awayCompletionLift I f hf).toAlgebra
    IsScalarTower R (awayCompletion I f) A :=
  letI := (awayCompletionLift I f hf).toAlgebra
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [← awayCompletionHom_eq_algebraMap]
    exact (awayCompletionLift_awayCompletionHom I f hf r).symm

end Lift

/-!
### Continuity under `R`, and uniqueness of the lift
-/

section Uniqueness

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **Continuity is free for a map under `R`.** The ideal of definition of `R{1/f}` is the
extension of `I` along the structural map (`FormalSpectrum.map_awayCompletionHom`,
`FormalSchemes.BasicOpenChart`), so a ring map `R{1/f} →+* A` restricting to the structure map of
`A` carries it into `I·A` by `Ideal.map_map` alone.

This is the reason the change of base to a basic open never has to discharge the continuity
binder of the Spf–Γ round trip `FormalSpectrum.spfGammaEquiv`
(`FormalSchemes.SpfGammaRoundTrip`): the map is not recovered from a morphism of formal spectra,
it is built under `R`, and being under `R` is already the continuity.

`FormalSpectrum.le_comap_of_comp_awayCompletionHom` (`FormalSchemes.BasicOpenChart`) is the same
argument with the target specialised to another completed localization of the *same* ring `R`. That
one is recoverable from this one at `A = awayCompletion I g`, but not by instantiation alone:
`FormalSpectrum.awayCompletionHom_eq_algebraMap` and `FormalSpectrum.map_awayCompletionHom` have to
be rewritten through first, to read `awayCompletionIdeal I g` as an extension of `I`. Both are
stated for that reason — and in any case the older one could not be replaced by this one, since it
is proved in a module this file imports. -/
theorem le_comap_of_comp_awayCompletionHom_eq_algebraMap {F : awayCompletion I f →+* A}
    (hF : F.comp (awayCompletionHom I f) = algebraMap R A) :
    awayCompletionIdeal I f ≤ (I.map (algebraMap R A)).comap F := by
  rw [← Ideal.map_le_iff_le_comap, ← map_awayCompletionHom I f, Ideal.map_map, hF]

/-- **The lift carries the ideal of definition onto `I·A`**, not merely into it: both sides are
the extension of `I` along the structural map of `A`. -/
theorem map_awayCompletionLift [IsAdicComplete (I.map (algebraMap R A)) A]
    (hf : IsUnit (algebraMap R A f)) :
    (awayCompletionIdeal I f).map (awayCompletionLift I f hf) = I.map (algebraMap R A) := by
  rw [← map_awayCompletionHom I f, Ideal.map_map, awayCompletionLift_comp_awayCompletionHom]

/-- **The lift is the unique map under `R`.** Any ring map `R{1/f} →+* A` into a complete
`R`-algebra restricting to the structure map of `A` is `FormalSpectrum.awayCompletionLift`; its
continuity is not a hypothesis, because
`FormalSpectrum.le_comap_of_comp_awayCompletionHom_eq_algebraMap` supplies it. -/
theorem eq_awayCompletionLift (hI : I.FG) [IsAdicComplete (I.map (algebraMap R A)) A]
    (hf : IsUnit (algebraMap R A f)) {F : awayCompletion I f →+* A}
    (hFsq : F.comp (awayCompletionHom I f) = algebraMap R A) :
    F = awayCompletionLift I f hf :=
  awayCompletion_hom_ext' I f hI (le_comap_of_comp_awayCompletionHom_eq_algebraMap I f hFsq)
    (le_comap_of_comp_awayCompletionHom_eq_algebraMap I f
      (awayCompletionLift_comp_awayCompletionHom I f hf))
    (by rw [hFsq, awayCompletionLift_comp_awayCompletionHom])

end Uniqueness

/-!
### `R`-linear becomes `R{1/f}`-linear
-/

section Linearity

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable [Algebra (awayCompletion I f) S] [Algebra (awayCompletion I f) T]
variable [IsScalarTower R (awayCompletion I f) S] [IsScalarTower R (awayCompletion I f) T]
variable [IsAdicComplete (I.map (algebraMap R T)) T]

/-- **An `R`-algebra map between `R{1/f}`-algebras is `R{1/f}`-linear.** Both
`R{1/f} → S → T` and `R{1/f} → T` are ring maps under `R` into a target complete for `I·T`, so
`FormalSpectrum.awayCompletion_hom_ext'` identifies them; the continuity each needs is
`FormalSpectrum.le_comap_of_comp_awayCompletionHom_eq_algebraMap`.

No hypothesis is placed on `S` — only the target has to be complete, because rigidity is a
statement about where the two maps land. -/
theorem algEquiv_commutes_awayCompletion (hI : I.FG) (e : S ≃ₐ[R] T)
    (x : awayCompletion I f) :
    e (algebraMap (awayCompletion I f) S x) = algebraMap (awayCompletion I f) T x := by
  have hsq : ∀ F : awayCompletion I f →+* T,
      F.comp (algebraMap R (awayCompletion I f)) = algebraMap R T →
      awayCompletionIdeal I f ≤ (I.map (algebraMap R T)).comap F := fun F hF =>
    le_comap_of_comp_awayCompletionHom_eq_algebraMap I f
      (by rw [awayCompletionHom_eq_algebraMap]; exact hF)
  have hFsq : ((e : S →+* T).comp (algebraMap (awayCompletion I f) S)).comp
      (algebraMap R (awayCompletion I f)) = algebraMap R T := by
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    exact e.toAlgHom.comp_algebraMap
  have hGsq : (algebraMap (awayCompletion I f) T).comp (algebraMap R (awayCompletion I f)) =
      algebraMap R T := (IsScalarTower.algebraMap_eq R (awayCompletion I f) T).symm
  have key : (e : S →+* T).comp (algebraMap (awayCompletion I f) S) =
      algebraMap (awayCompletion I f) T := by
    refine awayCompletion_hom_ext' I f hI (hsq _ hFsq) (hsq _ hGsq) ?_
    rw [awayCompletionHom_eq_algebraMap, hFsq, hGsq]
  exact RingHom.congr_fun key x

/-- **An `R`-algebra equivalence between `R{1/f}`-algebras, read over `R{1/f}`.** The underlying
equivalence of rings is unchanged; only the scalars are enlarged, which
`FormalSpectrum.algEquiv_commutes_awayCompletion` licenses. -/
def awayCompletionAlgEquiv (hI : I.FG) (e : S ≃ₐ[R] T) : S ≃ₐ[awayCompletion I f] T :=
  AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (algEquiv_commutes_awayCompletion I f hI e)

@[simp]
theorem awayCompletionAlgEquiv_apply (hI : I.FG) (e : S ≃ₐ[R] T) (x : S) :
    awayCompletionAlgEquiv I f hI e x = e x := rfl

@[simp]
theorem awayCompletionAlgEquiv_symm_apply (hI : I.FG) (e : S ≃ₐ[R] T) (y : T) :
    (awayCompletionAlgEquiv I f hI e).symm y = e.symm y := rfl

end Linearity

/-!
### The chart transitions
-/

section Chart

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
variable [Algebra (awayCompletion I f) A] [Algebra (awayCompletion I f) A']
variable [IsScalarTower R (awayCompletion I f) A] [IsScalarTower R (awayCompletion I f) A']

/-- **The away completion of a chart is complete for the extension of `I`.** It is complete for
its own ideal of definition (`FormalSpectrum.isAdicRing_awayCompletionIdeal`,
`FormalSchemes.BasicOpenChart`), and that ideal is `I·A{1/s}^`
(`FormalSpectrum.map_algebraMap_awayCompletion_eq`). -/
theorem isAdicComplete_map_algebraMap_awayCompletion (hI : I.FG) (s : A) :
    IsAdicComplete (I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) s)))
      (awayCompletion (I.map (algebraMap R A)) s) := by
  rw [map_algebraMap_awayCompletion_eq]
  exact (isAdicRing_awayCompletionIdeal _ _ (hI.map _)).toIsAdicComplete

/-- **The chart transitions of a presentation over `(R, I)` are linear over `R{1/f}`** as soon as
the chart algebras are. This is the shape the transitions `τ` and the double-overlap data `σ` of
an affine-charted presentation actually have — an `R`-algebra equivalence
`A{1/s}^ ≃ₐ[R] A'{1/s'}^` between away completions of two chart algebras — so one declaration
covers both. -/
def awayCompletionChartAlgEquivBase (hI : I.FG) {s : A} {s' : A'}
    (e : awayCompletion (I.map (algebraMap R A)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A')) s') :
    awayCompletion (I.map (algebraMap R A)) s ≃ₐ[awayCompletion I f]
      awayCompletion (I.map (algebraMap R A')) s' :=
  letI := isAdicComplete_map_algebraMap_awayCompletion I hI s'
  awayCompletionAlgEquiv I f hI e

@[simp]
theorem awayCompletionChartAlgEquivBase_apply (hI : I.FG) {s : A} {s' : A'}
    (e : awayCompletion (I.map (algebraMap R A)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A')) s')
    (x : awayCompletion (I.map (algebraMap R A)) s) :
    awayCompletionChartAlgEquivBase I f hI e x = e x := rfl

@[simp]
theorem awayCompletionChartAlgEquivBase_symm_apply (hI : I.FG) {s : A} {s' : A'}
    (e : awayCompletion (I.map (algebraMap R A)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A')) s')
    (y : awayCompletion (I.map (algebraMap R A')) s') :
    (awayCompletionChartAlgEquivBase I f hI e).symm y = e.symm y := rfl

end Chart

/-!
### The structural map of the away base change is the lift
-/

section BaseChange

variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}

/-- **The base element is a unit in the away completion of a chart at its own image.** `f` reaches
`A{1/(f·A)}^` through `A_{f·A}`, where it is the away element itself, so
`IsLocalization.Away.algebraMap_isUnit` gives the unit downstairs and `IsUnit.map` carries it up
the completion map. It is the completion-level form of
`FormalSpectrum.isUnit_algebraMap_awayLocBase` (`FormalSchemes.AwayBaseChangeTopFiniteType`), and
it is what the universal property below is applied at.

It is stated here, where the theorem below needs the unit as a *term* in its own statement, rather
than beside the rest of the `awayCompletion` API in `FormalSchemes.BasicOpenChart`, whose reverse
closure is **433**: the move down rebuilds all of those, which is the price to pay once a second
module asks for the lemma and not before — this tree's standing disposition for a general statement
with one call site. -/
theorem isUnit_algebraMap_awayCompletionBase :
    IsUnit (algebraMap R (awayCompletion L (algebraMap R A f)) f) := by
  rw [IsScalarTower.algebraMap_apply R (Localization.Away (algebraMap R A f))
    (awayCompletion L (algebraMap R A f))]
  exact (isUnit_algebraMap_awayLocBase (A := A) f).map _

/-- **The structural map of the away base change is the lift the universal property produces.**
`FormalSpectrum.awayBaseHom` (`FormalSchemes.AwayBaseChangeTopFiniteType`) transports the
localization map `R_f → A_{f·A}` up the completions; `FormalSpectrum.awayCompletionLift` produces a
map into any complete `R`-algebra in which `f` is inverted. At `A{1/(f·A)}^` both apply, and they
agree — so the `R{1/f}`-algebra structure `FormalSpectrum.awayBaseAlgebra` is `RingHom.toAlgebra`
of the lift, which is a `congrArg` away and is not restated here.

The proof is `FormalSpectrum.eq_awayCompletionLift` and nothing else. Its only hypothesis is that
the map be one under `R`, which `FormalSpectrum.awayBaseHom_comp_algebraMap` already proves;
`FormalSpectrum.awayCompletionHom_eq_algebraMap` matches the two spellings of `R → R{1/f}`.
Continuity is not a hypothesis of either side — over a basic open it is free, which is the finding
recorded above.

The `letI` supplies what `FormalSpectrum.awayCompletionLift` needs of its target and is unavoidable
for the reason it is in `FormalSpectrum.isScalarTower_awayCompletionLift`: the instance depends on
the proof arguments `hI` and `hL`. It is
`FormalSpectrum.isAdicComplete_map_algebraMap_awayCompletion` at `algebraMap R A f`, read along
`hL`. Being a `Prop`, which instance a caller supplies does not matter. -/
theorem awayBaseHom_eq_awayCompletionLift (hI : I.FG) (hL : I.map (algebraMap R A) = L) :
    letI : IsAdicComplete (I.map (algebraMap R (awayCompletion L (algebraMap R A f))))
        (awayCompletion L (algebraMap R A f)) :=
      hL ▸ isAdicComplete_map_algebraMap_awayCompletion I hI (algebraMap R A f)
    awayBaseHom f hI hL =
      awayCompletionLift I f (isUnit_algebraMap_awayCompletionBase (L := L) f) := by
  letI : IsAdicComplete (I.map (algebraMap R (awayCompletion L (algebraMap R A f))))
      (awayCompletion L (algebraMap R A f)) :=
    hL ▸ isAdicComplete_map_algebraMap_awayCompletion I hI (algebraMap R A f)
  refine eq_awayCompletionLift I f hI _ ?_
  rw [awayCompletionHom_eq_algebraMap]
  exact awayBaseHom_comp_algebraMap f hI hL

end BaseChange

/-!
### The nested chart identification at a containment of basic opens
-/

section NestedOfLe

variable {A : Type u} [CommRing A] (J : Ideal A) (f g : A)

/-- **The ideal-convention bridge, twice.** The extension of `J` to the chart-local presentation
`A{1/f}{1/ĝ}` is that ring's own ideal of definition: extend along `A → A{1/f}` and then along
`A{1/f} → A{1/f}{1/ĝ}`, and `FormalSpectrum.awayCompletionIdeal_eq_map_algebraMap`
(`FormalSchemes.BasicOpenChart`) identifies each step. -/
theorem map_algebraMap_awayCompletionChart :
    J.map (algebraMap A (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g))) =
      awayCompletionIdeal (awayCompletionIdeal J f) (awayCompletionHom J f g) := by
  rw [IsScalarTower.algebraMap_eq A (awayCompletion J f)
      (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)), ← Ideal.map_map,
    awayCompletionIdeal_eq_map_algebraMap, awayCompletionIdeal_eq_map_algebraMap]

/-- `A{1/g}` is `J·A{1/g}`-adically complete. -/
theorem isAdicComplete_awayCompletion_self (hJ : J.FG) :
    IsAdicComplete (J.map (algebraMap A (awayCompletion J g))) (awayCompletion J g) := by
  rw [awayCompletionIdeal_eq_map_algebraMap]
  exact (isAdicRing_awayCompletionIdeal J g hJ).toIsAdicComplete

/-- `A{1/f}{1/ĝ}` is `J·A{1/f}{1/ĝ}`-adically complete. -/
theorem isAdicComplete_awayCompletionChart (hJ : J.FG) :
    IsAdicComplete (J.map (algebraMap A (awayCompletion (awayCompletionIdeal J f)
        (awayCompletionHom J f g))))
      (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) := by
  rw [map_algebraMap_awayCompletionChart]
  exact (isAdicRing_awayCompletionIdeal (awayCompletionIdeal J f) (awayCompletionHom J f g)
    (awayCompletionIdeal_fg J f hJ)).toIsAdicComplete

/-- **`g` is inverted in the chart-local presentation**, which is what lets the universal property
of `A{1/g}` produce the forward map. It is inverted there by construction: its image is the away
element of the second localization. -/
theorem isUnit_algebraMap_awayCompletionChart (hJ : J.FG) :
    IsUnit (algebraMap A (awayCompletion (awayCompletionIdeal J f)
      (awayCompletionHom J f g)) g) := by
  have hu : IsUnit (awayCompletionHom (awayCompletionIdeal J f) (awayCompletionHom J f g)
      (awayCompletionHom J f g)) :=
    isUnit_awayCompletionHom_of_basicOpen_le (awayCompletionIdeal J f)
      (awayCompletionHom J f g) (awayCompletionHom J f g) (awayCompletionIdeal_fg J f hJ) le_rfl
  rw [awayCompletionHom_eq_algebraMap] at hu
  rw [IsScalarTower.algebraMap_apply A (awayCompletion J f)
    (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)),
    ← awayCompletionHom_eq_algebraMap]
  exact hu

/-- The structure map of the chart-local presentation, factored through the chart. -/
theorem algebraMap_awayCompletionChart_eq :
    algebraMap A (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) =
      (awayCompletionHom (awayCompletionIdeal J f) (awayCompletionHom J f g)).comp
        (awayCompletionHom J f) :=
  (IsScalarTower.algebraMap_eq A (awayCompletion J f)
      (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g))).trans
    (congrArg₂ RingHom.comp
      (awayCompletionHom_eq_algebraMap (awayCompletionIdeal J f) (awayCompletionHom J f g)).symm
      (awayCompletionHom_eq_algebraMap J f).symm)

/-- **The forward map `A{1/g} ⟶ A{1/f}{1/ĝ}`**, by the universal property of `A{1/g}`: the target
is complete and `g` is inverted in it. **No relation between `f` and `g` is used.** -/
def awayCompletionChartHomOfLe (hJ : J.FG) :
    awayCompletion J g →+*
      awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g) :=
  haveI := isAdicComplete_awayCompletionChart J f g hJ
  awayCompletionLift J g (isUnit_algebraMap_awayCompletionChart J f g hJ)

/-- The forward map is a map under `A`. -/
theorem awayCompletionChartHomOfLe_comp_awayCompletionHom (hJ : J.FG) :
    (awayCompletionChartHomOfLe J f g hJ).comp (awayCompletionHom J g) =
      algebraMap A (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) :=
  haveI := isAdicComplete_awayCompletionChart J f g hJ
  awayCompletionLift_comp_awayCompletionHom J g (isUnit_algebraMap_awayCompletionChart J f g hJ)

/-- **The `A{1/f}`-algebra structure the containment supplies on `A{1/g}`.** This is the only place
`D(g) ≤ D(f)` is used, and it is used only through `FormalSpectrum.awayCompletionRestrict`
(`FormalSchemes.AwayCompletionRestrict`), whose whole point is that it is keyed on the containment
and not on a unit in the uncompleted localization. -/
abbrev awayCompletionRestrictAlgebra (hJ : J.FG) (hle : basicOpen J g ≤ basicOpen J f) :
    Algebra (awayCompletion J f) (awayCompletion J g) :=
  (awayCompletionRestrict J f g hJ hle).toAlgebra

/-- **The backward map `A{1/f}{1/ĝ} ⟶ A{1/g}`**, by the universal property of the *chart-local*
presentation over its own base `A{1/f}`: `A{1/g}` is an `A{1/f}`-algebra by the restriction, it is
complete for the ideal that restriction carries across
(`FormalSpectrum.map_awayCompletionRestrict`), and `ĝ` goes to `g`, a unit there. -/
def awayCompletionChartInvOfLe (hJ : J.FG) (hle : basicOpen J g ≤ basicOpen J f) :
    awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g) →+* awayCompletion J g :=
  letI := awayCompletionRestrictAlgebra J f g hJ hle
  haveI : IsAdicComplete ((awayCompletionIdeal J f).map
      (algebraMap (awayCompletion J f) (awayCompletion J g))) (awayCompletion J g) := by
    rw [RingHom.algebraMap_toAlgebra, map_awayCompletionRestrict]
    exact (AdicCompletion.isAdicRing_map _ (hJ.map _)).toIsAdicComplete
  haveI hu : IsUnit (algebraMap (awayCompletion J f) (awayCompletion J g)
      (awayCompletionHom J f g)) := by
    rw [RingHom.algebraMap_toAlgebra, awayCompletionRestrict_awayCompletionHom]
    exact isUnit_awayCompletionHom_of_basicOpen_le J g g hJ le_rfl
  awayCompletionLift (awayCompletionIdeal J f) (awayCompletionHom J f g) hu

/-- The backward map is a map under `A{1/f}`: precomposed with the structural map of the
chart-local presentation it is the restriction itself. -/
theorem awayCompletionChartInvOfLe_comp_awayCompletionHom (hJ : J.FG)
    (hle : basicOpen J g ≤ basicOpen J f) :
    (awayCompletionChartInvOfLe J f g hJ hle).comp
        (awayCompletionHom (awayCompletionIdeal J f) (awayCompletionHom J f g)) =
      awayCompletionRestrict J f g hJ hle := by
  letI := awayCompletionRestrictAlgebra J f g hJ hle
  haveI : IsAdicComplete ((awayCompletionIdeal J f).map
      (algebraMap (awayCompletion J f) (awayCompletion J g))) (awayCompletion J g) := by
    rw [RingHom.algebraMap_toAlgebra, map_awayCompletionRestrict]
    exact (AdicCompletion.isAdicRing_map _ (hJ.map _)).toIsAdicComplete
  haveI hu : IsUnit (algebraMap (awayCompletion J f) (awayCompletion J g)
      (awayCompletionHom J f g)) := by
    rw [RingHom.algebraMap_toAlgebra, awayCompletionRestrict_awayCompletionHom]
    exact isUnit_awayCompletionHom_of_basicOpen_le J g g hJ le_rfl
  have h := awayCompletionLift_comp_awayCompletionHom
    (awayCompletionIdeal J f) (awayCompletionHom J f g) hu
  rw [RingHom.algebraMap_toAlgebra] at h
  exact h

/-- **The forward map is a map under `A{1/f}` as well**, not merely under `A`: both sides are maps
out of `A{1/f}` under `A` into a complete target, so
`FormalSpectrum.awayCompletion_hom_ext'` identifies them. This is what makes the second composite
below an identity. -/
theorem awayCompletionChartHomOfLe_comp_awayCompletionRestrict (hJ : J.FG)
    (hle : basicOpen J g ≤ basicOpen J f) :
    (awayCompletionChartHomOfLe J f g hJ).comp (awayCompletionRestrict J f g hJ hle) =
      algebraMap (awayCompletion J f)
        (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) := by
  haveI := isAdicComplete_awayCompletionChart J f g hJ
  have hsqF : ((awayCompletionChartHomOfLe J f g hJ).comp
      (awayCompletionRestrict J f g hJ hle)).comp (awayCompletionHom J f) =
      algebraMap A (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) := by
    rw [RingHom.comp_assoc, awayCompletionRestrict_comp_awayCompletionHom,
      awayCompletionChartHomOfLe_comp_awayCompletionHom]
  have hsqG : (algebraMap (awayCompletion J f)
        (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g))).comp
      (awayCompletionHom J f) =
      algebraMap A (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) :=
    (congrArg (algebraMap (awayCompletion J f)
          (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g))).comp
        (awayCompletionHom_eq_algebraMap J f)).trans
      (IsScalarTower.algebraMap_eq A (awayCompletion J f)
        (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g))).symm
  exact awayCompletion_hom_ext'
    (L := J.map (algebraMap A (awayCompletion (awayCompletionIdeal J f)
      (awayCompletionHom J f g)))) J f hJ
    (le_comap_of_comp_awayCompletionHom_eq_algebraMap J f hsqF)
    (le_comap_of_comp_awayCompletionHom_eq_algebraMap J f hsqG)
    (hsqF.trans hsqG.symm)

/-- **First composite**: the backward map undoes the forward one, by rigidity at `A{1/g}`. -/
theorem awayCompletionChartInvOfLe_comp_homOfLe (hJ : J.FG)
    (hle : basicOpen J g ≤ basicOpen J f) :
    (awayCompletionChartInvOfLe J f g hJ hle).comp (awayCompletionChartHomOfLe J f g hJ) =
      RingHom.id (awayCompletion J g) := by
  haveI := isAdicComplete_awayCompletion_self J g hJ
  have hsqF : ((awayCompletionChartInvOfLe J f g hJ hle).comp
      (awayCompletionChartHomOfLe J f g hJ)).comp (awayCompletionHom J g) =
      algebraMap A (awayCompletion J g) := by
    rw [RingHom.comp_assoc, awayCompletionChartHomOfLe_comp_awayCompletionHom,
      algebraMap_awayCompletionChart_eq, ← RingHom.comp_assoc,
      awayCompletionChartInvOfLe_comp_awayCompletionHom,
      awayCompletionRestrict_comp_awayCompletionHom, awayCompletionHom_eq_algebraMap]
  have hsqG : (RingHom.id (awayCompletion J g)).comp (awayCompletionHom J g) =
      algebraMap A (awayCompletion J g) := by
    rw [RingHom.id_comp, awayCompletionHom_eq_algebraMap]
  exact awayCompletion_hom_ext' (L := J.map (algebraMap A (awayCompletion J g))) J g hJ
    (le_comap_of_comp_awayCompletionHom_eq_algebraMap J g hsqF)
    (le_comap_of_comp_awayCompletionHom_eq_algebraMap J g hsqG)
    (hsqF.trans hsqG.symm)

/-- **Second composite**: the forward map undoes the backward one, by rigidity at the chart-local
presentation over `A{1/f}`. -/
theorem awayCompletionChartHomOfLe_comp_invOfLe (hJ : J.FG)
    (hle : basicOpen J g ≤ basicOpen J f) :
    (awayCompletionChartHomOfLe J f g hJ).comp (awayCompletionChartInvOfLe J f g hJ hle) =
      RingHom.id (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) := by
  haveI : IsAdicComplete ((awayCompletionIdeal J f).map (algebraMap (awayCompletion J f)
      (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g))))
      (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) := by
    rw [← awayCompletionHom_eq_algebraMap, map_awayCompletionHom]
    exact (AdicCompletion.isAdicRing_map _
      ((awayCompletionIdeal_fg J f hJ).map _)).toIsAdicComplete
  have hsqF : ((awayCompletionChartHomOfLe J f g hJ).comp
      (awayCompletionChartInvOfLe J f g hJ hle)).comp
      (awayCompletionHom (awayCompletionIdeal J f) (awayCompletionHom J f g)) =
      algebraMap (awayCompletion J f)
        (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) := by
    rw [RingHom.comp_assoc, awayCompletionChartInvOfLe_comp_awayCompletionHom,
      awayCompletionChartHomOfLe_comp_awayCompletionRestrict]
  have hsqG : (RingHom.id (awayCompletion (awayCompletionIdeal J f)
        (awayCompletionHom J f g))).comp
      (awayCompletionHom (awayCompletionIdeal J f) (awayCompletionHom J f g)) =
      algebraMap (awayCompletion J f)
        (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) :=
    (RingHom.id_comp _).trans (awayCompletionHom_eq_algebraMap _ _)
  exact awayCompletion_hom_ext'
    (L := (awayCompletionIdeal J f).map (algebraMap (awayCompletion J f)
      (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g))))
    (awayCompletionIdeal J f) (awayCompletionHom J f g) (awayCompletionIdeal_fg J f hJ)
    (le_comap_of_comp_awayCompletionHom_eq_algebraMap _ _ hsqF)
    (le_comap_of_comp_awayCompletionHom_eq_algebraMap _ _ hsqG)
    (hsqF.trans hsqG.symm)

/-- **The nested chart identification, keyed on the containment.** `A{1/g} ≃+* A{1/f}{1/ĝ}` for
`D(g) ≤ D(f)` in `Spf (A, J)`.

`FormalSpectrum.awayCompletionChartEquiv` (`FormalSchemes.AwayCompletionInterchange`) is the same
isomorphism under `IsUnit (algebraMap A (Localization.Away g) f)` — a statement in the
**uncompleted** localization, which is the `Spec A` containment and is strictly stronger than this
one. `FormalSchemes.AwayCompletionRestrict` opens by saying so, and the separation is witnessed at
`A = ℤ`, `J = (2)`, `f = 3`, `g = 5`.

Nothing here reproves that route. Both maps come from
`FormalSpectrum.awayCompletionLift` — the universal property of a completed localization, applied
once at `A{1/g}` over `A` and once at `A{1/f}{1/ĝ}` over `A{1/f}` — and both composites are
identities by `FormalSpectrum.awayCompletion_hom_ext'`. What the containment supplies, and all it
supplies, is the `A{1/f}`-algebra structure on `A{1/g}`: the ring map
`FormalSpectrum.awayCompletionRestrict`, together with
`FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le`, which is exactly the statement that `f`
is invertible in the **completion** `A{1/g}` even though it need not be in
`Localization.Away g`. -/
def awayCompletionChartEquivOfLe (hJ : J.FG) (hle : basicOpen J g ≤ basicOpen J f) :
    awayCompletion J g ≃+*
      awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g) :=
  RingEquiv.ofRingHom (awayCompletionChartHomOfLe J f g hJ)
    (awayCompletionChartInvOfLe J f g hJ hle)
    (awayCompletionChartHomOfLe_comp_invOfLe J f g hJ hle)
    (awayCompletionChartInvOfLe_comp_homOfLe J f g hJ hle)

/-- **The identification fixes `A`**, which is what the `R`-algebra upgrade below needs. -/
theorem awayCompletionChartEquivOfLe_algebraMap (hJ : J.FG)
    (hle : basicOpen J g ≤ basicOpen J f) (a : A) :
    awayCompletionChartEquivOfLe J f g hJ hle (algebraMap A (awayCompletion J g) a) =
      algebraMap A (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) a := by
  have h := RingHom.congr_fun (awayCompletionChartHomOfLe_comp_awayCompletionHom J f g hJ) a
  rw [RingHom.comp_apply, awayCompletionHom_eq_algebraMap J g] at h
  exact h

end NestedOfLe

section NestedOfLeBase

variable {B : Type u} [CommRing B] [Algebra R B]

/-- **The `R`-algebra form** of `FormalSpectrum.awayCompletionChartEquivOfLe`: it fixes `B`, hence
a fortiori the image of `R`. The upgrade is the one
`FormalSpectrum.awayCompletionChartAlgEquiv` (`FormalSchemes.AwayCompletionNested`) performs at
the stronger hypothesis. -/
def awayCompletionChartAlgEquivOfLe (hI : I.FG) (x y : B)
    (hle : basicOpen (I.map (algebraMap R B)) y ≤ basicOpen (I.map (algebraMap R B)) x) :
    awayCompletion (I.map (algebraMap R B)) y ≃ₐ[R]
      awayCompletion (awayCompletionIdeal (I.map (algebraMap R B)) x)
        (awayCompletionHom (I.map (algebraMap R B)) x y) :=
  AlgEquiv.ofRingEquiv
    (f := awayCompletionChartEquivOfLe (I.map (algebraMap R B)) x y (hI.map _) hle)
    fun r => by
      rw [IsScalarTower.algebraMap_apply R B (awayCompletion (I.map (algebraMap R B)) y),
        awayCompletionChartEquivOfLe_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **`FormalSpectrum.awayCompletionNestedAlgEquiv` at a containment of basic opens**, in the ideal
convention an affine-charted datum spells its charts with. Same type, same conclusion; the
hypothesis `IsUnit (algebraMap B (Localization.Away y) x)` is replaced by
`D(y) ≤ D(x)` in `Spf (B, I·B)`, which is strictly weaker.

This is the statement issue 2148's refined overlap waits on: the refined presentation of a
cross-chart overlap is `B{1/(h·e)}` with `D(h·e) ≤ D(g_ij)` given by
`FormalSpectrum.basicOpen_refinedOverlapElt_le` (`FormalSchemes.RefinedOverlapRestrict`), and no
divisibility or uncompleted unit is available there. -/
def awayCompletionNestedAlgEquivOfLe (hI : I.FG) (x y : B)
    (hle : basicOpen (I.map (algebraMap R B)) y ≤ basicOpen (I.map (algebraMap R B)) x) :
    awayCompletion (I.map (algebraMap R B)) y ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (awayCompletion (I.map (algebraMap R B)) x)))
        (awayCompletionHom (I.map (algebraMap R B)) x y) :=
  (awayCompletionChartAlgEquivOfLe I hI x y hle).trans
    (AdicCompletion.congrIdealₐ R
      (congrArg (Ideal.map (algebraMap (awayCompletion (I.map (algebraMap R B)) x)
          (Localization.Away (awayCompletionHom (I.map (algebraMap R B)) x y))))
        (map_algebraMap_awayCompletion_eq I x).symm))

end NestedOfLeBase

end FormalSpectrum

end
