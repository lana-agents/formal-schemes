import FormalSchemes.AwayCompletionRestrictUnique
import FormalSchemes.AwayTopFiniteType

set_option linter.style.header false

/-!
# `R{1/f}` as a base ring: its universal property, and what becomes `R{1/f}`-linear

`FormalSpectrum.awayCompletion I f` — the completed localization `R{1/f}` — is built in
`FormalSchemes.BasicOpenChart` as the ring of the basic-open chart of `Spf (R, I)`, and every
statement about it on this tree so far reads it as an *object over* `(R, I)`. This file reads it
the other way round, as a **base ring in its own right**: it is the affine base a morphism
`X ⟶ Spf (R, I)` acquires when it factors through the basic open `D(f)`, and the question this
file answers is what of an affine-chart presentation of `X` over `(R, I)` survives that change of
base.

Three things do — an `R{1/f}`-algebra structure on each chart algebra, the ideal it induces
there, and the `R{1/f}`-linearity of the transitions between charts — and they are the three
outputs below. Nothing here is about formal schemes; it is all commutative algebra, which is the
point: the geometry contributes only the hypothesis that `f` is invertible on each chart.

## The universal property

`R{1/f}` is the `I`-adic completion of `R_f`, so a ring map out of it into an `L`-adically complete
target is determined by, and can be built from, a ring map out of `R_f`; and a ring map out of
`R_f` is a ring map out of `R` inverting `f`. Putting the two together:

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
site in this file. For a general adic base `(R', I')` the question is a real one and this file
does not settle it; for `(R', I') = (R{1/f}, I·R{1/f})` it is empty.

## The two outputs that follow

* **The induced ideals do not move.** `Ideal.map_algebraMap_family_eq_of_tower` says that for a
  family `A` of `R{1/f}`-algebras over `R`, the family `fun i => I'·A i` computed over the new
  base is *equal*, as a function, to `fun i => I·A i` computed over the old one. It is
  `Ideal.map_algebraMap_of_tower` (`FormalSchemes.AwayTopFiniteType`) under a `funext`, and the
  function-level spelling is not decoration — see that lemma's docstring for the three spellings
  and which one a consumer can actually use.
* **`R`-linear becomes `R{1/f}`-linear, for free.** `FormalSpectrum.awayCompletionAlgEquiv`
  upgrades an `R`-algebra equivalence between two complete `R{1/f}`-algebras to an
  `R{1/f}`-algebra equivalence, with no hypothesis beyond `I.FG` and completeness of the target
  — the two composites `R{1/f} → S → T` and `R{1/f} → T` are then maps under `R` into a complete
  target, so rigidity identifies them. `FormalSpectrum.awayCompletionChartAlgEquivBase` is the
  same statement at the shape the chart transitions actually have,
  `A{1/s}^ ≃ₐ[R] A'{1/s'}^`, where that completeness is automatic.

## Main definitions

* `FormalSpectrum.awayLocLift`, `FormalSpectrum.awayLocLiftₐ`: the localization half of the lift.
* `FormalSpectrum.awayCompletionLift`: the universal property of `R{1/f}`.
* `FormalSpectrum.awayCompletionAlgEquiv`, `FormalSpectrum.awayCompletionChartAlgEquivBase`: an
  `R`-algebra equivalence read over the base `R{1/f}`.

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

## What is *not* proved here

**The general affine base is untouched.** Nothing below produces an `R'`-algebra structure on a
chart from a factorisation through an arbitrary `Spf (R', I')`; the input is always an inverted
element of `R`, and `FormalSpectrum.awayCompletionLift` is the only construction offered. In
particular the question whether the map `R' →+* A` supplied by `FormalSpectrum.globalSectionsMap`
(`FormalSchemes.SpfGamma`) is continuous is neither answered nor answerable here.

**No datum is base-changed.** `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData`
(`FormalSchemes.GeneralFibreProductExposeXAlgebraData`) is not used below and that module is not
imported here; assembling these three outputs into a datum over `R{1/f}` needs a congruence for
that constructor along the ideal-family equality, which is a separate statement and is not
here. Nothing here says anything about `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`,
fibre products or diagonals.

**The `σ`-cocycle and the `τ`-symmetry identities are not restated over `R{1/f}`.**
`FormalSpectrum.awayCompletionAlgEquiv` does not change the underlying function of an equivalence
(`FormalSpectrum.awayCompletionAlgEquiv_apply` is `rfl`), so any identity between composites of
transitions transports along it by `AlgEquiv.ext`; but that transport is performed where the
identities live, not here.

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
goes through. So the equation a consumer needs is one it can `generalize` into that last shape,
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

/-- **The localization half of the lift**: the ring map `R_f →+* A` attached to an `R`-algebra `A`
in which the image of `f` is a unit, by the universal property of `Localization.Away f`. -/
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
`AdicCompletion.extendRingHom` (`FormalSchemes.AdicExtend`) consumes: it carries `(I·R_f)^m` into
`(I·A)^m` for every `m`, because it is a map of `R`-algebras. -/
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
argument with the target specialised to another completed localization of the *same* ring `R`;
this one takes an arbitrary `R`-algebra and lands in `I·A` rather than in a second ideal of
definition, so neither is an instance of the other. -/
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

end FormalSpectrum

end
