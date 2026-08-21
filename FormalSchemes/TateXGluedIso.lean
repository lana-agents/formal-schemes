import FormalSchemes.GlueMorphisms
import FormalSchemes.TateCurveExposeXDatum
import FormalSchemes.TateChartTransitionInvAlgEq
import FormalSchemes.TateOverlapSummandAffine

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The glued object of the Tate `X`-expose datum is the Tate curve model

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, and write
`A = R{x, y}/(x·y − q)` for the coordinate ring of the formal Tate annulus, `J = I·A`, and
`w = x + y`. Two presentations of the Tate curve `𝔈_q` are on `master`:

* the **model** `tateCurveModel` (`FormalSchemes.TateCurveModel`), glued from two copies of
  `Spf A` along the coproduct overlap `Spf A{1/x}^ ⨿ Spf A{1/y}^` by the 𝔾m-inversion;
* the **datum** `tateCurveExposeXDatum` (683, `FormalSchemes.TateCurveExposeXDatum`), an
  `AffineChartedFibreDatumX` whose two charts are `Spf A`, whose overlap is the *single* basic open
  `Spf A{1/w}^` (601a), and whose transition is the `R`-algebra map `tateOverlapTransitionAlg`
  of 672.

683 deliberately did **not** claim that the datum's glued object `xGlued` is `𝔈_q`. This file
proves it: `tateXGluedIso : xGlued ≅ tateCurveModel`. It is brick 4a2 of 601's programme
(issue 704) and, with the fibre-product half (705), it is what lets the general `IsSeparated`
vocabulary of §10.15 be applied to the Tate curve.

## The route

The two glue data live on the same index type `ULift Bool`, so the comparison is componentwise: a
chart comparison `tateChartCompIso` and an overlap comparison `tateOverlapCompIso`, subject to two
laws — one for the overlap immersions (`tateOverlapCompIso_hom_fac`) and one for the transitions
(`tateOverlapCompIso_transition_fac`) — after which `FormalScheme.GlueData.glueMorphisms` produces
a morphism in each direction and `hom_ext` proves they are inverse. (A *general* "isomorphic glue
data have isomorphic glued objects" lemma is not needed and should not be attempted: its statement
requires an equivalence of the two index types, which forces object-level dependent transport that
`subst` cannot discharge. None of that friction exists here.)

The chart law is bookkeeping. **The transition law is the mathematical content**, and it is where
671, 672, 644 and 703 meet: reduced summandwise by `coprod.hom_ext`, it becomes the two affine
identities

```
projX ∘ T = ι⁻¹ ∘ projY ,      projY ∘ T = ι ∘ projX ,
```

where `T = tateOverlapTransitionAlg` is the datum's transition, `projX`/`projY` are the two
projections of the splitting `A{1/w}^ ≃ₐ[R] A{1/x}^ × A{1/y}^` (644) and `ι` is the 𝔾m-inversion
chart transition. Both come straight from 672's computation rule `tateOverlapTransitionAlg_apply`,
which exhibits `T` as the twisted swap `(a, b) ↦ (ι⁻¹ b, ι a)`. This is the point at which the
*direction* of the datum's `τ` is finally pinned against the geometry, and it comes out as 672
predicted — no swap was needed.

## Main definitions and results

* `AlgebraicGeometry.tateOverlapTransitionSpf`: `Spf` of 672's transition, in the model's ideal
  convention, with `tateOverlapTransitionSpf_comp_self` (it is an involution).
* `AlgebraicGeometry.annulusOverlapSummandX_comp_transitionSpf` and its `y` analogue: **the affine
  crux** — the transition carries the `x`-summand of the overlap to the `y`-summand by the
  𝔾m-inversion.
* `AlgebraicGeometry.tateChartCompIso`, `tateOverlapCompIso`, and their two laws
  `tateOverlapCompIso_hom_fac`, `tateOverlapCompIso_transition_fac`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.xGlueData_V` / `_f` / `_t` / `_glue_raw`: the shape of
  a general affine-charted `X` glue datum off the diagonal, stated **generically in the datum** so
  that instantiating them never unfolds `ofAlgebraData`.
* `AlgebraicGeometry.tateXGluedHom`, `tateXGluedInv`, `tateXGluedIsoLRS` and the headline
  `AlgebraicGeometry.tateXGluedIso : xGlued ≅ 𝔈_q`, with the characterisations
  `ι_tateXGluedHom` / `ι_tateXGluedInv` that brick 4c will consume.

## Implementation notes: two spellings, and why they must be kept apart

`CategoryTheory.GlueData.ofGlueData'` puts a `dite` in the *type* of `f`, so every statement about
a glue datum off the diagonal carries the transport `dif_neg` produces, and the index type appears
in two guises: the datum's own `D.J` and the glue datum's `D.xFormalGlueData.….J`. They are
definitionally equal, but a statement that mixes them is only type-correct *after unfolding a
semireducible definition*, and then two things fail silently:

* `simp only [.., dif_neg hij]` reports **"this simp argument is unused"** — the hypothesis is at
  the wrong spelling of `Eq`;
* `Category.assoc` refuses to associate, with the note *"the target expression is not type-correct
  under the `instances` transparency level"*.

The reducible `abbrev`s of this file (`tateModelIdx`, `tateXDatumIdx`, `tateXIdxToModel`,
`tateChartCompU`, …) exist to keep the spellings apart: each ascribes a term to the spelling its
neighbours use, without changing the term. Ignoring this discipline is not a matter of taste — the
first version of this file was **OOM-killed after twelve minutes**; the same content with the
ascriptions in place elaborates in **eight seconds**.

The other rule inherited from 683 and paid for again here: state generic algebra lemmas with the
conjugate **left-associated** (`(E.trans P).trans E.symm`), matching
`annulusFibreOverlapTransitionAlg`. The right-associated spelling is the same map, is `rfl`-equal,
and costs a four-minute `whnf` timeout when the elaborator has to bridge the two at the concrete
completion types.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits FormalSpectrum

universe u

namespace AlgEquiv

/-- **Conjugation, cancelled on one side.** For `E : X ≃ₐ[R] Y` and `P : Y ≃ₐ[R] Y`,
`E⁻¹ ≫ (E ≫ P ≫ E⁻¹) = P ≫ E⁻¹`. The conjugate is spelled **left-associated**, matching the
spelling `annulusFibreOverlapTransitionAlg` (683) uses: the right-associated term is the same map
but not the same term, and unifying the two at the concrete completions is what
`maxRecDepth`/`whnf` timeouts are made of. -/
theorem symm_trans_conj {R X Y : Type u} [CommSemiring R] [Semiring X] [Semiring Y]
    [Algebra R X] [Algebra R Y] (E : X ≃ₐ[R] Y) (P : Y ≃ₐ[R] Y) :
    E.symm.trans ((E.trans P).trans E.symm) = P.trans E.symm :=
  AlgEquiv.ext fun y => by simp

/-- The ring-hom form of `symm_trans_conj`, again stated generically. -/
theorem toRingHom_symm_trans_conj {R X Y : Type u} [CommSemiring R] [Semiring X] [Semiring Y]
    [Algebra R X] [Algebra R Y] (E : X ≃ₐ[R] Y) (P : Y ≃ₐ[R] Y) :
    ((E.trans P).trans E.symm).toRingHom.comp E.symm.toRingHom =
      E.symm.toRingHom.comp P.toRingHom :=
  congrArg (fun e : Y ≃ₐ[R] X => e.toRingHom) (symm_trans_conj E P)

/-- **An involution applied twice is the identity**, in the `symm`-form the datum's `τ_symm`
field produces. -/
theorem apply_apply_of_symm_eq {R X : Type u} [CommSemiring R] [Semiring X] [Algebra R X]
    (e : X ≃ₐ[R] X) (he : e.symm = e) (x : X) : e (e x) = x := by
  have h : e (e x) = e (e.symm x) := by rw [he]
  rw [h, e.apply_symm_apply]

/-- **The underlying ring hom of an involution composes with itself to the identity.** Stated
generically: the same equation checked directly at a concrete adic completion exhausts
`maxRecDepth`, whereas here the kernel sees it once at abstract types. -/
theorem toRingHom_comp_self_of_symm_eq {R X : Type u} [CommSemiring R] [Semiring X] [Algebra R X]
    (e : X ≃ₐ[R] X) (he : e.symm = e) : e.toRingHom.comp e.toRingHom = RingHom.id X :=
  RingHom.ext fun x => apply_apply_of_symm_eq e he x

end AlgEquiv

namespace FormalSpectrum

variable {R : Type u} [CommRing R]

/-- **The basic-open chart transports along an equality of ideals.** Stated generically in the two
ideals, so `subst` discharges it and no concrete completion is ever unfolded. -/
theorem spfCongrIdeal_hom_comp_basicOpenChart {A : Type u} [CommRing A] {K L : Ideal A}
    (h : K = L) (f : A) :
    (spfCongrIdeal (congrArg (Ideal.map (algebraMap A (Localization.Away f))) h)).hom ≫
        basicOpenChart L f =
      basicOpenChart K f ≫ eqToHom (congrArg locallyRingedSpaceObj h) := by
  subst h
  have hid : (spfCongrIdeal
      (congrArg (Ideal.map (algebraMap A (Localization.Away f))) (rfl : K = K))).hom =
      𝟙 _ := rfl
  rw [hid, Category.id_comp, eqToHom_refl, Category.comp_id]

/-- **An `R`-algebra isomorphism of away completions respects the ideals of definition**, in any
ideal convention presenting the base ideal as `I·S`.

`AlgebraicGeometry.awayCompletionTransition_le_comap` is stated in the `I.map (algebraMap R S)`
convention only; this transports it to an arbitrary ideal `K` known to equal `I·S`, which is what
the Tate annulus needs (`annulus_map_eq`). The transport is a `subst`. -/
theorem le_comap_algEquiv_symm_of_map_eq {S : Type u} [CommRing S] [Algebra R S] {I : Ideal R}
    {K : Ideal S} (h : I.map (algebraMap R S) = K) (f g : S)
    (e : awayCompletion K f ≃ₐ[R] awayCompletion K g) :
    awayCompletionIdeal K g ≤ (awayCompletionIdeal K f).comap e.symm.toRingHom := by
  subst h
  exact AlgebraicGeometry.awayCompletionTransition_le_comap (I := I) f g e

end FormalSpectrum

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The transition of the model's overlap, as an affine morphism -/

/-- The `R`-algebra transition of the two-chart overlap respects the ideal of definition. -/
theorem tateOverlapTransitionAlg_le_comap (hq : q ∈ I) (hI : I.FG) :
    awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (overlapX R I q + overlapY R I q)).comap
        (tateOverlapTransitionAlg R I q hq hI).toRingHom := by
  have h := FormalSpectrum.le_comap_algEquiv_symm_of_map_eq (annulus_map_eq R I q)
    (overlapX R I q + overlapY R I q) (overlapX R I q + overlapY R I q)
    (tateOverlapTransitionAlg R I q hq hI)
  rwa [tateOverlapTransitionAlg_symm] at h

/-- **The transition of the Tate two-chart overlap as a morphism of formal spectra**, in the
`annulusIdealOfDefinition` convention the model `𝔈_q` uses: `Spf` of 672's `R`-algebra
transition. -/
def tateOverlapTransitionSpf (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (overlapX R I q + overlapY R I q)) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q)) :=
  locallyRingedSpaceMap _ _ (tateOverlapTransitionAlg R I q hq hI).toRingHom
    (tateOverlapTransitionAlg_le_comap R I q hq hI)

/-- The overlap transition composed with itself is the identity ring map: it is an involution
(`tateOverlapTransitionAlg_symm`). -/
theorem tateOverlapTransitionAlg_comp_self (hq : q ∈ I) (hI : I.FG) :
    (tateOverlapTransitionAlg R I q hq hI).toRingHom.comp
        (tateOverlapTransitionAlg R I q hq hI).toRingHom = RingHom.id _ :=
  AlgEquiv.toRingHom_comp_self_of_symm_eq _ (tateOverlapTransitionAlg_symm R I q hq hI)

/-- **The overlap transition is an involution**, geometrically. -/
@[reassoc]
theorem tateOverlapTransitionSpf_comp_self (hq : q ∈ I) (hI : I.FG) :
    tateOverlapTransitionSpf R I q hq hI ≫ tateOverlapTransitionSpf R I q hq hI = 𝟙 _ := by
  rw [tateOverlapTransitionSpf, ← FormalSpectrum.locallyRingedSpaceMap_comp
    (φ := (tateOverlapTransitionAlg R I q hq hI).toRingHom)
    (ψ := (tateOverlapTransitionAlg R I q hq hI).toRingHom)
    (hIK := le_comap_comp _ _ (tateOverlapTransitionAlg_le_comap R I q hq hI)
      (tateOverlapTransitionAlg_le_comap R I q hq hI))]
  exact (FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ (RingHom.id _) _
    (Ideal.comap_id _).ge (tateOverlapTransitionAlg_comp_self R I q hq hI)).trans
    (FormalSpectrum.locallyRingedSpaceMap_id _)

/-! ### The affine crux: the transition exchanges the two summands of the overlap -/

/-- **The ring-level crux.** The first projection of the splitting, after the overlap transition,
is the inverse 𝔾m-inversion applied to the second projection: `projX ∘ T = ι⁻¹ ∘ projY`.

This is 672's `tateOverlapTransitionAlg_apply` — which exhibits `T` as the twisted swap
`(a, b) ↦ (ι⁻¹ b, ι a)` under the splitting of 644 — read on the first component. -/
theorem annulusOverlapProjX_comp_transitionAlg (hq : q ∈ I) (hI : I.FG) :
    (annulusOverlapProjX R I q hq).comp (tateOverlapTransitionAlg R I q hq hI).toRingHom =
      (annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
        (annulusOverlapProjY R I q hq) := by
  refine RingHom.ext fun s => ?_
  change ((TateAwaySplit.awaySplitEquiv R I q hq) (tateOverlapTransitionAlg R I q hq hI s)).1 =
    (annulusChartTransitionInvAlg R I q hI).symm
      ((TateAwaySplit.awaySplitEquiv R I q hq) s).2
  rw [tateOverlapTransitionAlg_apply]
  simp only [← TateAwaySplit.awaySplitAlgEquiv_toRingEquiv, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply]

/-- **The `x`-summand of the overlap is carried to the `y`-summand by the transition**, and the
identification is the 𝔾m-inversion. This is `Spf` of `annulusOverlapProjX_comp_transitionAlg`,
using 703's presentation of the summand inclusions as `Spf` of the splitting's projections. -/
@[reassoc]
theorem annulusOverlapSummandX_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapSummandX R I q hq ≫ tateOverlapTransitionSpf R I q hq hI =
      (annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapSummandY R I q hq := by
  rw [annulusOverlapSummandX, tateOverlapTransitionSpf,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := (tateOverlapTransitionAlg R I q hq hI).toRingHom)
      (ψ := annulusOverlapProjX R I q hq)
      (hIK := le_comap_comp _ _ (tateOverlapTransitionAlg_le_comap R I q hq hI)
        (le_comap_of_comp_awayCompletionHom _ _ _ _
          (annulusOverlapProjX_comp_awayCompletionHom R I q hq))),
    annulusChartTransitionInvSpf_hom_eq, annulusOverlapSummandY,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := annulusOverlapProjY R I q hq)
      (ψ := (annulusChartTransitionInvAlg R I q hI).symm.toRingHom)
      (hIK := le_comap_comp _ _
        (le_comap_of_comp_awayCompletionHom _ _ _ _
          (annulusOverlapProjY_comp_awayCompletionHom R I q hq))
        (annulusChartTransitionInvAlg_symm_le_comap R I q hI))]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (annulusOverlapProjX_comp_transitionAlg R I q hq hI)

/-- **The `y`-summand of the overlap is carried to the `x`-summand by the transition.** Deduced
from the `x`-statement and the fact that the transition is an involution, which avoids a second
continuity witness for the inversion. -/
@[reassoc]
theorem annulusOverlapSummandY_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapSummandY R I q hq ≫ tateOverlapTransitionSpf R I q hq hI =
      (annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapSummandX R I q hq := by
  refine (Iso.eq_inv_comp _).2 ?_
  rw [← Category.assoc, ← annulusOverlapSummandX_comp_transitionSpf, Category.assoc,
    tateOverlapTransitionSpf_comp_self, Category.comp_id]

/-! ### The transition matches the model's, through the overlap identification -/

/-- **The model's overlap transition, read through the affine identification of the overlap.**
Both sides are endomorphisms of `Spf A{1/x}^ ⨿ Spf A{1/y}^`; the left one is the transition of
`tateCurveGlueData'`, the right one is `Spf` of the `R`-algebra transition of 672, conjugated by
671's identification. The two summandwise obligations are the affine crux above. -/
theorem tateOverlapChartIso_transition_comm (hq : q ∈ I) (hI : I.FG) :
    (tateOverlapChartIso R I q hq hI).hom ≫
        coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
          ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl) =
      tateOverlapTransitionSpf R I q hq hI ≫ (tateOverlapChartIso R I q hq hI).hom := by
  refine (Iso.eq_inv_comp _).1 (coprod.hom_ext ?_ ?_)
  · rw [coprod.inl_desc, ← Category.assoc, coprod_inl_comp_tateOverlapChartIso_inv,
      annulusOverlapSummandX_comp_transitionSpf_assoc,
      annulusOverlapSummandY_comp_tateOverlapChartIso_hom]
  · rw [coprod.inr_desc, ← Category.assoc, coprod_inr_comp_tateOverlapChartIso_inv,
      annulusOverlapSummandY_comp_transitionSpf_assoc,
      annulusOverlapSummandX_comp_tateOverlapChartIso_hom]

/-! ### The comparison isomorphisms -/

/-- **The chart comparison**: the datum's chart `Spf (I·A)` is the model's chart `Spf A`. The two
differ only by the ideal convention (`annulus_map_eq`), and `locallyRingedSpaceObj` is a plain
function of the ideal, so this is a genuine equality of objects. -/
def tateChartCompIso : locallyRingedSpaceObj (I.map (algebraMap R (annulusAlgebra R I q))) ≅
    locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  eqToIso (congrArg locallyRingedSpaceObj (annulus_map_eq R I q))

/-- **The ideal-convention transport on the overlap chart** `Spf A{1/(x+y)}^`, the geometric
counterpart of the algebra bridge `annulusFibreChartBridgeXY` (683). -/
def tateOverlapBridgeIso :
    locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q + overlapY R I q)) ≅
      locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q)) :=
  spfCongrIdeal (congrArg (Ideal.map (algebraMap (annulusAlgebra R I q)
    (Localization.Away (overlapX R I q + overlapY R I q)))) (annulus_map_eq R I q))

/-- **The overlap comparison**: the datum's overlap `Spf A{1/(x+y)}^` is the model's overlap
`Spf A{1/x}^ ⨿ Spf A{1/y}^`, by the ideal-convention transport followed by 671's identification. -/
def tateOverlapCompIso (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q + overlapY R I q)) ≅
      (locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (overlapX R I q)) ⨿
        locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (overlapY R I q))) :=
  tateOverlapBridgeIso R I q ≪≫ tateOverlapChartIso R I q hq hI

/-- **The chart law**: the datum's overlap immersion, followed by the chart comparison, is the
overlap comparison followed by the model's overlap immersion. The content is 671's
`tateOverlapChartIso_hom_fac`; the rest is the ideal-convention transport. -/
theorem tateOverlapCompIso_hom_fac (hq : q ∈ I) (hI : I.FG) :
    basicOpenChart (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q) ≫ (tateChartCompIso R I q).hom =
      (tateOverlapCompIso R I q hq hI).hom ≫
        coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) := by
  rw [tateOverlapCompIso, Iso.trans_hom, Category.assoc, tateOverlapChartIso_hom_fac,
    tateChartCompIso, eqToIso.hom, tateOverlapBridgeIso]
  exact (FormalSpectrum.spfCongrIdeal_hom_comp_basicOpenChart (annulus_map_eq R I q) _).symm

/-- The bridged transition of the datum is the model's transition, conjugated by the algebra
bridge. Both sides are ring maps `A{1/(x+y)}^ → A{1/(x+y)}^` between the two ideal conventions;
the identity is the generic conjugation law `AlgEquiv.toRingHom_symm_trans_conj`, so no concrete
completion is unfolded. -/
theorem annulusFibreOverlapTransitionAlg_comp_bridge (hq : q ∈ I) (hI : I.FG) :
    (annulusFibreOverlapTransitionAlg R I q hq hI).symm.toRingHom.comp
        (annulusFibreChartBridgeXY R I q).symm.toRingHom =
      (annulusFibreChartBridgeXY R I q).symm.toRingHom.comp
        (tateOverlapTransitionAlg R I q hq hI).toRingHom := by
  rw [annulusFibreOverlapTransitionAlg_symm, annulusFibreOverlapTransitionAlg]
  exact AlgEquiv.toRingHom_symm_trans_conj _ _

/-- **The datum's transition is the model's, transported.** -/
theorem awayCompletionTransition_comp_tateOverlapBridgeIso (hq : q ∈ I) (hI : I.FG) :
    awayCompletionTransition (I := I) (overlapX R I q + overlapY R I q)
          (overlapX R I q + overlapY R I q) (annulusFibreOverlapTransitionAlg R I q hq hI) ≫
        (tateOverlapBridgeIso R I q).hom =
      (tateOverlapBridgeIso R I q).hom ≫ tateOverlapTransitionSpf R I q hq hI := by
  rw [awayCompletionTransition, tateOverlapBridgeIso, FormalSpectrum.spfCongrIdeal_hom_eq,
    tateOverlapTransitionSpf,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := (AdicCompletion.congrIdeal (congrArg (Ideal.map (algebraMap (annulusAlgebra R I q)
          (Localization.Away (overlapX R I q + overlapY R I q))))
          (annulus_map_eq R I q))).symm.toRingHom)
      (ψ := (annulusFibreOverlapTransitionAlg R I q hq hI).symm.toRingHom)
      (hIK := le_comap_comp _ _
        (FormalSpectrum.le_comap_congrIdeal_symm _)
        (awayCompletionTransition_le_comap (I := I) _ _
          (annulusFibreOverlapTransitionAlg R I q hq hI))),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := (tateOverlapTransitionAlg R I q hq hI).toRingHom)
      (ψ := (AdicCompletion.congrIdeal (congrArg (Ideal.map (algebraMap (annulusAlgebra R I q)
          (Localization.Away (overlapX R I q + overlapY R I q))))
          (annulus_map_eq R I q))).symm.toRingHom)
      (hIK := le_comap_comp _ _ (tateOverlapTransitionAlg_le_comap R I q hq hI)
        (FormalSpectrum.le_comap_congrIdeal_symm _))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [← AdicCompletion.congrIdealₐ_symm_toRingHom R, ← annulusFibreChartBridgeXY]
  exact annulusFibreOverlapTransitionAlg_comp_bridge R I q hq hI

/-- **The transition law**: the overlap comparison intertwines the datum's transition with the
model's. This is the mathematical content of the comparison, and it rests on the affine crux
above. -/
theorem tateOverlapCompIso_transition_fac (hq : q ∈ I) (hI : I.FG) :
    awayCompletionTransition (I := I) (overlapX R I q + overlapY R I q)
          (overlapX R I q + overlapY R I q) (annulusFibreOverlapTransitionAlg R I q hq hI) ≫
        (tateOverlapCompIso R I q hq hI).hom =
      (tateOverlapCompIso R I q hq hI).hom ≫
        coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
          ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl) := by
  rw [tateOverlapCompIso, Iso.trans_hom, ← Category.assoc,
    awayCompletionTransition_comp_tateOverlapBridgeIso]
  simp only [Category.assoc]
  rw [tateOverlapChartIso_transition_comm]


private abbrev tcOverlap : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ⨿
    locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))

private abbrev tcTransition (hI : I.FG) : tcOverlap R I q ⟶ tcOverlap R I q :=
  coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
    ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl)

variable [IsNoetherianRing R]

/-- The index type of the Tate curve model's glue datum, in the glue datum's own spelling.
Definitionally `ULift Bool`; see the implementation notes for why the spelling matters. -/
abbrev tateModelIdx (hq : q ∈ I) (hI : I.FG) : Type u :=
  (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J

private abbrev tcChartU (hq : q ∈ I) (hI : I.FG) (i : tateModelIdx R I q hq hI) :
    tcOverlap R I q ⟶ (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U i :=
  coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q)

private theorem tcm_V (hq : q ∈ I) (hI : I.FG) {i j : tateModelIdx R I q hq hI} (hij : i ≠ j) :
    (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
      tcOverlap R I q := by
  simp only [tateCurveFormalGlueData, tateCurveLRSGlueData, tateCurveGlueData',
    CategoryTheory.GlueData.ofGlueData', dif_neg (show ¬ @Eq (ULift.{u} Bool) i j from hij)]

private theorem tcm_f (hq : q ∈ I) (hI : I.FG) {i j : tateModelIdx R I q hq hI} (hij : i ≠ j)
    (h : (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
      tcOverlap R I q) :
    (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f i j =
      eqToHom h ≫ tcChartU R I q hq hI i := by
  simp only [tateCurveFormalGlueData, tateCurveLRSGlueData, tateCurveGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
    dif_neg (show ¬ @Eq (ULift.{u} Bool) i j from hij), tcChartU]

private theorem tcm_t (hq : q ∈ I) (hI : I.FG) {i j : tateModelIdx R I q hq hI} (hij : i ≠ j)
    (h : (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
      tcOverlap R I q)
    (h' : (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.V (j, i) =
      tcOverlap R I q) :
    (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.t i j =
      eqToHom h ≫ tcTransition R I q hI ≫ eqToHom h'.symm := by
  simp only [tateCurveFormalGlueData, tateCurveLRSGlueData, tateCurveGlueData',
    CategoryTheory.GlueData.ofGlueData',
    dif_neg (show ¬ @Eq (ULift.{u} Bool) i j from hij), tcTransition]

private theorem tcm_glue_raw (hq : q ∈ I) (hI : I.FG) {i j : tateModelIdx R I q hq hI}
    (hij : i ≠ j) :
    tcChartU R I q hq hI i ≫ (tateCurveFormalGlueData R I q hq hI).ι i =
      tcTransition R I q hI ≫ tcChartU R I q hq hI j ≫
        (tateCurveFormalGlueData R I q hq hI).ι j := by
  have hc := (tateCurveFormalGlueData R I q hq
    hI).toLocallyRingedSpaceGlueData.toGlueData.glue_condition i j
  rw [tcm_f R I q hq hI hij (tcm_V R I q hq hI hij),
    tcm_f R I q hq hI (Ne.symm hij) (tcm_V R I q hq hI (Ne.symm hij)),
    tcm_t R I q hq hI hij (tcm_V R I q hq hI hij) (tcm_V R I q hq hI (Ne.symm hij))] at hc
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hc
  exact ((cancel_epi (eqToHom (tcm_V R I q hq hI hij))).1 hc).symm


namespace AffineChartedFibreDatumX
section Generic
attribute [local instance] AffineChartedFibreDatum.commRing AffineChartedFibreDatum.algebra

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B] (D : AffineChartedFibreDatumX R I hI B)

/-- The index type of the `X` glue datum, in the glue datum's own spelling. -/
abbrev xIdx : Type u := D.xFormalGlueData.toLocallyRingedSpaceGlueData.J

/-- An index of the `X` glue datum, read back as an index of the datum. -/
abbrev xIdxToJ (i : D.xIdx) : D.J := i

/-- The overlap object of the `X` glue datum at an ordered pair of distinct charts. -/
abbrev xOverlapObj (i j : D.J) : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.A i))) (D.g i j))

/-- The overlap immersion of the `X` glue datum, in the glue datum's spelling. -/
abbrev xChartU (i j : D.xIdx) :
    D.xOverlapObj (D.xIdxToJ i) (D.xIdxToJ j) ⟶
      D.xFormalGlueData.toLocallyRingedSpaceGlueData.U i :=
  basicOpenChart (I.map (algebraMap R (D.A (D.xIdxToJ i)))) (D.g (D.xIdxToJ i) (D.xIdxToJ j))

/-- The transition of the `X` glue datum, in the glue datum's spelling. -/
abbrev xTransitionU {i j : D.xIdx} (hij : i ≠ j) :
    D.xOverlapObj (D.xIdxToJ i) (D.xIdxToJ j) ⟶ D.xOverlapObj (D.xIdxToJ j) (D.xIdxToJ i) :=
  awayCompletionTransition (D.g (D.xIdxToJ i) (D.xIdxToJ j)) (D.g (D.xIdxToJ j) (D.xIdxToJ i))
    (D.τ (D.xIdxToJ i) (D.xIdxToJ j) (show D.xIdxToJ i ≠ D.xIdxToJ j from hij))

/-- Off the diagonal, the `X` glue datum's overlap is the basic open `D(g i j)` of the `i`-th
chart. -/
theorem xGlueData_V {i j : D.xIdx} (hij : i ≠ j) :
    D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
      D.xOverlapObj (D.xIdxToJ i) (D.xIdxToJ j) := by
  simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
    dif_neg (show ¬ @Eq D.J i j from hij), xOverlapObj]

/-- Off the diagonal, the `X` glue datum's overlap immersion is the basic-open chart at `g i j`,
up to the transport `ofGlueData'` inserts. -/
theorem xGlueData_f {i j : D.xIdx} (hij : i ≠ j)
    (h : D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
      D.xOverlapObj (D.xIdxToJ i) (D.xIdxToJ j)) :
    D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.f i j =
      eqToHom h ≫ D.xChartU i j := by
  simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', dif_neg (show ¬ @Eq D.J i j from hij), xChartU]

/-- Off the diagonal, the `X` glue datum's transition is `Spf` of the datum's `τ`, up to the
transports `ofGlueData'` inserts. -/
theorem xGlueData_t {i j : D.xIdx} (hij : i ≠ j)
    (h : D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
      D.xOverlapObj (D.xIdxToJ i) (D.xIdxToJ j))
    (h' : D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.V (j, i) =
      D.xOverlapObj (D.xIdxToJ j) (D.xIdxToJ i)) :
    D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.t i j =
      eqToHom h ≫ D.xTransitionU hij ≫ eqToHom h'.symm := by
  simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
    dif_neg (show ¬ @Eq D.J i j from hij), xTransitionU]

/-- **The `X` glue datum's glue relation off the diagonal, free of transports**: the overlap chart
into the `i`-th piece agrees, after the transition, with the one into the `j`-th. -/
theorem xGlueData_glue_raw {i j : D.xIdx} (hij : i ≠ j) :
    D.xChartU i j ≫ D.xFormalGlueData.ι i =
      D.xTransitionU hij ≫ D.xChartU j i ≫ D.xFormalGlueData.ι j := by
  have hc := D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.glue_condition i j
  rw [D.xGlueData_f hij (D.xGlueData_V hij),
    D.xGlueData_f (Ne.symm hij) (D.xGlueData_V (Ne.symm hij)),
    D.xGlueData_t hij (D.xGlueData_V hij) (D.xGlueData_V (Ne.symm hij))] at hc
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hc
  exact ((cancel_epi (eqToHom (D.xGlueData_V hij))).1 hc).symm


end Generic
end AffineChartedFibreDatumX

/-! ### The Tate-specific comparison -/

variable (B : Type u) [CommRing B] [Algebra R B]

/-- The index type of the Tate datum's glue datum, in the glue datum's own spelling. -/
abbrev tateXDatumIdx (hq : q ∈ I) (hI : I.FG) : Type u :=
  (tateCurveExposeXDatum R I q B hq hI).xIdx

/-- The two index types agree; this reducible identity is what lets a datum index be fed to the
model's glue datum in a statement that stays type-correct at `instances` transparency. -/
abbrev tateXIdxToModel {R : Type u} [CommRing R] {I : Ideal R} {q : R} [IsNoetherianRing R]
    {B : Type u} [CommRing B] [Algebra R B] {hq : q ∈ I} {hI : I.FG}
    (i : tateXDatumIdx R I q B hq hI) : tateModelIdx R I q hq hI := i

/-- The reverse identification of index types. -/
abbrev tateModelIdxToX {R : Type u} [CommRing R] {I : Ideal R} {q : R} [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] {hq : q ∈ I} {hI : I.FG}
    (i : tateModelIdx R I q hq hI) : tateXDatumIdx R I q B hq hI := i

/-- The chart comparison, in the two glue data's spellings. -/
abbrev tateChartCompU {R : Type u} [CommRing R] {I : Ideal R} {q : R} [IsNoetherianRing R]
    {B : Type u} [CommRing B] [Algebra R B] {hq : q ∈ I} {hI : I.FG}
    (i : tateXDatumIdx R I q B hq hI) :
    (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.toLocallyRingedSpaceGlueData.U i ⟶
      (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U (tateXIdxToModel i) :=
  (tateChartCompIso R I q).hom

/-- The inverse chart comparison, in the two glue data's spellings. -/
abbrev tateChartCompUInv {R : Type u} [CommRing R] {I : Ideal R} {q : R} [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] {hq : q ∈ I} {hI : I.FG}
    (i : tateModelIdx R I q hq hI) :
    (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U i ⟶
      (tateCurveExposeXDatum R I q B hq
        hI).xFormalGlueData.toLocallyRingedSpaceGlueData.U (tateModelIdxToX B i) :=
  (tateChartCompIso R I q).inv

private abbrev txCompHomU (hq : q ∈ I) (hI : I.FG) (i j : tateXDatumIdx R I q B hq hI) :
    (tateCurveExposeXDatum R I q B hq hI).xOverlapObj
        ((tateCurveExposeXDatum R I q B hq hI).xIdxToJ i)
        ((tateCurveExposeXDatum R I q B hq hI).xIdxToJ j) ⟶ tcOverlap R I q :=
  (tateOverlapCompIso R I q hq hI).hom

private abbrev txCompInvU (hq : q ∈ I) (hI : I.FG) (i j : tateXDatumIdx R I q B hq hI) :
    tcOverlap R I q ⟶ (tateCurveExposeXDatum R I q B hq hI).xOverlapObj
      ((tateCurveExposeXDatum R I q B hq hI).xIdxToJ i)
      ((tateCurveExposeXDatum R I q B hq hI).xIdxToJ j) :=
  (tateOverlapCompIso R I q hq hI).inv

private theorem tate_chart_law (hq : q ∈ I) (hI : I.FG) (i j : tateXDatumIdx R I q B hq hI) :
    (tateCurveExposeXDatum R I q B hq hI).xChartU i j ≫ tateChartCompU i =
      txCompHomU R I q B hq hI i j ≫ tcChartU R I q hq hI (tateXIdxToModel i) :=
  tateOverlapCompIso_hom_fac R I q hq hI

private theorem tate_transition_law (hq : q ∈ I) (hI : I.FG) {i j : tateXDatumIdx R I q B hq hI}
    (hij : i ≠ j) :
    (tateCurveExposeXDatum R I q B hq hI).xTransitionU hij ≫ txCompHomU R I q B hq hI j i =
      txCompHomU R I q B hq hI i j ≫ tcTransition R I q hI :=
  tateOverlapCompIso_transition_fac R I q hq hI

/-! ### The two glue conditions -/

private theorem tate_glue_raw_hom (hq : q ∈ I) (hI : I.FG) {i j : tateXDatumIdx R I q B hq hI}
    (hij : i ≠ j) :
    (tateCurveExposeXDatum R I q B hq hI).xChartU i j ≫
        tateChartCompU i ≫ (tateCurveFormalGlueData R I q hq hI).ι
          (tateXIdxToModel i) =
      (tateCurveExposeXDatum R I q B hq hI).xTransitionU hij ≫
        (tateCurveExposeXDatum R I q B hq hI).xChartU j i ≫
          tateChartCompU j ≫ (tateCurveFormalGlueData R I q hq hI).ι
            (tateXIdxToModel j) := by
  rw [← Category.assoc, tate_chart_law, Category.assoc,
    tcm_glue_raw R I q hq hI (show tateXIdxToModel i ≠ tateXIdxToModel j from hij),
    ← Category.assoc, ← tate_transition_law R I q B hq hI hij]
  simp only [Category.assoc]
  rw [← Category.assoc ((tateCurveExposeXDatum R I q B hq hI).xChartU j i), tate_chart_law]
  simp only [Category.assoc]

private theorem tateXGlued_hom_condition (hq : q ∈ I) (hI : I.FG)
    (i j : tateXDatumIdx R I q B hq hI) :
    (tateCurveExposeXDatum R I q B hq
          hI).xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫
        (tateChartCompU i ≫
          (tateCurveFormalGlueData R I q hq hI).ι (tateXIdxToModel i)) =
      (tateCurveExposeXDatum R I q B hq
            hI).xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
        (tateCurveExposeXDatum R I q B hq
            hI).xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.f j i ≫
          (tateChartCompU j ≫
            (tateCurveFormalGlueData R I q hq hI).ι (tateXIdxToModel j)) := by
  by_cases hij : i = j
  · subst hij
    simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
  · rw [(tateCurveExposeXDatum R I q B hq hI).xGlueData_f hij
      ((tateCurveExposeXDatum R I q B hq hI).xGlueData_V hij),
    (tateCurveExposeXDatum R I q B hq hI).xGlueData_f (Ne.symm hij)
      ((tateCurveExposeXDatum R I q B hq hI).xGlueData_V (Ne.symm hij)),
    (tateCurveExposeXDatum R I q B hq hI).xGlueData_t hij
      ((tateCurveExposeXDatum R I q B hq hI).xGlueData_V hij)
      ((tateCurveExposeXDatum R I q B hq hI).xGlueData_V (Ne.symm hij))]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [tate_glue_raw_hom R I q B hq hI hij]

/-! ### The inverse comparison laws -/

private theorem tate_chart_law_inv (hq : q ∈ I) (hI : I.FG) (i j : tateModelIdx R I q hq hI) :
    tcChartU R I q hq hI i ≫ tateChartCompUInv B i =
      txCompInvU R I q B hq hI (tateModelIdxToX B i) (tateModelIdxToX B j) ≫
        (tateCurveExposeXDatum R I q B hq hI).xChartU (tateModelIdxToX B i)
          (tateModelIdxToX B j) := by
  rw [Iso.eq_inv_comp, ← Category.assoc,
    ← tate_chart_law R I q B hq hI (tateModelIdxToX B i) (tateModelIdxToX B j),
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem tate_transition_law_inv (hq : q ∈ I) (hI : I.FG) {i j : tateModelIdx R I q hq hI}
    (hij : i ≠ j) :
    tcTransition R I q hI ≫ txCompInvU R I q B hq hI (tateModelIdxToX B j)
        (tateModelIdxToX B i) =
      txCompInvU R I q B hq hI (tateModelIdxToX B i) (tateModelIdxToX B j) ≫
        (tateCurveExposeXDatum R I q B hq hI).xTransitionU
          (show tateModelIdxToX B i ≠ tateModelIdxToX B j from hij) := by
  rw [Iso.eq_inv_comp, ← Category.assoc,
    ← tate_transition_law R I q B hq hI (show tateModelIdxToX B i ≠ tateModelIdxToX B j
      from hij), Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem tate_glue_raw_inv (hq : q ∈ I) (hI : I.FG) {i j : tateModelIdx R I q hq hI}
    (hij : i ≠ j) :
    tcChartU R I q hq hI i ≫ tateChartCompUInv B i ≫
        (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B i) =
      tcTransition R I q hI ≫ tcChartU R I q hq hI j ≫ tateChartCompUInv B j ≫
        (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B j) := by
  rw [← Category.assoc, tate_chart_law_inv R I q B hq hI i j, Category.assoc,
    (tateCurveExposeXDatum R I q B hq hI).xGlueData_glue_raw
      (show tateModelIdxToX B i ≠ tateModelIdxToX B j from hij),
    ← Category.assoc, ← tate_transition_law_inv R I q B hq hI hij]
  simp only [Category.assoc]
  rw [← Category.assoc (tcChartU R I q hq hI j), tate_chart_law_inv R I q B hq hI j i]
  simp only [Category.assoc]

private theorem tateXGlued_inv_condition (hq : q ∈ I) (hI : I.FG) (i j : tateModelIdx R I q hq hI) :
    (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f i j ≫
        (tateChartCompUInv B i ≫
          (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B i)) =
      (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
        (tateCurveFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f j i ≫
          (tateChartCompUInv B j ≫
            (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B j)) := by
  by_cases hij : i = j
  · subst hij
    simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
  · rw [tcm_f R I q hq hI hij (tcm_V R I q hq hI hij),
      tcm_f R I q hq hI (Ne.symm hij) (tcm_V R I q hq hI (Ne.symm hij)),
      tcm_t R I q hq hI hij (tcm_V R I q hq hI hij) (tcm_V R I q hq hI (Ne.symm hij))]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [tate_glue_raw_inv R I q B hq hI hij]

/-! ### The comparison isomorphism -/

/-- **The comparison morphism** `xGlued ⟶ 𝔈_q`, glued from the chart comparisons. -/
def tateXGluedHom (hq : q ∈ I) (hI : I.FG) :
    ((tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.gluedFormalScheme).toLocallyRingedSpace ⟶
      ((tateCurveFormalGlueData R I q hq hI).gluedFormalScheme).toLocallyRingedSpace :=
  (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.glueMorphisms
    (fun i => tateChartCompU i ≫
      (tateCurveFormalGlueData R I q hq hI).ι (tateXIdxToModel i))
    (tateXGlued_hom_condition R I q B hq hI)

/-- **The inverse comparison morphism** `𝔈_q ⟶ xGlued`. -/
def tateXGluedInv (hq : q ∈ I) (hI : I.FG) :
    ((tateCurveFormalGlueData R I q hq hI).gluedFormalScheme).toLocallyRingedSpace ⟶
      ((tateCurveExposeXDatum R I q B hq
        hI).xFormalGlueData.gluedFormalScheme).toLocallyRingedSpace :=
  (tateCurveFormalGlueData R I q hq hI).glueMorphisms
    (fun i => tateChartCompUInv B i ≫
      (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B i))
    (tateXGlued_inv_condition R I q B hq hI)

/-- **The comparison morphism restricted to the `i`-th chart** is the chart comparison followed by
the model's glue inclusion. This, with `ι_tateXGluedInv`, is what brick 4c consumes. -/
theorem ι_tateXGluedHom (hq : q ∈ I) (hI : I.FG) (i : tateXDatumIdx R I q B hq hI) :
    (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι i ≫ tateXGluedHom R I q B hq hI =
      tateChartCompU i ≫
        (tateCurveFormalGlueData R I q hq hI).ι (tateXIdxToModel i) :=
  FormalScheme.GlueData.ι_glueMorphisms _ _ _ i

/-- **The inverse comparison morphism restricted to the `i`-th chart.** -/
theorem ι_tateXGluedInv (hq : q ∈ I) (hI : I.FG) (i : tateModelIdx R I q hq hI) :
    (tateCurveFormalGlueData R I q hq hI).ι i ≫ tateXGluedInv R I q B hq hI =
      tateChartCompUInv B i ≫
        (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B i) :=
  FormalScheme.GlueData.ι_glueMorphisms _ _ _ i

private theorem tateXGluedHom_comp_inv (hq : q ∈ I) (hI : I.FG) :
    tateXGluedHom R I q B hq hI ≫ tateXGluedInv R I q B hq hI = 𝟙 _ := by
  refine FormalScheme.GlueData.hom_ext _ fun i => ?_
  rw [← Category.assoc, ι_tateXGluedHom, Category.assoc, ι_tateXGluedInv,
    ← Category.assoc, Category.comp_id,
    show tateChartCompU i ≫ tateChartCompUInv B (tateXIdxToModel i) = 𝟙 _
      from (tateChartCompIso R I q).hom_inv_id, Category.id_comp]

private theorem tateXGluedInv_comp_hom (hq : q ∈ I) (hI : I.FG) :
    tateXGluedInv R I q B hq hI ≫ tateXGluedHom R I q B hq hI = 𝟙 _ := by
  refine FormalScheme.GlueData.hom_ext _ fun i => ?_
  rw [← Category.assoc, ι_tateXGluedInv, Category.assoc, ι_tateXGluedHom,
    ← Category.assoc, Category.comp_id,
    show tateChartCompUInv B i ≫ tateChartCompU (tateModelIdxToX B i) = 𝟙 _
      from (tateChartCompIso R I q).inv_hom_id, Category.id_comp]

/-- **The glued object of the Tate `X`-expose datum is the Tate curve model**, as locally ringed
spaces. -/
def tateXGluedIsoLRS (hq : q ∈ I) (hI : I.FG) :
    ((tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.gluedFormalScheme).toLocallyRingedSpace ≅
      ((tateCurveFormalGlueData R I q hq hI).gluedFormalScheme).toLocallyRingedSpace where
  hom := tateXGluedHom R I q B hq hI
  inv := tateXGluedInv R I q B hq hI
  hom_inv_id := tateXGluedHom_comp_inv R I q B hq hI
  inv_hom_id := tateXGluedInv_comp_hom R I q B hq hI

/-- **The glued object of the Tate `X`-expose datum is the Tate curve model.** -/
def tateXGluedIso (hq : q ∈ I) (hI : I.FG) :
    (tateCurveExposeXDatum R I q B hq hI).xGlued ≅ tateCurveModel R I q hq hI :=
  (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).preimageIso (tateXGluedIsoLRS R I q B hq hI)

/-- The underlying morphism of locally ringed spaces of `tateXGluedIso` is `tateXGluedHom`. -/
theorem forgetToLocallyRingedSpace_map_tateXGluedIso_hom (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.forgetToLocallyRingedSpace.map (tateXGluedIso R I q B hq hI).hom =
      tateXGluedHom R I q B hq hI :=
  (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).map_preimage _


end AlgebraicGeometry

end
