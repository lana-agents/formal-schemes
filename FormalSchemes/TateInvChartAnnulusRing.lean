import FormalSchemes.TateInvOverlapBand
import FormalSchemes.TateInvQuotientChartRing

set_option linter.style.header false

/-!
# The chart ring of `T_inv/⟨σ⟩`, as the equalizer of two annulus-chart restrictions

`AlgebraicGeometry.tateInvChartSubring` (`FormalSchemes.TateInvQuotientChartRing`) identifies
`Γ (T_inv/⟨σ⟩, V)` with a subring of `Γ (Spf A, tateInvPatchSaturate S)`, but cuts it out by an
infimum of `RingHom.eqLocus`s indexed by **every** pair of patch indices, each leg naming the
chain's glue datum. `AlgebraicGeometry.isTateInvOverlapCompatible_iff_charts`
(`FormalSchemes.TateInvOverlapBand`) collapses that family to **two** equations between morphisms
of formal spectra of annuli. The two files landed within minutes of each other on branches neither
of which saw the other, so nothing joined them.

This file joins them. The bridge is `AlgebraicGeometry.mem_tateInvChartSubring_iff`, and the
outcome is that the same subring is the infimum of exactly two `RingHom.eqLocus`s, whose four legs
are the two annulus overlap charts and the `𝔾m`-inversion transition.

## What is here

* `AlgebraicGeometry.tateInvChartAnnulusSubring`: the `Subring` of
  `Γ (Spf A, tateInvPatchSaturateOpens hq hI hS)` cut out by the two chart conditions, as
  `RingHom.eqLocus … ⊓ RingHom.eqLocus …`. No glue datum, no `ι`, no overlap object of the chain
  occurs in either leg.
* `AlgebraicGeometry.mem_tateInvChartAnnulusSubring_iff`: membership is
  `AlgebraicGeometry.IsTateInvChartCompatibleForward` and
  `AlgebraicGeometry.IsTateInvChartCompatibleBackward` together.
* `AlgebraicGeometry.tateInvChartSubring_eq_tateInvChartAnnulusSubring`: **the two subrings are
  equal.** This is the statement `FormalSchemes.TateInvQuotientChartRing` names as missing.
* `AlgebraicGeometry.tateInvChartAnnulusRingEquiv` and
  `AlgebraicGeometry.exists_tateInvChartAnnulusRingEquiv`: `Γ (T_inv/⟨σ⟩, V)` is isomorphic to it,
  by transport of `AlgebraicGeometry.tateInvChartRingEquiv` along that equality. There is no new
  content in these two; they exist so that a consumer never has to mention
  `tateInvChartSubring`'s `⨅` again.
* `AlgebraicGeometry.tateInvChartAnnulusSubring_eq_top_iff`: the subring is the whole of
  `Γ (Spf A, tateInvPatchSaturateOpens hq hI hS)` exactly when the two chart legs agree as *ring
  homomorphisms*. This is the reformulation that turns "is the subring proper?" into a question
  about two maps and no sections.

## What is *not* proved

**Whether the subring is proper.** `tateInvChartAnnulusSubring_eq_top_iff` reduces that question
to the equality of two named ring homomorphisms, which is strictly better posed than
`FormalSchemes.TateInvQuotientChartRing` left it — there the condition was an `⨅` over `ℤ × ℤ` and
the legs were glue-datum morphisms — but it does not answer it. Answering it needs the two legs
read in the coordinates of `FormalSchemes.TateChartTransitionInvAlgEq`, which is not done here.
`AlgebraicGeometry.isTateInvOverlapCompatible_one` and the membership of `0` are non-vacuity, not
an answer.

**The open is still described through the chain.**
`AlgebraicGeometry.tateInvPatchSaturateOpens hq hI hS` is by definition the preimage under
`ι ⟨0⟩` of a saturation inside `T_inv` (`FormalSchemes.TateInvNodeChartRing`). What the results
below eliminate is the glue datum from the four **legs**, not from the open they are read over.

**Nothing here produces a chart.** A ring is not a chart:
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) still needs an adic structure on this ring and an
open immersion out of its formal spectrum.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon;
  the affine chart at its node is `Spec` of the subring of functions agreeing at the two
  preimages, and that subring is proper. The classical statement is about a nodal curve over a
  field, so it predicts the answer to the question left open above rather than settling it.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

/-- **A `RingHom.eqLocus` is everything exactly when the two maps are equal.** Mathlib has
`RingHom.eqLocus_same` (the `←` direction at `f = g`) but not this `iff`; it is what turns a
question about a subring into a question about two maps. -/
theorem RingHom.eqLocus_eq_top_iff {A B : Type*} [Ring A] [Ring B] {f g : A →+* B} :
    f.eqLocus g = ⊤ ↔ f = g := by
  rw [Subring.eq_top_iff']
  refine ⟨fun h => RingHom.ext fun x => h x, fun h x => ?_⟩
  subst h
  exact RingHom.mem_eqLocus.2 rfl

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}
variable {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}

/-! ### The four legs, as ring homomorphisms -/

/-- **The `x`-chart restriction**, as a `RingHom`: the left leg of
`AlgebraicGeometry.IsTateInvChartCompatibleForward`. -/
def tateInvChartLegX (hS : IsOpen S) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI hS)) →+*
      (FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
        (annulusIdealOfDefinition R I q) (overlapX R I q))).presheaf.obj
        (op ((Opens.map (annulusOverlapChart R I q).base).obj
          (tateInvPatchSaturateOpens hq hI hS))) :=
  ((annulusOverlapChart R I q).c.app (op (tateInvPatchSaturateOpens hq hI hS))).hom

/-- **The transition-then-`y`-chart restriction**, as a `RingHom`, with its target transported onto
the `x`-chart's by `AlgebraicGeometry.map_annulusOverlapChartY_tateInvPatchSaturateOpens`: the
right leg of `AlgebraicGeometry.IsTateInvChartCompatibleForward`.

The transport is what makes the two legs comparable at all; without it they land in the sections
over two syntactically different opens of `Spf A{1/x}`. -/
def tateInvChartLegYX (hS : IsOpen S) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI hS)) →+*
      (FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
        (annulusIdealOfDefinition R I q) (overlapX R I q))).presheaf.obj
        (op ((Opens.map (annulusOverlapChart R I q).base).obj
          (tateInvPatchSaturateOpens hq hI hS))) :=
  (((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
    (annulusIdealOfDefinition R I q) (overlapX R I q))).presheaf.map
      (eqToHom (congrArg op (map_annulusOverlapChartY_tateInvPatchSaturateOpens hS)))).hom).comp
    ((((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q).c.app
      (op (tateInvPatchSaturateOpens hq hI hS))).hom)

/-- **The `y`-chart restriction**, as a `RingHom`: the left leg of
`AlgebraicGeometry.IsTateInvChartCompatibleBackward`. -/
def tateInvChartLegY (hS : IsOpen S) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI hS)) →+*
      (FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
        (annulusIdealOfDefinition R I q) (overlapY R I q))).presheaf.obj
        (op ((Opens.map (annulusOverlapChartY R I q).base).obj
          (tateInvPatchSaturateOpens hq hI hS))) :=
  ((annulusOverlapChartY R I q).c.app (op (tateInvPatchSaturateOpens hq hI hS))).hom

/-- **The inverse-transition-then-`x`-chart restriction**, as a `RingHom`: the right leg of
`AlgebraicGeometry.IsTateInvChartCompatibleBackward`, transported by
`AlgebraicGeometry.map_annulusOverlapChart_tateInvPatchSaturateOpens`. -/
def tateInvChartLegXY (hS : IsOpen S) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI hS)) →+*
      (FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
        (annulusIdealOfDefinition R I q) (overlapY R I q))).presheaf.obj
        (op ((Opens.map (annulusOverlapChartY R I q).base).obj
          (tateInvPatchSaturateOpens hq hI hS))) :=
  (((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
    (annulusIdealOfDefinition R I q) (overlapY R I q))).presheaf.map
      (eqToHom (congrArg op (map_annulusOverlapChart_tateInvPatchSaturateOpens hS)))).hom).comp
    ((((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q).c.app
      (op (tateInvPatchSaturateOpens hq hI hS))).hom)

/-- The forward chart condition is the equation between the two forward legs. Definitional; it is
stated so that the `RingHom.eqLocus` below can be quoted against
`AlgebraicGeometry.IsTateInvChartCompatibleForward`. -/
theorem isTateInvChartCompatibleForward_iff (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    IsTateInvChartCompatibleForward hS s ↔
      tateInvChartLegX (hq := hq) (hI := hI) hS s = tateInvChartLegYX hS s :=
  Iff.rfl

/-- The backward chart condition is the equation between the two backward legs. Definitional. -/
theorem isTateInvChartCompatibleBackward_iff (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    IsTateInvChartCompatibleBackward hS s ↔
      tateInvChartLegY (hq := hq) (hI := hI) hS s = tateInvChartLegXY hS s :=
  Iff.rfl

/-! ### The subring -/

/-- **The chart ring, as the equalizer of two pairs of ring homomorphisms.** Each of the two chart
conditions of `FormalSchemes.TateInvOverlapBand` is an equation between the values of two
`RingHom`s out of `Γ (Spf A, tateInvPatchSaturateOpens hq hI hS)`, so each cuts out a
`RingHom.eqLocus` and the pair cuts out their infimum.

`tateInvChartSubring_eq_tateInvChartAnnulusSubring` says this is the same subring as
`AlgebraicGeometry.tateInvChartSubring`, which is defined by an infimum indexed by every pair of
patch indices with glue-datum morphisms for legs. -/
def tateInvChartAnnulusSubring (hS : IsOpen S) :
    Subring ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :=
  RingHom.eqLocus (tateInvChartLegX (hq := hq) (hI := hI) hS) (tateInvChartLegYX hS) ⊓
    RingHom.eqLocus (tateInvChartLegY (hq := hq) (hI := hI) hS) (tateInvChartLegXY hS)

/-- **Membership is the pair of chart conditions.** `Subring.mem_inf` and `RingHom.mem_eqLocus`
unfold the definition, and the two sides are then the two `Iff.rfl`s above. -/
theorem mem_tateInvChartAnnulusSubring_iff (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    s ∈ tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS ↔
      IsTateInvChartCompatibleForward hS s ∧ IsTateInvChartCompatibleBackward hS s := by
  simp only [tateInvChartAnnulusSubring, Subring.mem_inf, RingHom.mem_eqLocus,
    isTateInvChartCompatibleForward_iff, isTateInvChartCompatibleBackward_iff]

/-- **The two spellings of the chart ring agree.** `AlgebraicGeometry.mem_tateInvChartSubring_iff`
turns membership in `AlgebraicGeometry.tateInvChartSubring` into
`AlgebraicGeometry.IsTateInvOverlapCompatible`,
`AlgebraicGeometry.isTateInvOverlapCompatible_iff_charts` turns that into the two chart conditions,
and `mem_tateInvChartAnnulusSubring_iff` turns those back into membership here.

This is what `FormalSchemes.TateInvQuotientChartRing`'s "What is *not* proved" section asks for:
the `⨅` over `ℤ × ℤ` is an infimum of two `RingHom.eqLocus`s, and no glue-datum morphism survives
in any leg. -/
theorem tateInvChartSubring_eq_tateInvChartAnnulusSubring (hS : IsOpen S) :
    tateInvChartSubring (hq := hq) (hI := hI) hS =
      tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS := by
  ext s
  rw [mem_tateInvChartSubring_iff, mem_tateInvChartAnnulusSubring_iff,
    isTateInvOverlapCompatible_iff_charts]

/-! ### The isomorphism, restated -/

section Quotient

variable (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)

/-- **`Γ (T_inv/⟨σ⟩, V) ≅ tateInvChartAnnulusSubring hS`, as rings.**
`AlgebraicGeometry.tateInvChartRingEquiv` transported along
`tateInvChartSubring_eq_tateInvChartAnnulusSubring`. There is no new content here: the bijection
is #426's and the equality of subrings is the theorem above. -/
def tateInvChartAnnulusRingEquiv (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
      tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS :=
  (tateInvChartRingEquiv V hS hV).trans
    (RingEquiv.subringCongr (tateInvChartSubring_eq_tateInvChartAnnulusSubring hS))

end Quotient

/-- **The isomorphism is not conditioned on an unexhibited open.** For every open `S` of the model
patch, `AlgebraicGeometry.exists_preimage_eq_tateInvSaturateOpens` produces an open `V` of the
quotient whose preimage is the saturation of `S`, with no hypothesis on the action — which is what
makes it available at a node. -/
theorem exists_tateInvChartAnnulusRingEquiv (hS : IsOpen S) :
    ∃ (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
      (_ : (Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
          tateInvSaturateOpens hq hI hS),
      Nonempty (((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
        tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS) :=
  let ⟨V, hV⟩ := exists_preimage_eq_tateInvSaturateOpens (hq := hq) (hI := hI) hS
  ⟨V, hV, ⟨tateInvChartAnnulusRingEquiv V hS hV⟩⟩

/-! ### Properness, reduced to an equality of ring homomorphisms -/

/-- **The chart ring is everything exactly when the two chart legs agree.** With the condition cut
down to two `RingHom.eqLocus`s, "is the subring proper?" is no longer a question about sections: it
is the question whether `tateInvChartLegX = tateInvChartLegYX` and
`tateInvChartLegY = tateInvChartLegXY` as ring homomorphisms.

This does **not** answer it. It is the reformulation that makes the question finite: before it, the
condition was an infimum over every pair of patch indices whose legs named the chain's glue datum,
and there was nothing to compare. Deciding it needs the four legs read in the coordinates of
`FormalSchemes.TateChartTransitionInvAlgEq`. -/
theorem tateInvChartAnnulusSubring_eq_top_iff (hS : IsOpen S) :
    tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS = ⊤ ↔
      tateInvChartLegX (hq := hq) (hI := hI) hS = tateInvChartLegYX hS ∧
        tateInvChartLegY (hq := hq) (hI := hI) hS = tateInvChartLegXY hS := by
  simp only [tateInvChartAnnulusSubring, RingHom.eqLocus_eq_top_iff, inf_eq_top_iff]

/-- **The chart ring is everything exactly when every section satisfies both chart conditions.**
The section-level form of `tateInvChartAnnulusSubring_eq_top_iff`, kept because it is the shape a
refutation would take: a single `s` failing one of the two conditions proves the subring proper. -/
theorem tateInvChartAnnulusSubring_ne_top_iff (hS : IsOpen S) :
    tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS ≠ ⊤ ↔
      ∃ s : (FormalSpectrum.locallyRingedSpaceObj
          (annulusIdealOfDefinition R I q)).presheaf.obj
          (op (tateInvPatchSaturateOpens hq hI hS)),
        ¬ (IsTateInvChartCompatibleForward hS s ∧ IsTateInvChartCompatibleBackward hS s) := by
  rw [ne_eq, Subring.eq_top_iff', not_forall]
  simp only [mem_tateInvChartAnnulusSubring_iff]

end AlgebraicGeometry
