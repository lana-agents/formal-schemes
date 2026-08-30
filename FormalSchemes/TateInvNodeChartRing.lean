import FormalSchemes.TateInvNodeLocus
import FormalSchemes.GlueDataSectionExt
import FormalSchemes.ActionQuotientSectionInjective

set_option linter.style.header false

/-!
# The sections of `T_inv/⟨σ⟩` live on a single patch

`FormalSchemes.TateInvNodeLocus` settled the *points* of the period-`q` Tate quotient over the
image of a saturation: `image_base_tateInvSaturate_eq_image_base_ι` says `π '' tateInvSaturate S`
is the image of one patch's copy of `S`, and `eq_of_base_ι_eq_of_mem_tateInvNodeLocus` says the
node points of that patch are identified with nothing but themselves. Both are statements about
underlying spaces; that file says so, twice, and constructs no morphism of locally ringed spaces.

This file is the first statement on this tree about the **structure sheaf** of the quotient. It
proves the injectivity half of the expected description of `Γ (Q, π V)`: for `V` the saturation of
an open of the model patch `Spf A`, a section of the quotient over `π V` is determined by its
pullback to `Spf A` along one patch, for any single patch index. So `Γ (Q, π V)` is a **subring of
`Γ (Spf A, S')`**, where `S'` is the part of `Spf A` that the saturation sees.

## What is proved, and what is not

Write `D` for `tateChainInvFormalGlueData`, `ι m` for its patch inclusions and
`π : T_inv ⟶ Q` for an action quotient of the `q^ℤ`-shift.

* `AlgebraicGeometry.ι_comp_eq_of_isActionQuotient`: **`ι n ≫ π = ι m ≫ π`** — the patch index is
  invisible after projecting. This is the morphism-level statement whose pointwise shadow
  `AlgebraicGeometry.base_ι_eq_of_isActionQuotient`
  (`FormalSchemes.TateInvPeriodQuotientCharts`) proves inline; naming it is what makes the sections
  argument possible, since a `c`-component is a statement about a morphism and not about points.
* `AlgebraicGeometry.injective_c_app_ι_comp_of_isActionQuotient`: **the collapse.** For every open
  `V` of `Q` and every patch index `m`, the ring map `Γ (Q, V) → Γ (Spf A, (ι m ≫ π)⁻¹ V)` is
  injective. Two inputs: `AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq`
  (`FormalSchemes.GlueDataSectionExt`) says a section of the glued chain is determined patch by
  patch, and the previous item collapses all those patch data onto one.
* `AlgebraicGeometry.injective_globalSectionsToAnnulus`: at `V = ⊤`, composed with
  `FormalSpectrum.globalSectionsEquiv`: **`Γ (T_inv/⟨σ⟩)` is a subring of
  `A = R{x, y}/(x·y − q)`**, whatever the quotient turns out to be. The composite is
  `AlgebraicGeometry.globalSectionsToAnnulus`, a `def` only because the adic-ring instance on
  `annulusIdealOfDefinition` is a theorem applied to `hI` and so cannot appear in a statement.
* `AlgebraicGeometry.injective_c_app_tateInvSaturate`: the same at `V = π '' tateInvSaturate S`,
  where the target open is computed to be `tateInvPatchSaturate S`.

**The surjectivity half is not proved here and is not claimed here.** Which sections of `Spf A`
extend to the quotient is the existence half of the sheaf axiom on the cover `{ι m '' S}`, and it
is what turns the injection into the equalizer description. `FormalSchemes.GlueDataSectionExt`
deliberately proves only separation; see its module docstring. So this file does not identify the
ring — it locates it, inside a ring on one patch. The identification is
`AlgebraicGeometry.tateInvChartRingEquiv` (`FormalSchemes.TateInvQuotientChartRing`), over
`tateInvPatchSaturate` below.

## The open that the saturation sees

`(ι m)⁻¹ (tateInvSaturate S)` is in general **larger than `S`**: a point of `Spf A` outside `S`
whose image lies in an overlap can be carried into `ι (m ± 1) '' S` by the transition. That is not
a defect of the construction, it is where the overlap condition of the expected equalizer
description comes from. `AlgebraicGeometry.tateInvPatchSaturate` names this open,
`subset_tateInvPatchSaturate` records `S ⊆ tateInvPatchSaturate S`,
`preimage_ι_tateInvSaturate` records that it does not depend on the patch index — cofinality of
the description in the patch, which is what makes "the ring of the chart" well posed — and
`tateInvSaturate_tateInvPatchSaturate` records that saturating it again changes nothing, so one
may always normalise `S` to it.

## Main results

* `AlgebraicGeometry.base_inv_tateInvShiftAut_zpow_apply`,
  `AlgebraicGeometry.tateInvShiftAut_zpow_neg_hom`,
  `AlgebraicGeometry.mem_tateInvSaturate_shift_iff`: the shift is invisible to a saturation, on
  points.
* `AlgebraicGeometry.tateInvPatchSaturate`, `AlgebraicGeometry.preimage_ι_tateInvSaturate`,
  `AlgebraicGeometry.subset_tateInvPatchSaturate`,
  `AlgebraicGeometry.isOpen_tateInvPatchSaturate`,
  `AlgebraicGeometry.tateInvSaturate_tateInvPatchSaturate`,
  `AlgebraicGeometry.tateInvPatchSaturate_univ`: the open of `Spf A` that a saturation sees.
* `AlgebraicGeometry.ι_comp_eq_of_isActionQuotient`
* `AlgebraicGeometry.injective_c_app_ι_comp_of_isActionQuotient`: **the collapse.**
* `AlgebraicGeometry.globalSectionsToAnnulus`,
  `AlgebraicGeometry.injective_globalSectionsToAnnulus`,
  `AlgebraicGeometry.injective_globalSectionsToAnnulus_actionQuotient`: `Γ (T_inv/⟨σ⟩)` is a
  subring of `A`, in general and at the coequalizer presentation.
* `AlgebraicGeometry.injective_c_app_tateInvSaturate`,
  `AlgebraicGeometry.preimage_ι_comp_image_base_tateInvSaturate`: the same over the image of a
  saturation, with the source open identified.
* `AlgebraicGeometry.tateInvChartLocus_ne_univ`: for `I ≠ ⊤` the chart locus is a *proper* open, so
  the general `S` is not the case `S = Set.univ` in disguise.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon;
  the affine chart at its node is `Spec` of the subring of functions agreeing at the two preimages,
  which is the ring this file locates.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### The shift, on a saturation -/

/-- **The shift is invertible on points**, spelled so that it can be applied inside a membership.
`Iso.hom_inv_id` read on the underlying space; recorded because `σ ^ k` is an element of
`Aut T_inv` and `simp` does not get from the group inverse to `Iso.inv` unaided. -/
theorem base_inv_tateInvShiftAut_zpow_apply (k : ℤ)
    (x : (tateChainInv R I q hq hI).toLocallyRingedSpace) :
    ((tateInvShiftAut R I q hq hI) ^ k).inv.base
      (((tateInvShiftAut R I q hq hI) ^ k).hom.base x) = x := by
  have h := congrArg
    (fun φ : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶
      (tateChainInv R I q hq hI).toLocallyRingedSpace => ⇑φ.base x)
    ((tateInvShiftAut R I q hq hI) ^ k).hom_inv_id
  simpa only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
    ContinuousMap.coe_comp, Function.comp_apply, LocallyRingedSpace.id_toHom,
    PresheafedSpace.id_base, TopCat.hom_id, ContinuousMap.coe_id, id_eq] using h

/-- **`σ ^ (-k)` is the inverse of `σ ^ k`**, as morphisms. `zpow_neg` in `Aut T_inv`, unfolded to
the `Iso` field. -/
theorem tateInvShiftAut_zpow_neg_hom (k : ℤ) :
    ((tateInvShiftAut R I q hq hI) ^ (-k)).hom = ((tateInvShiftAut R I q hq hI) ^ k).inv := by
  rw [zpow_neg, Aut.Aut_inv_def, Iso.symm_hom]

variable {R I q}

/-- **A saturation does not see the shift, pointwise.** `x` lies in `tateInvSaturate S` if and only
if `σ ^ k x` does — the membership form of `image_tateInvShiftAut_zpow_tateInvSaturate`
(`FormalSchemes.TateInvSaturation`), which gives the equality of *images* and so only one of the
two directions on the nose. -/
theorem mem_tateInvSaturate_shift_iff (k : ℤ)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)))
    (x : (tateChainInv R I q hq hI).toLocallyRingedSpace) :
    ((tateInvShiftAut R I q hq hI) ^ k).hom.base x ∈ tateInvSaturate R I q hq hI S ↔
      x ∈ tateInvSaturate R I q hq hI S := by
  constructor
  · intro hx
    rw [← image_tateInvShiftAut_zpow_tateInvSaturate hq hI (-k) S]
    refine ⟨_, hx, ?_⟩
    rw [tateInvShiftAut_zpow_neg_hom R I q hq hI k]
    exact base_inv_tateInvShiftAut_zpow_apply R I q hq hI k x
  · intro hx
    rw [← image_tateInvShiftAut_zpow_tateInvSaturate hq hI k S]
    exact ⟨x, hx, rfl⟩

/-! ### The open of the model patch that a saturation sees -/

/-- **The part of the model patch that the saturation of `S` sees**: the preimage of
`tateInvSaturate S` along a patch inclusion. `preimage_ι_tateInvSaturate` says the choice of patch
does not matter, so `⟨0⟩` is taken as the representative.

It contains `S` (`subset_tateInvPatchSaturate`) and is in general strictly larger: a point outside
`S` lying in an overlap is carried into a neighbouring patch's copy of `S` by the transition. That
extra part is exactly what the equalizer description of `Γ (Q, π V)` imposes a condition on; that
description is `AlgebraicGeometry.tateInvChartSubring`
(`FormalSchemes.TateInvQuotientChartRing`), and it is stated over this open. -/
def tateInvPatchSaturate
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) :=
  ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base ⁻¹' tateInvSaturate R I q hq hI S

/-- **The patch a saturation is read on does not matter.** Every patch inclusion pulls
`tateInvSaturate S` back to the same open of `Spf A`, because `ι n = ι m ≫ σ ^ (n − m)` and a
saturation does not see the shift (`mem_tateInvSaturate_shift_iff`).

This is what makes "the ring of the chart" well posed as a statement about `Spf A`: the collapse
`injective_c_app_ι_comp_of_isActionQuotient` holds for each `m` separately, and this says all those
statements are about one and the same open. -/
theorem preimage_ι_tateInvSaturate
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)))
    (m : ULift.{u} ℤ) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base ⁻¹' tateInvSaturate R I q hq hI S =
      tateInvPatchSaturate hq hI S := by
  ext z
  have hshift : ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base z =
      ((tateInvShiftAut R I q hq hI) ^ m.down).hom.base
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base z) := by
    have hmor := ι_tateInvShiftAut_zpow R I q hq hI m.down ⟨0⟩
    have hidx : (⟨(0 : ℤ) + m.down⟩ : ULift.{u} ℤ) = m := ULift.down_injective (by simp)
    have h := congrArg
      (fun φ : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U ⟨0⟩ ⟶
        (tateChainInv R I q hq hI).toLocallyRingedSpace => ⇑φ.base z) (hmor.trans (by rw [hidx]))
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply] at h
    exact h.symm
  change ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base z ∈
      tateInvSaturate R I q hq hI S ↔
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base z ∈ tateInvSaturate R I q hq hI S
  rw [hshift]
  exact mem_tateInvSaturate_shift_iff hq hI m.down S _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `S` sits inside the open its own saturation sees. -/
theorem subset_tateInvPatchSaturate
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    S ⊆ tateInvPatchSaturate hq hI S :=
  fun z hz => image_ι_subset_tateInvSaturate hq hI S ⟨0⟩ ⟨z, hz, rfl⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`tateInvPatchSaturate` of an open is open**, being a preimage of the open
`tateInvSaturate S`. -/
theorem isOpen_tateInvPatchSaturate
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    (hS : IsOpen S) : IsOpen (tateInvPatchSaturate hq hI S) :=
  (isOpen_tateInvSaturate hq hI hS).preimage
    ((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base.hom.continuous

/-- **Normalising `S` changes nothing.** The saturation of `tateInvPatchSaturate S` is
`tateInvSaturate S` again, so every statement below may be read with `S` already equal to the open
its saturation sees. One inclusion is `subset_tateInvPatchSaturate` and monotonicity; the other is
`tateInvSaturate_subset_of_invariant`, whose hypothesis is
`image_tateInvShiftAut_zpow_tateInvSaturate`. -/
theorem tateInvSaturate_tateInvPatchSaturate
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    tateInvSaturate R I q hq hI (tateInvPatchSaturate hq hI S) =
      tateInvSaturate R I q hq hI S := by
  refine Set.Subset.antisymm ?_ (tateInvSaturate_mono hq hI (subset_tateInvPatchSaturate hq hI S))
  refine tateInvSaturate_subset_of_invariant hq hI
    (fun k => (image_tateInvShiftAut_zpow_tateInvSaturate hq hI k S).le) ⟨0⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  exact hz

section Quotient

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **The patch index is invisible after projecting to the quotient.** `ι n ≫ π = ι m ≫ π`, for
all patch indices.

The morphism-level form of `AlgebraicGeometry.base_ι_eq_of_isActionQuotient`
(`FormalSchemes.TateInvPeriodQuotientCharts`), which proves exactly this inline and then applies it
to a point. Naming it is what lets the argument reach the structure sheaf: the composite
`ι m ≫ π` is a morphism of locally ringed spaces, so it has a `c`-component, and the pointwise
statement does not. -/
theorem ι_comp_eq_of_isActionQuotient
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) {m n : ULift.{u} ℤ} (k : ℤ)
    (hk : n.down = m.down + k) :
    (tateChainInvFormalGlueData R I q hq hI).ι n ≫ π =
      (tateChainInvFormalGlueData R I q hq hI).ι m ≫ π := by
  obtain rfl : n = (⟨m.down + k⟩ : ULift.{u} ℤ) := ULift.down_injective hk
  have hinv : ((tateInvShiftAut R I q hq hI) ^ k).hom ≫ π = π :=
    h.isInvariant (Multiplicative.ofAdd k)
  conv_lhs => rw [← ι_tateInvShiftAut_zpow R I q hq hI k m]
  exact (Category.assoc _ _ _).trans (congrArg
    (fun φ : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q =>
      (tateChainInvFormalGlueData R I q hq hI).ι m ≫ φ) hinv)

/-- **The collapse: a section of the quotient is determined on one patch.** For every open `V` of
`Q` and every patch index `m`, the ring map `Γ (Q, V) → Γ (Spf A, (ι m ≫ π)⁻¹ V)` is injective.

Three steps, and each is a named theorem elsewhere.
`CategoryTheory.IsActionQuotient.injective_c_app`
(`FormalSchemes.ActionQuotientSectionInjective`) reduces to injectivity on `Γ (T_inv, π⁻¹ V)`;
`AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq` (`FormalSchemes.GlueDataSectionExt`)
reduces *that* to the family of pullbacks along all the patches; and
`ι_comp_eq_of_isActionQuotient` collapses the family to the single index `m`. The factorisation
`(ι i ≫ π).c.app = π.c.app ≫ (ι i).c.app` is definitional.

The transport of the hypothesis from index `m` to index `i` cannot be a `rw`: the type of
`(φ.c.app (op V)).hom t` depends on `φ`, so the motive is ill-typed. It is done by `congrArg` into
`Prop`, which is not — the *statement* `… = …` is a `Prop`-valued function of `φ` even though each
side is not. -/
theorem injective_c_app_ι_comp_of_isActionQuotient
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ) (V : Opens Q) :
    Function.Injective
      ((((tateChainInvFormalGlueData R I q hq hI).ι m ≫ π).c.app (op V)).hom) := by
  intro t t' heq
  refine h.injective_c_app V ?_
  refine FormalScheme.GlueData.eq_of_ι_c_app_eq (tateChainInvFormalGlueData R I q hq hI)
    ((Opens.map π.base).obj V) _ _ (fun i => ?_)
  have hfac : ∀ (j : ULift.{u} ℤ) (u : (Q.presheaf.obj (op V))),
      ((((tateChainInvFormalGlueData R I q hq hI).ι j ≫ π).c.app (op V)).hom) u =
        (((tateChainInvFormalGlueData R I q hq hI).ι j).c.app
          (op ((Opens.map π.base).obj V))).hom (((π.c.app (op V)).hom) u) := fun _ _ => rfl
  rw [← hfac, ← hfac]
  have hcm := ι_comp_eq_of_isActionQuotient hq hI h (m := m) (n := i)
    (i.down - m.down) (by omega)
  have hP := congrArg
    (fun φ : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U i ⟶ Q =>
      ((φ.c.app (op V)).hom t = (φ.c.app (op V)).hom t')) hcm
  exact cast hP.symm heq

/-- **`Γ (T_inv/⟨σ⟩)` is a subring of `A = R{x, y}/(x·y − q)`.** The collapse at `V = ⊤`, composed
with `FormalSpectrum.globalSectionsEquiv` (`FormalSchemes.Sections`), which identifies the global
sections of `Spf A` with `A`.

No hypothesis beyond the standing ones, and in particular none on the quotient: whatever
`T_inv/⟨σ⟩` turns out to be — and whether or not it is a formal scheme — its global sections embed
in the ring of one patch. Geometrically this is the Néron 1-gon being covered by the image of a
single component. -/
def globalSectionsToAnnulus (m : ULift.{u} ℤ)
    (π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q) :
    Q.presheaf.obj (op (⊤ : Opens Q)) → annulusAlgebra R I q :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  fun t => FormalSpectrum.globalSectionsEquiv (annulusIdealOfDefinition R I q)
    (((((tateChainInvFormalGlueData R I q hq hI).ι m ≫ π).c.app (op (⊤ : Opens Q))).hom) t)

theorem injective_globalSectionsToAnnulus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ) :
    Function.Injective (globalSectionsToAnnulus hq hI m π) :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  ((FormalSpectrum.globalSectionsEquiv (annulusIdealOfDefinition R I q)).injective).comp
    (injective_c_app_ι_comp_of_isActionQuotient hq hI h m ⊤)

/-- **The ring of the quotient over the image of a saturation is a subring of the model patch's
ring over `tateInvPatchSaturate S`.** The collapse at `V = π '' tateInvSaturate S`, with the source
open computed: `(ι m ≫ π)⁻¹ (π '' tateInvSaturate S) = tateInvPatchSaturate S`, by
`preimage_image_base_tateInvSaturate` (`FormalSchemes.TateInvSaturation`) followed by
`preimage_ι_tateInvSaturate`.

This is goal 1 of the row this file was written for, in its uniqueness half. The existence half —
which sections of `Γ (Spf A, tateInvPatchSaturate S)` arise this way — is **not** proved; see the
module docstring. -/
theorem injective_c_app_tateInvSaturate
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ)
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    (hS : IsOpen S) :
    Function.Injective
      ((((tateChainInvFormalGlueData R I q hq hI).ι m ≫ π).c.app
        (op ⟨⇑π.base '' tateInvSaturate R I q hq hI S,
          isOpen_image_base_tateInvSaturate hq hI h hS⟩)).hom) :=
  injective_c_app_ι_comp_of_isActionQuotient hq hI h m _

/-- **The open the collapse is stated over, identified.** `(ι m ≫ π)⁻¹ (π '' tateInvSaturate S)` is
`tateInvPatchSaturate S` — nothing of `Q` survives in the description of the source ring. -/
theorem preimage_ι_comp_image_base_tateInvSaturate
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι m ≫ π).base ⁻¹'
        (⇑π.base '' tateInvSaturate R I q hq hI S) =
      tateInvPatchSaturate hq hI S := by
  have hbase : ⇑((tateChainInvFormalGlueData R I q hq hI).ι m ≫ π).base =
      ⇑π.base ∘ ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base := rfl
  rw [hbase, Set.preimage_comp, preimage_image_base_tateInvSaturate hq hI h S]
  exact preimage_ι_tateInvSaturate hq hI S m

end Quotient

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The whole patch saturates to the whole chain**, so the collapse at `S = Set.univ` is the
collapse at `V = ⊤`. `tateInvSaturate_univ` (`FormalSchemes.TateInvSaturation`) plus
`Set.preimage_univ`. -/
theorem tateInvPatchSaturate_univ :
    tateInvPatchSaturate hq hI (Set.univ) = Set.univ := by
  unfold tateInvPatchSaturate
  rw [tateInvSaturate_univ hq hI]
  exact Set.preimage_univ

include hq hI in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The chart locus is a proper open of the model patch** whenever `Spf R` is nonempty. It is
the complement form of `tateInvNodeLocus_nonempty` (`FormalSchemes.TateInvNodeLocus`), since
`tateInvNodeLocus` is by definition `(tateInvChartLocus R I q)ᶜ`. So the opens `S` this file's
collapse is stated over are not all `Set.univ`.

That on its own does **not** separate `injective_c_app_tateInvSaturate` from
`injective_globalSectionsToAnnulus`: for that the *image* `π '' tateInvSaturate S` would have to
be a proper open of `Q` too, which does not follow from `S ≠ Set.univ` — the saturation of a
proper open can meet every patch. At `S = tateInvChartLocus R I q` the tree already has it,
`AlgebraicGeometry.exists_notMem_image_base_tateInvSaturate_chartLocus`
(`FormalSchemes.TateInvNodeLocus`), under the same `I ≠ ⊤`. -/
theorem tateInvChartLocus_ne_univ (hItop : I ≠ ⊤) :
    tateInvChartLocus R I q ≠ Set.univ := by
  obtain ⟨z, hz⟩ := tateInvNodeLocus_nonempty R I q hq hI hItop
  intro hc
  exact hz (hc ▸ Set.mem_univ z)

section NonVacuity

/-- **Non-vacuity, as an application.** Every theorem above is conditional on a value of
`CategoryTheory.IsActionQuotient`, and the tree constructs one unconditionally:
`CategoryTheory.actionQuotient` of the `q^ℤ`-action exists for every `(R, I, q)` the chain is
defined for, with `CategoryTheory.isActionQuotient_actionQuotientπ` its witness
(`FormalSchemes.ActionQuotientColimit`).

Instantiated there, `injective_globalSectionsToAnnulus` reads: **the global sections of the
period-`q` Tate quotient form a subring of `A`**, with no hypothesis at all. This is an
instantiation at a specific `Q` and `π`, not a restatement of the general theorem: the general one
quantifies over presentations of the quotient and this one names the coequalizer. -/
theorem injective_globalSectionsToAnnulus_actionQuotient (m : ULift.{u} ℤ) :
    Function.Injective (globalSectionsToAnnulus hq hI m
      (CategoryTheory.actionQuotientπ (tateInvPeriodAction R I q hq hI))) :=
  injective_globalSectionsToAnnulus hq hI
    (CategoryTheory.isActionQuotient_actionQuotientπ _) m

end NonVacuity

end AlgebraicGeometry
