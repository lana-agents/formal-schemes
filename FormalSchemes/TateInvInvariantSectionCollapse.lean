import FormalSchemes.TateInvSaturation
import FormalSchemes.ActionInvariantExtension

set_option linter.style.header false

/-!
# An invariant section on a saturation is determined by one patch

Issue 1223's goal 1, injectivity half. `AlgebraicGeometry.tateInvSaturate`
(`FormalSchemes.TateInvSaturation`) turns an arbitrary subset `S` of the model patch `Spf A` into
the `σ`-invariant subset `⋃ₘ ιₘ '' S` of the inversion-glued chain `T_inv`. This file proves that a
**`σ`-invariant section of `𝒪_{T_inv}` over that saturation is determined by its restriction to the
single patch image `ι₀ '' S`** — for every open `S`, with no hypothesis on the action.

That last clause is the whole point, and it is why this is not a corollary of what was already on
the tree.

## Why the existing lemma did not apply, and what changed

`AlgebraicGeometry.LocallyRingedSpace.eq_of_isInvariantSection_of_restrict_eq`
(`FormalSchemes.ActionInvariantExtension`) is exactly this statement in general form. Until
2026-08-31 it carried two extra hypotheses, `IsProperlyDiscontinuousOn a U` and `V ⊆ U`, and at the
node locus of this chain those are not merely unproved — they are **false**:
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) says some point of `T_inv` has no separating open
neighbourhood at all, because every open containing a node contains the generic points of both
branches through it and `σ` exchanges them. Issue 1197 records this as the reason the node chart
cannot come from a separating open, and issue 1223 records `exists_invariant_extension` as
unavailable here for the same reason.

**The two hypotheses were never used.** The old proof took its two equalities from the *uniqueness*
clause of `existsUnique_invariantExtension`, which does consume disjointness of the translates —
but only the *existence* clause needs disjointness, and uniqueness of a gluing is the sheaf
separation axiom, which holds for every sheaf. `FormalSchemes.ActionInvariantExtension` now
proves it by `TopCat.Sheaf.eq_of_locally_eq'` over the cover of the saturation by its translates,
and the two hypotheses are gone. `restrict_translate_of_isInvariantSection`, the per-translate
step, never had them.

So the *existence* half of the descent — extending a section of `S` to an invariant one — is still
blocked at a node, and this file does not touch it. The *injectivity* half is not, and that is what
is proved here. Non-vacuity is `not_isProperlyDiscontinuousOn_univ` below, which says in so many
words that the hypothesis the general lemma shed is unavailable on the set this file's `S = univ`
instance uses.

## Main definitions and results

* `AlgebraicGeometry.tateInvPatchOpen`: the `m`-th patch image of an open of the model patch, as
  an **open** of the chain — the form `TopologicalSpace.Opens.map` and the sections API consume,
  where `FormalSchemes.TateInvSaturation` works with bare sets. Its companion, the saturation as
  an open, is `AlgebraicGeometry.tateInvSaturateOpens` of that same file.
* `AlgebraicGeometry.translate_tateInvPatchOpen`: the `n`-th translate of a patch open is a patch
  open, at the index shifted by `n`. This is the cover-shift law `ι_tateInvShiftAut_zpow` read
  through `LocallyRingedSpace.translate`, which is a *preimage*.
* `AlgebraicGeometry.tateInvSaturateOpens_eq_iSup_translate`: the saturation is the supremum of the
  translates of the patch-`0` open — the cover the sheaf axiom is applied to.
* `AlgebraicGeometry.preimage_tateInvSaturateOpens`: a saturation is its own preimage under every
  `σⁿ`, which is the `Opens`-level form of `image_tateInvShiftAut_zpow_tateInvSaturate`.
* `AlgebraicGeometry.eq_of_isInvariantSection_of_restrict_patch_eq`: **the collapse.** Two invariant
  sections over `tateInvSaturateOpens hS` agreeing on `tateInvPatchOpen S ⟨0⟩` are equal.
* `AlgebraicGeometry.exists_forall_not_isProperlyDiscontinuousOn` and
  `AlgebraicGeometry.not_isProperlyDiscontinuousOn_univ`: the non-vacuity, stated as the
  unavailability of the hypothesis that was removed.

## What is *not* proved

* **The converse.** Issue 1223's goal 1 also asks that a section over `S` extend to an invariant
  section over the saturation exactly when it satisfies the overlap condition. That is the
  *existence* half, it is not here, and it is the half that genuinely needs work: with the
  translates overlapping rather than disjoint, `TopCat.Sheaf.existsUnique_gluing_of_disjoint'` does
  not apply and the gluing acquires a compatibility condition on the annulus overlap — which is
  precisely the equalizer condition goal 2 asks to pin down. Nothing here identifies which two maps
  that condition equalises.
* **The ring.** Goal 2 — a `def` for the equalizer subring of `Γ(Spf A, S)` and a ring isomorphism
  to `Γ(Q, π V)` — is untouched. This file stays on the chain and never mentions the quotient's
  structure sheaf.
* **Anything about the quotient's sections directly.** `CategoryTheory.injective_restrictPullback`
  (`FormalSchemes.ActionQuotientSeparatingSections`) is the quotient-side form of this collapse and
  is proved there in general, but it is **not** instantiated at this chain, for a reason worth
  recording rather than working around: that file fixes its group and its space in the *same*
  universe (`variable {G : Type u} … {X : LocallyRingedSpace.{u}}`), while
  `tateInvPeriodAction` has group `Multiplicative ℤ : Type 0` over a chain in the ring's universe
  `u`. Generalising that file needs `Small.{u} G` plus the six coproduct/colimit instance binders
  that `FormalSchemes.ActionQuotientInvariantSections` carries for its own `{G : Type w}`, and
  every consumer of `bijective_restrictPullback` would have to supply them. That is a universe
  generalisation of one file and its cone, not part of this row.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

/-- **A preimage read off an image, for an isomorphism of locally ringed spaces.** The base map of
an iso is a homeomorphism, so `f ⁻¹' (f '' T) = T`; the hypothesis is supplied in the `image` form
because that is the form the cover-shift law `ι_tateInvShiftAut_zpow` produces, while
`LocallyRingedSpace.translate` and `TopologicalSpace.Opens.map` consume preimages.

Stated over abstract locally ringed spaces and instantiated below, as
`FormalSchemes.TateInvOverlapDiscontinuous` does for `image_comp_base`: instantiation is
substitution, so nothing re-elaborates at the chain's concrete types. -/
theorem preimage_base_of_image_eq {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) {T : Set X}
    {U : Set Y} (h : ⇑e.hom.base '' T = U) : ⇑e.hom.base ⁻¹' U = T :=
  h ▸ Set.preimage_image_eq T
    (TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso e)).injective

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}

/-! ### The patch images and the saturation, as opens -/

/-- **The `m`-th patch image of an open of the model patch, as an open of the chain.** Open because
each patch inclusion of the glue datum is an open immersion. -/
def tateInvPatchOpen (hS : IsOpen S) (m : ULift.{u} ℤ) :
    Opens (tateChainInv R I q hq hI).toLocallyRingedSpace.toTopCat :=
  ⟨⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S,
    ((tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion m).base_open.isOpenMap _ hS⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Every patch image sits inside the saturation. The `Opens` form of
`image_ι_subset_tateInvSaturate`. -/
theorem tateInvPatchOpen_le_tateInvSaturateOpens (hS : IsOpen S) (m : ULift.{u} ℤ) :
    tateInvPatchOpen R I q hq hI hS m ≤ tateInvSaturateOpens hq hI hS :=
  image_ι_subset_tateInvSaturate hq hI S m

/-! ### The translates of a patch open -/

/-- **The `n`-th translate of a patch open is a patch open.** `LocallyRingedSpace.translate` is a
*preimage* under `σⁿ`, so the index moves the other way: the translate of the `(m + n)`-th patch
image is the `m`-th. -/
theorem translate_tateInvPatchOpen (hS : IsOpen S) (n : Multiplicative ℤ) (m : ULift.{u} ℤ) :
    LocallyRingedSpace.translate (tateInvPeriodAction R I q hq hI)
        (tateInvPatchOpen R I q hq hI hS ⟨m.down + Multiplicative.toAdd n⟩) n =
      tateInvPatchOpen R I q hq hI hS m := by
  refine Opens.ext ?_
  rw [LocallyRingedSpace.coe_translate, tateInvPeriodAction_apply]
  exact preimage_base_of_image_eq _ (image_ι_tateInvShiftAut_zpow hq hI _ m S)

/-- **The saturation is the supremum of the translates of the patch-`0` open.** This is the open
cover the sheaf separation axiom is applied to in the collapse below. The reindexing is along
`n ↦ -n`, `translate` being a preimage. -/
theorem tateInvSaturateOpens_eq_iSup_translate (hS : IsOpen S) :
    tateInvSaturateOpens hq hI hS =
      ⨆ n : Multiplicative ℤ, LocallyRingedSpace.translate (tateInvPeriodAction R I q hq hI)
        (tateInvPatchOpen R I q hq hI hS ⟨0⟩) n := by
  refine Opens.ext ?_
  have hstep : ∀ n : Multiplicative ℤ,
      LocallyRingedSpace.translate (tateInvPeriodAction R I q hq hI)
          (tateInvPatchOpen R I q hq hI hS ⟨0⟩) n =
        tateInvPatchOpen R I q hq hI hS ⟨-Multiplicative.toAdd n⟩ := fun n => by
    have hidx : (⟨(-Multiplicative.toAdd n) + Multiplicative.toAdd n⟩ : ULift.{u} ℤ) = ⟨0⟩ :=
      ULift.down_injective (by change (-Multiplicative.toAdd n) + Multiplicative.toAdd n = 0; omega)
    exact hidx ▸ translate_tateInvPatchOpen R I q hq hI hS n ⟨-Multiplicative.toAdd n⟩
  rw [iSup_congr hstep, Opens.coe_iSup]
  exact (Set.iUnion_congr_of_surjective
    (fun n : Multiplicative ℤ => (⟨-Multiplicative.toAdd n⟩ : ULift.{u} ℤ))
    (fun m => ⟨Multiplicative.ofAdd (-m.down), ULift.down_injective (by simp)⟩)
    fun _ => rfl).symm

/-- **A saturation is its own preimage under every `σⁿ`.** The `Opens` form of
`image_tateInvShiftAut_zpow_tateInvSaturate`, which is the invariance hypothesis
`LocallyRingedSpace.eq_of_isInvariantSection_of_restrict_eq` needs in order for
`IsInvariantSection` to be stated at all. -/
theorem preimage_tateInvSaturateOpens (hS : IsOpen S) (k : Multiplicative ℤ) :
    tateInvSaturateOpens hq hI hS =
      (Opens.map (tateInvPeriodAction R I q hq hI k).hom.toShHom.hom.base).obj
        (tateInvSaturateOpens hq hI hS) := by
  refine (Opens.ext ?_).symm
  exact preimage_base_of_image_eq (tateInvShiftAut R I q hq hI ^ Multiplicative.toAdd k)
    (image_tateInvShiftAut_zpow_tateInvSaturate hq hI (Multiplicative.toAdd k) S)

/-! ### The collapse -/

/-- **An invariant section on a saturation is determined by its restriction to one patch.** Issue
1223's goal 1, injectivity half, for an arbitrary open `S` of the model patch — **including one
whose saturation contains nodes**, which is the case the row is for.

It is the general
`AlgebraicGeometry.LocallyRingedSpace.eq_of_isInvariantSection_of_restrict_eq` instantiated at the
three facts above; the substance is that the general lemma no longer asks for proper discontinuity,
which this chain provably does not have (`not_isProperlyDiscontinuousOn_univ` below). -/
theorem eq_of_isInvariantSection_of_restrict_patch_eq (hS : IsOpen S)
    {r₁ r₂ : ToType ((tateChainInv R I q hq hI).toLocallyRingedSpace.presheaf.obj
      (op (tateInvSaturateOpens hq hI hS)))}
    (hr₁ : LocallyRingedSpace.IsInvariantSection (tateInvPeriodAction R I q hq hI) r₁)
    (hr₂ : LocallyRingedSpace.IsInvariantSection (tateInvPeriodAction R I q hq hI) r₂)
    (hres : (tateChainInv R I q hq hI).toLocallyRingedSpace.presheaf.map
        (homOfLE (tateInvPatchOpen_le_tateInvSaturateOpens R I q hq hI hS ⟨0⟩)).op r₁ =
      (tateChainInv R I q hq hI).toLocallyRingedSpace.presheaf.map
        (homOfLE (tateInvPatchOpen_le_tateInvSaturateOpens R I q hq hI hS ⟨0⟩)).op r₂) :
    r₁ = r₂ :=
  LocallyRingedSpace.eq_of_isInvariantSection_of_restrict_eq
    (tateInvSaturateOpens_eq_iSup_translate R I q hq hI hS)
    (tateInvPatchOpen_le_tateInvSaturateOpens R I q hq hI hS ⟨0⟩)
    (preimage_tateInvSaturateOpens R I q hq hI hS) hr₁ hr₂ hres

/-! ### Non-vacuity: the hypothesis that was removed is not available here

The collapse above would be worth nothing if `IsProperlyDiscontinuousOn` held on the sets it is
applied to, since then the pre-2026-08-31 form of the general lemma would already have covered it.
It does not, and the two statements below say so. -/

include hq hI in
/-- **Some point of the chain lies in no separating open.** The contrapositive of
`not_isFreeProperlyDiscontinuous_tateInvPeriodAction`, whose refutation supplies a node as the
witness: every open containing a node meets both branches through it, and `σ` exchanges them. -/
theorem exists_forall_not_isProperlyDiscontinuousOn (hItop : I ≠ ⊤) :
    ∃ x : (tateChainInv R I q hq hI).toLocallyRingedSpace,
      ∀ U : Set (tateChainInv R I q hq hI).toLocallyRingedSpace, IsOpen U → x ∈ U →
        ¬ LocallyRingedSpace.IsProperlyDiscontinuousOn (tateInvPeriodAction R I q hq hI) U := by
  by_contra hcon
  push Not at hcon
  exact not_isFreeProperlyDiscontinuous_tateInvPeriodAction R I q hI hq hItop fun x => hcon x

include hq hI in
/-- **The whole chain is not a separating open**, whenever `I` is a proper ideal. So at `S = univ`
— where `tateInvSaturate S` is the whole chain (`tateInvSaturate_univ`) and the collapse above
applies unchanged — the general lemma's discarded `IsProperlyDiscontinuousOn` hypothesis is not
merely unproved at `U = Set.univ` but false. That is the sense in which removing it was necessary
and not a tidy-up.

**Two things this does not say.** The other discarded hypothesis, `V ⊆ U`, is not refuted by
anything here; at `U = Set.univ` it is trivially true, and only `IsProperlyDiscontinuousOn` is at
issue. And this refutes that hypothesis at `U = Set.univ` alone, not at every `U` containing the
patch open — for the latter one would have to place the witness of
`exists_forall_not_isProperlyDiscontinuousOn` inside `tateInvPatchOpen S ⟨0⟩`, which is not proved
here. -/
theorem not_isProperlyDiscontinuousOn_univ (hItop : I ≠ ⊤) :
    ¬ LocallyRingedSpace.IsProperlyDiscontinuousOn (tateInvPeriodAction R I q hq hI)
      (Set.univ : Set (tateChainInv R I q hq hI).toLocallyRingedSpace) := by
  obtain ⟨x, hx⟩ := exists_forall_not_isProperlyDiscontinuousOn R I q hq hI hItop
  exact hx Set.univ isOpen_univ (Set.mem_univ x)

end AlgebraicGeometry
