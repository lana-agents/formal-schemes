import FormalSchemes.TateInvNodeChartGlue

set_option linter.style.header false

/-!
# Descent to the period-`q` quotient, over an arbitrary base ring

`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`
(`FormalSchemes.ActionQuotientInvariantSections`) says a section of `X` over `π⁻¹ V` is the
pullback of a section of `X / G` over `V` **iff** it is invariant under every `a g`. It is the last
step of the description of `Γ (T_inv/⟨σ⟩, π V)`, and until the acting group was allowed its own
universe it could not be read at `AlgebraicGeometry.tateInvPeriodAction` over a base ring
`R : Type u`, because that action is by `Multiplicative ℤ`, which is in `Type 0`. This file reads
it there.

## What is here

* `AlgebraicGeometry.exists_actionQuotientπ_c_app_eq_iff_forall_zpow`: **the instantiation.**
  Invariance under the group `Multiplicative ℤ` restated as invariance under `σ ^ k` for every
  integer `k`, which is the form every statement about the chain is written in
  (`AlgebraicGeometry.tateInvShiftAut`).
* `AlgebraicGeometry.exists_actionQuotientπ_c_app_eq_of_const`: **the payoff.** A section of the
  chain over `π⁻¹ V` whose pullbacks to the patches are the *constant* family of one section of
  the model patch descends to the quotient. The invariance it needs is
  `AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`
  (`FormalSchemes.TateInvNodeChartGlue`), which was landed with nothing to consume it.
* `AlgebraicGeometry.existsUnique_actionQuotientπ_c_app_eq_of_isCompatible`: the two halves in
  one — a section `s` of the model patch over `AlgebraicGeometry.tateInvPatchSaturate S` whose
  constant family is compatible determines a **unique** section of the quotient over `V`, and its
  pullbacks to the patches are that family.

## The reindexing, and why it is not free

`AlgebraicGeometry.tateInvPeriodAction_apply` makes `a n` and `σ ^ n.toAdd` the same morphism, so
the two invariance conditions differ only by the bijection `Multiplicative.ofAdd`. The `eqToHom`
transports on the two sides are `eqToHom` of two different *proofs* of the same equality of opens
— `CategoryTheory.preimage_actionQuotientπ_eq` on one side and
`AlgebraicGeometry.eq_map_tateInvShiftAut_zpow` on the other — and are equal by proof irrelevance,
which is why `exists_actionQuotientπ_c_app_eq_of_const` closes without any transport bookkeeping.

## What is *not* proved

The equalizer description of `Γ (T_inv/⟨σ⟩, π V)` as a subring of `Γ (Spf A, tateInvPatchSaturate
S)`, and the ring isomorphism realising it. That is issue 1223's goal 2 and it stays there: this
file supplies the descent the description needs and stops. In particular the compatibility
hypothesis is still `TopCat.Presheaf.IsCompatible` for the transported constant family, on opens
of the chain, and is not translated into the chain's `𝔾m`-inversion transition — see
`FormalSchemes.GlueDataSectionGlue`'s "What this does not do".

Nothing here says the quotient is a formal scheme.
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) still needs a chart at a node image, which is issue
1197's business; a ring is not a chart.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}
variable {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}

/-! ### The instantiation -/

/-- **The sections of the period-`q` quotient are the `σ`-invariant sections**, over a base ring
in an arbitrary universe.

`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall` read at
`AlgebraicGeometry.tateInvPeriodAction`, with the acting group `Multiplicative ℤ` reindexed to
`ℤ` so that the condition is stated in terms of the shift `AlgebraicGeometry.tateInvShiftAut`
itself. The reindexing is the bijection `Multiplicative.ofAdd`; the two morphisms agree by
`AlgebraicGeometry.tateInvPeriodAction_apply`.

No hypothesis on the action: neither freeness nor proper discontinuity is used, and in fact
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction` says the shift does not
have a separating open at every point. That is exactly why the invariant-sections route is the one
available at a node. -/
theorem exists_actionQuotientπ_c_app_eq_iff_forall_zpow
    (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
    (s : ToType ((tateChainInv R I q hq hI).presheaf.obj
      (op ((Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V)))) :
    (∃ t, ((actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.c.app (op V)) t = s) ↔
      ∀ k : ℤ, (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app
          (op ((Opens.map (actionQuotientπ
            (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))) s =
        ((tateChainInv R I q hq hI).presheaf.map (eqToHom (congrArg op
          (preimage_actionQuotientπ_eq (tateInvPeriodAction R I q hq hI) V
            (Multiplicative.ofAdd k))))) s :=
  (exists_actionQuotientπ_c_app_eq_iff_forall (tateInvPeriodAction R I q hq hI) V s).trans
    ⟨fun h k => h (Multiplicative.ofAdd k), fun h n => h (Multiplicative.toAdd n)⟩

/-! ### Descent of a constant patch family -/

/-- **The hypothesis `hV` below is satisfiable, for every open `S` of the model patch.** The image
of the saturation is open (`AlgebraicGeometry.isOpen_image_base_tateInvSaturate`) and its preimage
is the saturation back again (`AlgebraicGeometry.preimage_image_base_tateInvSaturate`), both
`FormalSchemes.TateInvSaturation` and both with **no** hypothesis on the action — which is what
makes them available at a node, where
`AlgebraicGeometry.LocallyRingedSpace.IsProperlyDiscontinuousOn` is not.

The `CategoryTheory.IsActionQuotient` witness is
`CategoryTheory.isActionQuotient_actionQuotientπ`
(`FormalSchemes.ActionQuotientColimit`), so this is an instantiation at a named quotient with
every hypothesis discharged, not a restatement. -/
theorem exists_preimage_eq_tateInvSaturateOpens (hS : IsOpen S) :
    ∃ V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat,
      (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
        tateInvSaturateOpens hq hI hS :=
  ⟨⟨_, isOpen_image_base_tateInvSaturate hq hI (isActionQuotient_actionQuotientπ _) hS⟩,
    Opens.ext (preimage_image_base_tateInvSaturate hq hI (isActionQuotient_actionQuotientπ _) S)⟩

/-- **A section of the chain that is constant on the patches descends to the quotient.** The open
`V` of the quotient is one whose preimage is the saturation of an open `S` of the model patch, and
the section is one whose pullback to every patch is the same `s`.

This is `AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`
(`FormalSchemes.TateInvNodeChartGlue`) fed to
`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`, with the group element reindexed by
`Multiplicative.toAdd` at the point of use rather than through
`exists_actionQuotientπ_c_app_eq_iff_forall_zpow` — the two are interchangeable here and the
direct route is one step shorter. The invariance was landed with nothing able to consume it, being
exactly the hypothesis of a theorem that did not apply at this action; this is the consumption. -/
theorem exists_actionQuotientπ_c_app_eq_of_const (hS : IsOpen S)
    (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (g : (tateChainInv R I q hq hI).presheaf.obj
      (op ((Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V)))
    (hg : ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))).hom g =
      tateInvConstFamily hS hV s i) :
    ∃ t, ((actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.c.app (op V)) t = g :=
  (exists_actionQuotientπ_c_app_eq_iff_forall (tateInvPeriodAction R I q hq hI) V g).mpr
    fun n => c_app_tateInvShiftAut_zpow_eq_of_const hS hV s g hg (Multiplicative.toAdd n)

/-- **A compatible section of the model patch is a section of the quotient, uniquely.** For `V` an
open of `T_inv/⟨σ⟩` whose preimage is the saturation of `S`, and `s` a section of `Spf A` over
`AlgebraicGeometry.tateInvPatchSaturate S` whose constant family is compatible, there is exactly
one section of the quotient over `V` pulling back to `s` on every patch.

The three ingredients: `AlgebraicGeometry.existsUnique_tateInvConstFamily`
(`FormalSchemes.TateInvNodeChartGlue`) glues the constant family to a section `g` of the chain;
`exists_actionQuotientπ_c_app_eq_of_const` descends `g`; and uniqueness is
`AlgebraicGeometry.LocallyRingedSpace.injective_coequalizer_π_c_app`
(`FormalSchemes.ActionQuotientSections`) — a section of the quotient is determined by its pullback
along `π`, which is what `CategoryTheory.IsActionQuotient.injective_c_app`
(`FormalSchemes.ActionQuotientSectionInjective`) generalises to an arbitrary presentation.

Compatibility is the hypothesis of the sheaf axiom on the cover of `π⁻¹ V` by the patch images and
is stated for the transported family, exactly as
`AlgebraicGeometry.FormalScheme.GlueData.exists_ι_c_app_eq_iff_isCompatible`
(`FormalSchemes.GlueDataSectionGlue`) states it; making it concrete in terms of the chain's
transition is issue 1223's remaining piece and is not done here. -/
theorem existsUnique_actionQuotientπ_c_app_eq_of_isCompatible (hS : IsOpen S)
    (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (h : IsCompatible ((tateChainInvFormalGlueData R I q hq hI).gluedFormalScheme).presheaf
      ((tateChainInvFormalGlueData R I q hq hI).ιCover
        ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))
      (fun i => (((tateChainInvFormalGlueData R I q hq hI).ιSectionIso
        ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V) i).hom).hom
          (tateInvConstFamily hS hV s i))) :
    ∃! t, ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))).hom
        (((actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.c.app (op V)) t) =
      tateInvConstFamily hS hV s i := by
  obtain ⟨g, hg, -⟩ := existsUnique_tateInvConstFamily hS hV s h
  obtain ⟨t, ht⟩ := exists_actionQuotientπ_c_app_eq_of_const hS V hV s g hg
  refine ⟨t, fun i => by rw [ht]; exact hg i, fun t' ht' => ?_⟩
  refine LocallyRingedSpace.injective_coequalizer_π_c_app _ _ V ?_
  refine FormalScheme.GlueData.eq_of_ι_c_app_eq (tateChainInvFormalGlueData R I q hq hI) _ _ _
    fun i => ?_
  exact (ht' i).trans ((hg i).symm.trans (congrArg
    (fun z => (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
      (op ((Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))).hom z) ht.symm))

end AlgebraicGeometry
