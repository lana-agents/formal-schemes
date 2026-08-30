import FormalSchemes.TateInvNodeChartOverlap
import FormalSchemes.TateInvQuotientSections

set_option linter.style.header false

/-!
# `Γ (T_inv/⟨σ⟩, V)` as a subring of `Γ (Spf A, tateInvPatchSaturate S)`

For `S` an open of the model patch `Spf A` and `V` an open of the quotient whose preimage is the
saturation of `S`, this file identifies the ring of sections of the quotient over `V` with a
subring of the ring of sections of the **single patch** over
`AlgebraicGeometry.tateInvPatchSaturateOpens`, cut out by the overlap condition
`AlgebraicGeometry.IsTateInvOverlapCompatible` of `FormalSchemes.TateInvNodeChartOverlap`. Nothing
about `T_inv`, its topology, or the quotient survives in the description of the subring.

## The one thing that was missing

`AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`
(`FormalSchemes.TateInvNodeChartGlue`) says a section of the chain whose pullbacks to the patches
are a **constant** family is `σ`-invariant. Its converse was not on the tree, and it is what turns
the `ExistsUnique` of `AlgebraicGeometry.existsUnique_actionQuotientπ_c_app_eq_of_isCompatible`
(`FormalSchemes.TateInvQuotientSections`) into a bijection: without it, one knows that every
compatible `s` comes from a unique section of the quotient, but not that every section of the
quotient arises this way.

`tateInvConstFamily_tateInvPatchSection` is that converse, and its proof is
`c_app_tateInvShiftAut_zpow_eq_of_const`'s own computation run backwards. The section of the
patch it produces is named, not merely asserted to exist: `tateInvPatchSection`.

## Main results

* `AlgebraicGeometry.ι_tateInvShiftAut_zpow_of_eq`: the shift factorisation
  `ι i ≫ σ ^ k = ι j` at a pair of indices with `i.down + k = j.down`, stated over a pair with a
  hypothesis because the type of `ι j` depends on `j`.
* `AlgebraicGeometry.tateInvPatchSection` and
  `AlgebraicGeometry.tateInvConstFamily_tateInvPatchSection`: **the converse.** A `σ`-invariant
  section of the chain over a saturation is the constant family of a named section of the model
  patch.
* `AlgebraicGeometry.tateInvConstFamily_injective`: and that section is determined by the family.
* `AlgebraicGeometry.c_app_tateInvShiftAut_zpow_actionQuotientπ`: the pullback along `π` of a
  section of the quotient is `σ`-invariant. This is one direction of
  `AlgebraicGeometry.exists_actionQuotientπ_c_app_eq_iff_forall_zpow` and needs no hypothesis
  beyond the existence of the section it is pulled back from.
* `AlgebraicGeometry.tateInvChartSection`, `AlgebraicGeometry.tateInvChartSection_injective` and
  `AlgebraicGeometry.exists_tateInvChartSection_eq_of_isTateInvOverlapCompatible`: **the
  bijection.** `Γ (Q, V)` maps injectively to `Γ (Spf A, tateInvPatchSaturate S)`, the image is
  contained in the sections satisfying the overlap condition
  (`AlgebraicGeometry.isTateInvOverlapCompatible_tateInvChartSection`), and every such section is
  in the image.
* `AlgebraicGeometry.tateInvChartSubring`: **the ring.** The overlap condition is, at each pair of
  indices, an equation between two ring homomorphisms out of
  `Γ (Spf A, tateInvPatchSaturateOpens hq hI hS)`, so it cuts out an intersection of
  `RingHom.eqLocus`s. `AlgebraicGeometry.mem_tateInvChartSubring_iff` identifies its membership
  with `IsTateInvOverlapCompatible`.
* `AlgebraicGeometry.tateInvChartRingEquiv`: **the ring isomorphism**
  `Γ (Q, V) ≃+* tateInvChartSubring hS`, and
  `AlgebraicGeometry.exists_tateInvChartRingEquiv`, which exhibits it at an open `V` produced for
  every open `S` rather than assumed.

## What is *not* proved

**The condition still quantifies over all pairs of indices.** Cutting `∀ i j` down to the diagonal
and the adjacent pairs, and naming the two legs through `annulusOverlapChart`,
`annulusOverlapChartY` and the `𝔾m`-inversion transition, is untouched here — see
`FormalSchemes.TateInvNodeChartOverlap`'s "What is left", which is unaffected by this file.

**Nothing here says the quotient is a formal scheme.**
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) still needs a chart at a node image: an adic
structure on this ring and an open immersion out of its formal spectrum. A ring is not a chart.

**No element of the subring is exhibited beyond `0` and `1`**, which are in it because it is a
`Subring`. Whether it is strictly smaller than `Γ (Spf A, tateInvPatchSaturate S)` — equivalently,
whether the overlap condition is a genuine restriction — is not decided here; the condition is at
least not *definitionally* trivial, since it is not closed by `rfl`.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon;
  the affine chart at its node is `Spec` of the subring of functions agreeing at the two
  preimages, which is the ring named here.
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
variable {W : Opens (tateChainInv R I q hq hI).toLocallyRingedSpace}

/-! ### The shift factorisation, at a pair of indices -/

/-- **The `k`-th shift carries the `i`-th patch inclusion to the `j`-th**, whenever
`i.down + k = j.down`. `AlgebraicGeometry.ι_tateInvShiftAut_zpow` states this with `j` spelled out
as `⟨i.down + k⟩`, which is the wrong shape for a consumer that has an index of its own: rewriting
`⟨i.down + k⟩` into `j` is not available, because the type of `ι j` depends on `j` and the motive
is ill-typed.

Carrying the index equation as a hypothesis and opening with
`ULift.down_injective` is the cluster's recorded idiom for that, and it is what makes the
specialisation `i := ⟨0⟩`, `k := j.down` usable below — `zero_add` discharges the hypothesis. -/
theorem ι_tateInvShiftAut_zpow_of_eq (k : ℤ) (i j : ULift.{u} ℤ) (h : i.down + k = j.down) :
    (tateChainInvFormalGlueData R I q hq hI).ι i ≫ ((tateInvShiftAut R I q hq hI) ^ k).hom =
      (tateChainInvFormalGlueData R I q hq hI).ι j := by
  obtain rfl : (⟨i.down + k⟩ : ULift.{u} ℤ) = j := ULift.down_injective h
  exact ι_tateInvShiftAut_zpow R I q hq hI k i

/-! ### The section of the model patch cut out by a section of the chain -/

/-- **The section of the model patch a section of the chain restricts to**, read on the patch
`⟨0⟩` and transported along `AlgebraicGeometry.map_ι_of_eq_tateInvSaturateOpens`.

The transport is along an equality of opens, not an inclusion, so nothing is lost. No invariance
is required for the definition: it is `tateInvConstFamily_tateInvPatchSection` that needs it, to
say that the *other* patches see the same section. -/
def tateInvPatchSection (hS : IsOpen S) (hW : W = tateInvSaturateOpens hq hI hS)
    (g : (tateChainInv R I q hq hI).presheaf.obj (op W)) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)) :=
  ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
    (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens hS hW ⟨(0 : ℤ)⟩)))).hom
    ((((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).c.app (op W)).hom g)

/-- **A `σ`-invariant section of the chain is constant on the patches**, the converse of
`AlgebraicGeometry.c_app_tateInvShiftAut_zpow_eq_of_const`
(`FormalSchemes.TateInvNodeChartGlue`) and the one fact this file's description of `Γ (Q, V)` needs
that was not already on the tree.

The proof is the forward one run backwards. `ι_tateInvShiftAut_zpow_of_eq` factors `ι i` as
`ι ⟨0⟩ ≫ σ ^ i.down`, so `AlgebraicGeometry.LocallyRingedSpace.c_app_comp_of_eq`
(`FormalSchemes.ActionInvariantExtension`) turns the `i`-th pullback of `g` into the `⟨0⟩`-th
pullback of `(σ ^ i.down)^* g`; the invariance hypothesis replaces that by a transport of `g`, and
`AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom`
(`FormalSchemes.ActionQuotientInvariantSections`) moves the transport out past the pullback. What
is left is two transports on each side between the same pair of opens, and
`AlgebraicGeometry.LocallyRingedSpace.presheaf_map_comp_apply` together with
`AlgebraicGeometry.LocallyRingedSpace.presheaf_map_congr`
(`FormalSchemes.ActionInvariantExtension`) collapses both without naming either.

Every step is chained with `Eq.trans` and `congrArg` rather than `rw`: the hypothesis and the goal
reach the same `c`-component through `CommRingCat.Hom.hom` and through
`ConcreteCategory.hom` respectively, and the two spellings print identically. -/
theorem tateInvConstFamily_tateInvPatchSection (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (g : (tateChainInv R I q hq hI).presheaf.obj (op W))
    (hinv : ∀ k : ℤ, (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app (op W)) g =
      (tateChainInv R I q hq hI).presheaf.map
        (eqToHom (congrArg op (eq_map_tateInvShiftAut_zpow hS hW k))) g)
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
      tateInvConstFamily hS hW (tateInvPatchSection hS hW g) i := by
  have hphi : (tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩ ≫
      ((tateInvShiftAut R I q hq hI) ^ i.down).hom =
      (tateChainInvFormalGlueData R I q hq hI).ι i :=
    ι_tateInvShiftAut_zpow_of_eq i.down ⟨(0 : ℤ)⟩ i (zero_add _)
  have hL := LocallyRingedSpace.c_app_comp_of_eq
    ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩)
    ((tateInvShiftAut R I q hq hI) ^ i.down).hom hphi.symm W g
  have hc := AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom
    ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).toShHom.hom
    (eq_map_tateInvShiftAut_zpow hS hW i.down) g
  refine hL.trans ?_
  refine Eq.trans (congrArg _ (congrArg _ (hinv i.down))) ?_
  refine Eq.trans (congrArg _ hc) ?_
  simp only [tateInvConstFamily, tateInvPatchSection]
  exact ((LocallyRingedSpace.presheaf_map_comp_apply _ _ _ _).trans
    (ConcreteCategory.congr_hom (LocallyRingedSpace.presheaf_map_congr _ _ _) _)).trans
    (LocallyRingedSpace.presheaf_map_comp_apply _ _ _ _).symm

/-- **The constant family determines the section it is constant at.** `tateInvConstFamily` is a
transport along an equality of opens, so it is injective at each index; this is
`AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff` (`FormalSchemes.ActionQuotientSections`)
with the same equality on both sides, which leaves a transport along a proof of `A = A`. -/
theorem tateInvConstFamily_injective (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    Function.Injective (fun s => tateInvConstFamily hS hW s i) := by
  intro s s' h
  have hkey := (AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff _
    (map_ι_of_eq_tateInvSaturateOpens hS hW i).symm
    (map_ι_of_eq_tateInvSaturateOpens hS hW i).symm s s').1 h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hkey
  exact hkey

/-! ### At the quotient -/

section Quotient

variable (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)

/-- **A section pulled back along `π` is `σ`-invariant.** The easy direction of
`AlgebraicGeometry.exists_actionQuotientπ_c_app_eq_iff_forall_zpow`
(`FormalSchemes.TateInvQuotientSections`), applied to the witness `t` itself.

The transport on the right is `AlgebraicGeometry.eq_map_tateInvShiftAut_zpow` where that theorem's
is `CategoryTheory.preimage_actionQuotientπ_eq`: two different *proofs* of the same equality of
opens, equal by proof irrelevance, so no bookkeeping is needed to pass between them. -/
theorem c_app_tateInvShiftAut_zpow_actionQuotientπ (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) (k : ℤ) :
    (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V)))
        (((actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.c.app (op V)) t) =
      (tateChainInv R I q hq hI).presheaf.map
        (eqToHom (congrArg op (eq_map_tateInvShiftAut_zpow hS hV k)))
        (((actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.c.app (op V)) t) :=
  (exists_actionQuotientπ_c_app_eq_iff_forall_zpow V _).1 ⟨t, rfl⟩ k

/-- **The section of the model patch attached to a section of the quotient**: pull back along `π`,
restrict to the patch `⟨0⟩`, transport. This is the map the ring isomorphism below is built from,
and `tateInvChartSectionHom` is the same map as a `RingHom`. -/
def tateInvChartSection (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)) :=
  tateInvPatchSection hS hV
    ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app (op V))).hom t)

/-- **Every patch sees `π^* t` as the same section.** `tateInvConstFamily_tateInvPatchSection` fed
the invariance of `c_app_tateInvShiftAut_zpow_actionQuotientπ`. -/
theorem tateInvConstFamily_tateInvChartSection (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V))
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))).hom
        ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app (op V))).hom t) =
      tateInvConstFamily hS hV (tateInvChartSection V hS hV t) i :=
  tateInvConstFamily_tateInvPatchSection hS hV _
    (c_app_tateInvShiftAut_zpow_actionQuotientπ V hS hV t) i

/-- **The image of the map satisfies the overlap condition.** `π^* t` is a section of the chain
whose patch family is the constant family of `tateInvChartSection V hS hV t`, so
`AlgebraicGeometry.exists_tateInvConstFamily_iff_tateInvOverlapCompatible`
(`FormalSchemes.TateInvNodeChartOverlap`) applies to it. -/
theorem isTateInvOverlapCompatible_tateInvChartSection (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) :
    IsTateInvOverlapCompatible hS (tateInvChartSection V hS hV t) :=
  (exists_tateInvConstFamily_iff_tateInvOverlapCompatible hS hV _).1
    ⟨_, tateInvConstFamily_tateInvChartSection V hS hV t⟩

/-- **A section of the quotient is determined by the section of the patch it restricts to.** Two
sections with the same restriction have the same constant family, hence the same pullback along
`π` by `AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq`
(`FormalSchemes.GlueDataSectionExt`), hence are equal by
`AlgebraicGeometry.LocallyRingedSpace.injective_coequalizer_π_c_app`
(`FormalSchemes.ActionQuotientSections`). -/
theorem tateInvChartSection_injective (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS) :
    Function.Injective (tateInvChartSection V hS hV) := by
  intro t t' h
  refine LocallyRingedSpace.injective_coequalizer_π_c_app _ _ V ?_
  refine FormalScheme.GlueData.eq_of_ι_c_app_eq (tateChainInvFormalGlueData R I q hq hI) _ _ _
    fun i => ?_
  refine (tateInvConstFamily_tateInvChartSection V hS hV t i).trans ?_
  refine Eq.trans ?_ (tateInvConstFamily_tateInvChartSection V hS hV t' i).symm
  exact congrArg (fun z => tateInvConstFamily hS hV z i) h

/-- **Every section of the patch satisfying the overlap condition is in the image.**
`AlgebraicGeometry.existsUnique_actionQuotientπ_c_app_eq_of_isCompatible`
(`FormalSchemes.TateInvQuotientSections`) produces the section of the quotient, its hypothesis
being supplied by the two `iff`s of `FormalSchemes.TateInvNodeChartOverlap` and
`FormalSchemes.GlueDataOverlapCompat`; `tateInvConstFamily_injective` then identifies the section
of the patch it restricts to with `s`. -/
theorem exists_tateInvChartSection_eq_of_isTateInvOverlapCompatible (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (h : IsTateInvOverlapCompatible hS s) :
    ∃ t, tateInvChartSection V hS hV t = s := by
  obtain ⟨t, ht, -⟩ := existsUnique_actionQuotientπ_c_app_eq_of_isCompatible hS V hV s
    ((FormalScheme.GlueData.isCompatible_iff_isOverlapCompatible _ _ _).2
      ((isOverlapCompatible_tateInvConstFamily_iff hS hV s).2 h))
  refine ⟨t, tateInvConstFamily_injective hS hV ⟨(0 : ℤ)⟩ ?_⟩
  exact (tateInvConstFamily_tateInvChartSection V hS hV t ⟨(0 : ℤ)⟩).symm.trans (ht ⟨(0 : ℤ)⟩)

/-! ### The ring -/

/-- **The equalizer subring.** At each pair of indices the overlap condition
`AlgebraicGeometry.IsTateInvOverlapCompatible` is an equation between the values of two **ring
homomorphisms** out of `Γ (Spf A, tateInvPatchSaturateOpens hq hI hS)` — the left leg
`f i j` on one side, and the right leg `t i j ≫ f j i` followed by the transport of
`AlgebraicGeometry.map_f_tateInvPatchSaturateOpens` on the other. So it cuts out an intersection
of `RingHom.eqLocus`s, and that intersection is a `Subring` for free.

This is the equalizer that issue 1223 asks for. It is stated as a `Subring` rather than as a
categorical equalizer because both legs really are ring homomorphisms and nothing downstream wants
a limit cone. -/
def tateInvChartSubring (hS : IsOpen S) :
    Subring ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :=
  ⨅ i, ⨅ j, RingHom.eqLocus
    ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j).c.app
      (op (tateInvPatchSaturateOpens hq hI hS))).hom)
    ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V
        (i, j)).presheaf.map
      (eqToHom (congrArg op (map_f_tateInvPatchSaturateOpens hS i j)))).hom.comp
      ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).c.app
        (op (tateInvPatchSaturateOpens hq hI hS))).hom))

/-- **Membership in the subring is the overlap condition.** `Subring.mem_iInf` and
`RingHom.mem_eqLocus` unfold the definition; the two sides then differ only by the composition of
the right leg with its transport, which is definitional. -/
theorem mem_tateInvChartSubring_iff (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    s ∈ tateInvChartSubring hS ↔ IsTateInvOverlapCompatible hS s := by
  simp only [tateInvChartSubring, Subring.mem_iInf, RingHom.mem_eqLocus,
    IsTateInvOverlapCompatible]
  exact Iff.rfl

/-- **`tateInvChartSection` as a ring homomorphism.** It is the composite of three `c`-components
and restriction maps, each of which is a morphism of `CommRingCat`, so there is nothing to check;
`tateInvChartSectionHom_apply` records that it is the same map. -/
def tateInvChartSectionHom (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) →+*
      ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI hS))) :=
  (((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
      (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens hS hV ⟨(0 : ℤ)⟩)))).hom).comp
    (((((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).c.app
        (op ((Opens.map (actionQuotientπ
          (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V))).hom).comp
      (((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app (op V)).hom))

@[simp]
theorem tateInvChartSectionHom_apply (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) :
    tateInvChartSectionHom V hS hV t = tateInvChartSection V hS hV t :=
  rfl

/-- **`Γ (T_inv/⟨σ⟩, V) ≅ tateInvChartSubring hS`, as rings.** This is issue 1223's goal 2: the
ring of sections of the period-`q` quotient over an open whose preimage is the saturation of `S`
is the subring of `Γ (Spf A, tateInvPatchSaturate S)` cut out by the overlap condition.

Injectivity is `tateInvChartSection_injective`, surjectivity is
`exists_tateInvChartSection_eq_of_isTateInvOverlapCompatible`, and the codomain restriction is
`isTateInvOverlapCompatible_tateInvChartSection`. No hypothesis on `S`, on the action, or on the
quotient beyond the chain's standing ones. -/
def tateInvChartRingEquiv (hS : IsOpen S)
    (hV : (Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
      tateInvSaturateOpens hq hI hS) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
      tateInvChartSubring (hq := hq) (hI := hI) hS :=
  RingEquiv.ofBijective
    ((tateInvChartSectionHom V hS hV).codRestrict (tateInvChartSubring hS) fun t =>
      (mem_tateInvChartSubring_iff hS _).2
        (isTateInvOverlapCompatible_tateInvChartSection V hS hV t))
    ⟨fun a b h => tateInvChartSection_injective V hS hV (congrArg Subtype.val h), fun z => by
      obtain ⟨t, ht⟩ := exists_tateInvChartSection_eq_of_isTateInvOverlapCompatible V hS hV z.1
        ((mem_tateInvChartSubring_iff hS _).1 z.2)
      exact ⟨t, Subtype.ext ht⟩⟩

end Quotient

/-- **The isomorphism is not conditioned on an unexhibited open.** For *every* open `S` of the
model patch there is an open `V` of the quotient whose preimage is the saturation of `S`, by
`AlgebraicGeometry.exists_preimage_eq_tateInvSaturateOpens`
(`FormalSchemes.TateInvQuotientSections`), which needs no hypothesis on the action — which is what
makes it available at a node, where
`AlgebraicGeometry.LocallyRingedSpace.IsProperlyDiscontinuousOn` is not. -/
theorem exists_tateInvChartRingEquiv (hS : IsOpen S) :
    ∃ (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
      (_ : (Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
          tateInvSaturateOpens hq hI hS),
      Nonempty (((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
        tateInvChartSubring (hq := hq) (hI := hI) hS) :=
  let ⟨V, hV⟩ := exists_preimage_eq_tateInvSaturateOpens (hq := hq) (hI := hI) hS
  ⟨V, hV, ⟨tateInvChartRingEquiv V hS hV⟩⟩

end AlgebraicGeometry
