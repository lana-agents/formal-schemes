import FormalSchemes.TateInvNodeChartOverlap

set_option linter.style.header false

/-!
# The chain's overlap condition lives on the adjacent pairs

`AlgebraicGeometry.IsTateInvOverlapCompatible` (`FormalSchemes.TateInvNodeChartOverlap`) is the
condition on a section `s` of the model patch that makes its constant family glue to a section of
the chain: for **every** pair `i j`, the two legs `f i j` and `t i j ≫ f j i` out of the overlap
`V (i, j)` carry `s` to the same section. This file shows that all but the adjacent pairs are
automatic, so the quantifier runs over `j - i = ±1` alone.

## The two cases that carry no content

* **The diagonal.** `V (i, i)` is the patch itself and `CategoryTheory.GlueData.t_id` makes
  `t i i` the identity, so the two legs are *the same morphism* and the condition is an instance
  of `AlgebraicGeometry.LocallyRingedSpace.c_app_eq_of_hom_eq`. Note `f i i` is **not** the
  identity — `CategoryTheory.GlueData'.f'` is `if h : i = j then eqToHom (dif_pos h) else …`, so on
  the diagonal it is an `eqToHom` — but that does not matter, because the two legs are compared
  with each other and not with `𝟙`.
* **The far pairs.** `AlgebraicGeometry.tateV_far` (`FormalSchemes.TateChainGlue`) makes
  `V (i, j)` the empty locally ringed space when `j - i ∉ {1, -1}` and `i ≠ j`, and sections over an
  empty space are a subsingleton, so the two sides are equal for want of anything to distinguish
  them. That is `AlgebraicGeometry.LocallyRingedSpace.subsingleton_presheaf_obj_of_isEmpty`, proved
  here for an arbitrary locally ringed space with empty carrier: on such a space every open is `⊥`,
  and the sheaf axiom over the empty cover makes `Γ (X, ⊥)` terminal. **No property of
  `LocallyRingedSpace.empty` is used** — in particular not that its presheaf is the constant
  functor at `PUnit` — so the lemma applies to `V (i, j)`, which is `∅` only up to an equality of
  spaces.

## What is here

* `AlgebraicGeometry.LocallyRingedSpace.subsingleton_presheaf_obj_of_isEmpty`: sections of a
  locally ringed space with empty carrier form a subsingleton, over every open.
* `AlgebraicGeometry.LocallyRingedSpace.c_app_eq_of_hom_eq`: two equal morphisms have equal
  `c`-components, up to the `eqToHom` between the two spellings of the preimage.
* `AlgebraicGeometry.LocallyRingedSpace.c_app_eq_iff_of_eqToHom_comp` and
  `AlgebraicGeometry.LocallyRingedSpace.opens_map_eqToHom_comp_base_inj`: **the tool that makes the
  second half work.** An `eqToHom` between two *spaces* that prefixes both sides of an equation of
  sections may be cancelled, rather than pushed through a `c`-component.
* `AlgebraicGeometry.tateChainInv_V_of_ne`, `AlgebraicGeometry.isEmpty_tateChainInv_V_of_far`,
  `AlgebraicGeometry.tateChainInv_V_forward`, `AlgebraicGeometry.tateChainInv_V_backward`: the
  chain's overlap object off the diagonal is `AlgebraicGeometry.tateV` — empty away from the band,
  and the `x`- or `y`-chart domain on it.
* `AlgebraicGeometry.tateChainInv_f_forward`,
  `AlgebraicGeometry.tateChainInv_t_comp_f_forward` and their backward mirrors: **both legs of an
  adjacent pair factor through the same isomorphism of spaces**, as the `x`-chart and as the
  `𝔾m`-inversion transition followed by the `y`-chart.
* `AlgebraicGeometry.IsTateInvOverlapCompatibleAt`: the condition at one pair, with
  `AlgebraicGeometry.isTateInvOverlapCompatible_iff_forall` identifying the conjunction of these
  with `IsTateInvOverlapCompatible`.
* `AlgebraicGeometry.isTateInvOverlapCompatibleAt_self`,
  `AlgebraicGeometry.isTateInvOverlapCompatibleAt_of_far`: the two automatic cases.
* `AlgebraicGeometry.isTateInvOverlapCompatible_iff_adjacent`: **the first reduction.** The
  condition is the conjunction of its instances at `j - i = 1` and `j - i = -1`.
* `AlgebraicGeometry.IsTateInvChartCompatibleForward`,
  `AlgebraicGeometry.IsTateInvChartCompatibleBackward` and
  `AlgebraicGeometry.isTateInvOverlapCompatible_iff_charts`: **the second reduction.** Those two
  families of instances each say *one* thing, and the whole condition is the pair of equations

  > `s` read on the `x`-chart equals `s` read through the `𝔾m`-inversion transition on the
  > `y`-chart, and conversely.

  Neither *morphism* mentions `T_inv` or its glue datum. The **open** they are read over,
  `AlgebraicGeometry.tateInvPatchSaturateOpens`, still does: it is defined as the preimage under
  `ι ⟨0⟩` of a saturation inside the chain, and no chain-free description of it is on the tree. So
  what is eliminated here is the glue datum from the two *legs*, not from the statement.
* `AlgebraicGeometry.exists_tateInvConstFamily_iff_adjacent` and
  `AlgebraicGeometry.exists_tateInvShiftAut_zpow_invariant_of_adjacent`: the two consequences of
  `FormalSchemes.TateInvNodeChartOverlap` restated over the reduced quantifier.
* `AlgebraicGeometry.isTateInvOverlapCompatible_one`: **non-vacuity.** The unit section satisfies
  the condition, so the statements above are not about an empty set.

## The step that was expected to block this, and did not

`FormalSchemes.TateInvNodeChartOverlap` records that `AlgebraicGeometry.tateF` presents a leg as
`eqToHom (tateV_forward …) ≫ annulusOverlapChart` with the `eqToHom` between two **locally ringed
spaces**, and that transporting a section along an equality of spaces is a step this tree has not
taken. That remains true and no such transport is performed here. What makes the second reduction
possible instead is that **both** legs of an adjacent pair carry the *same* `eqToHom` prefix, so the
comparison between them never has to cross it: `c_app_eq_iff_of_eqToHom_comp` substitutes the
equality away and leaves an equation between the charts. The corresponding cancellation on opens is
`opens_map_eqToHom_comp_base_inj`.

## What is left

The two chart conditions are stated through `annulusChartTransitionInvSpf`, the
`𝔾m`-inversion transition as a morphism of formal spectra. Reading them in the *coordinates* of
`FormalSchemes.TateChartTransitionInvAlgEq` — which is what would decide whether the condition is
a genuine restriction — is not done here.

What *is* done elsewhere: `AlgebraicGeometry.tateInvChartAnnulusSubring`
(`FormalSchemes.TateInvChartAnnulusRing`) packages the two conditions as an infimum of two
`RingHom.eqLocus`s and identifies it with `AlgebraicGeometry.tateInvChartSubring`, the equalizer
description of `Γ (T_inv/⟨σ⟩, V)` that `FormalSchemes.TateInvQuotientChartRing` built over the
unreduced condition.

Nothing here descends to the quotient `T_inv/⟨σ⟩`; that is
`FormalSchemes.TateInvQuotientSections`.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **Sections of a space with empty carrier form a subsingleton.** On such a space every open is
`⊥`, and `TopCat.Sheaf.isTerminalOfEqEmpty` — the sheaf axiom read on the empty cover — makes
`Γ (X, ⊥)` a terminal object of `CommRingCat`, hence the zero ring
(`CommRingCat.subsingleton_of_isTerminal`).

Stated for an arbitrary `X` with `IsEmpty X` rather than for `LocallyRingedSpace.empty`, because
the overlap objects of a glue datum are equal to `∅` only as *spaces*: an `IsEmpty` instance
transports along such an equality, whereas a computation of the presheaf does not. -/
theorem subsingleton_presheaf_obj_of_isEmpty {X : LocallyRingedSpace.{u}} [IsEmpty X]
    (U : (Opens X.toTopCat)ᵒᵖ) : Subsingleton (ToType (X.presheaf.obj U)) := by
  have hU : U.unop = ⊥ := by
    ext x
    exact ⟨fun _ => (IsEmpty.false x).elim, fun h => h.elim⟩
  exact CommRingCat.subsingleton_of_isTerminal (X.toSheafedSpace.sheaf.isTerminalOfEqEmpty hU)

/-- **Equal morphisms have equal `c`-components**, up to the `eqToHom` between the two spellings of
the preimage of the open. The transport is unavoidable: the two `c`-components have different
types until the morphisms are identified, so the equation cannot be stated without it.

The `hV` argument is a *separate* proof of the equality of opens rather than one derived from `h`,
so that a caller may supply whichever proof its goal already mentions; the two are equal by proof
irrelevance. -/
theorem c_app_eq_of_hom_eq {X Y : LocallyRingedSpace.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ)
    (V : Opens Y.toTopCat) (s : ToType (Y.presheaf.obj (op V)))
    (hV : (Opens.map φ.base).obj V = (Opens.map ψ.base).obj V) :
    (ψ.c.app (op V)) s = (X.presheaf.map (eqToHom (congrArg op hV))) ((φ.c.app (op V)) s) := by
  subst h; simp

/-- **An equation of sections may be read after an isomorphism of spaces.** If two morphisms out of
`X` factor as `eqToHom h ≫ α` and `eqToHom h ≫ β` through a space `Y` equal to `X`, then the two
carry a section to the same place exactly when `α` and `β` do. The two transports are unrelated
proofs of two different equalities of opens, which is why both are taken as arguments rather than
derived; each side is stated in the form its own goal already has.

This is what turns the glue datum's `f i j` and `t i j ≫ f j i` into the annulus charts: both
factor through *the same* `eqToHom`, so the `eqToHom` cancels rather than having to be pushed
through a `c`-component. -/
theorem c_app_eq_iff_of_eqToHom_comp {X Y Z : LocallyRingedSpace.{u}} (h : X = Y)
    {φ ψ : X ⟶ Z} {α β : Y ⟶ Z} (hφ : φ = eqToHom h ≫ α) (hψ : ψ = eqToHom h ≫ β)
    (V : Opens Z.toTopCat) (s : ToType (Z.presheaf.obj (op V)))
    (hX : (Opens.map ψ.base).obj V = (Opens.map φ.base).obj V)
    (hY : (Opens.map β.base).obj V = (Opens.map α.base).obj V) :
    ((φ.c.app (op V)) s = (X.presheaf.map (eqToHom (congrArg op hX))) ((ψ.c.app (op V)) s)) ↔
      ((α.c.app (op V)) s = (Y.presheaf.map (eqToHom (congrArg op hY))) ((β.c.app (op V)) s)) := by
  subst h
  rw [eqToHom_refl, Category.id_comp] at hφ hψ
  subst hφ; subst hψ
  exact Iff.rfl

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}

/-! ### The chain's overlap object away from the diagonal -/

/-- **Off the diagonal the chain's overlap object is `AlgebraicGeometry.tateV`.**
`CategoryTheory.GlueData.ofGlueData'` defines `V (i, j)` as `if h : i = j then U i else …`, so the
identification costs exactly the `dif_neg`. -/
theorem tateChainInv_V_of_ne {i j : ULift.{u} ℤ} (hij : i ≠ j) :
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V (i, j) =
      tateV R I q i j := by
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', dif_neg hij]

/-- **Away from the band the chain's overlap object is empty.** `tateChainInv_V_of_ne` followed by
`AlgebraicGeometry.tateV_far`. The hypothesis `i ≠ j` is not implied by the other two: the diagonal
also has `j - i ∉ {1, -1}`, and there the overlap is the whole patch. -/
theorem isEmpty_tateChainInv_V_of_far {i j : ULift.{u} ℤ} (hij : i ≠ j)
    (h1 : j.down - i.down ≠ 1) (h2 : j.down - i.down ≠ -1) :
    IsEmpty ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V (i, j)) :=
  ((tateChainInv_V_of_ne (hq := hq) (hI := hI) hij).trans (tateV_far R I q h1 h2)) ▸ inferInstance

/-! ### The two legs, named -/

/-- **A common `eqToHom` prefix may be cancelled from an equality of preimages.** An equality of
locally ringed spaces induces a homeomorphism of carriers, so two morphisms out of `Y` that pull an
open back to the same place after that homeomorphism already pull it back to the same place. Used
to strip the `eqToHom` from the factorisations below and leave a statement about the annulus charts
alone. -/
theorem LocallyRingedSpace.opens_map_eqToHom_comp_base_inj {X Y Z : LocallyRingedSpace.{u}}
    (h : X = Y) (α β : Y ⟶ Z) (U : Opens Z.toTopCat)
    (hAB : (Opens.map (eqToHom h ≫ α).base).obj U = (Opens.map (eqToHom h ≫ β).base).obj U) :
    (Opens.map α.base).obj U = (Opens.map β.base).obj U := by
  subst h
  rw [eqToHom_refl, Category.id_comp, Category.id_comp] at hAB
  exact hAB

/-- **The forward overlap of the chain is the `x`-chart domain `Spf A{1/x}`.**
`tateChainInv_V_of_ne` followed by `AlgebraicGeometry.tateV_forward`. -/
theorem tateChainInv_V_forward {i j : ULift.{u} ℤ} (hij : i ≠ j) (h1 : j.down - i.down = 1) :
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V (i, j) =
      locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q)) :=
  (tateChainInv_V_of_ne (hq := hq) (hI := hI) hij).trans (tateV_forward R I q h1)

/-- **The backward overlap of the chain is the `y`-chart domain `Spf A{1/y}`.**
`tateChainInv_V_of_ne` followed by `AlgebraicGeometry.tateV_backward`. -/
theorem tateChainInv_V_backward {i j : ULift.{u} ℤ} (hij : i ≠ j) (h2 : j.down - i.down = -1) :
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V (i, j) =
      locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapY R I q)) :=
  (tateChainInv_V_of_ne (hq := hq) (hI := hI) hij).trans (tateV_backward R I q h2)

/-- **The first leg on a forward pair is the `x`-chart.** `CategoryTheory.GlueData'.f'` off the
diagonal is `eqToHom (dif_neg _) ≫ tateF`, and `AlgebraicGeometry.tateF_forward` is
`eqToHom _ ≫ annulusOverlapChart`; the two `eqToHom`s compose. -/
theorem tateChainInv_f_forward {i j : ULift.{u} ℤ} (hij : i ≠ j) (h1 : j.down - i.down = 1) :
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j =
      eqToHom (tateChainInv_V_forward (hq := hq) (hI := hI) hij h1) ≫
        annulusOverlapChart R I q := by
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij,
    tateF_forward R I q h1, eqToHom_trans_assoc]

/-- **The second leg on a forward pair is the `𝔾m`-inversion transition followed by the `y`-chart.**
`AlgebraicGeometry.tateTInv_forward` then `AlgebraicGeometry.tateF_backward` at the reversed pair;
every `eqToHom` between the two cancels, leaving *the same* `eqToHom` as
`tateChainInv_f_forward`. That the two legs factor through one isomorphism is what makes
`isTateInvOverlapCompatibleAt_forward_iff` below possible. -/
theorem tateChainInv_t_comp_f_forward {i j : ULift.{u} ℤ} (hij : i ≠ j)
    (h1 : j.down - i.down = 1) :
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i =
      eqToHom (tateChainInv_V_forward (hq := hq) (hI := hI) hij h1) ≫
        (annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q := by
  have hji : j ≠ i := fun h => hij h.symm
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij, dif_neg hji,
    tateTInv_forward R I q hI h1, tateF_backward R I q (show i.down - j.down = -1 by omega),
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **The first leg on a backward pair is the `y`-chart.** `tateChainInv_f_forward` with
`AlgebraicGeometry.tateF_backward` in place of `tateF_forward`. -/
theorem tateChainInv_f_backward {i j : ULift.{u} ℤ} (hij : i ≠ j) (h2 : j.down - i.down = -1) :
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j =
      eqToHom (tateChainInv_V_backward (hq := hq) (hI := hI) hij h2) ≫
        annulusOverlapChartY R I q := by
  have h1 : j.down - i.down ≠ 1 := by omega
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij,
    tateF_backward R I q h2, eqToHom_trans_assoc]

/-- **The second leg on a backward pair is the inverse transition followed by the `x`-chart.** The
mirror of `tateChainInv_t_comp_f_forward`, with `(annulusChartTransitionInvSpf …).inv` in place of
`.hom`. -/
theorem tateChainInv_t_comp_f_backward {i j : ULift.{u} ℤ} (hij : i ≠ j)
    (h2 : j.down - i.down = -1) :
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i =
      eqToHom (tateChainInv_V_backward (hq := hq) (hI := hI) hij h2) ≫
        (annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q := by
  have hji : j ≠ i := fun h => hij h.symm
  have h1 : j.down - i.down ≠ 1 := by omega
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij, dif_neg hji,
    tateTInv_backward R I q hI h2, tateF_forward R I q (show i.down - j.down = 1 by omega),
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-! ### The condition at one pair -/

variable [TopologicalSpace R] [IsAdicRing I]
variable {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}


/-- **`AlgebraicGeometry.IsTateInvOverlapCompatible` at a single pair of indices.** The two legs
`f i j` and `t i j ≫ f j i` out of the overlap `V (i, j)` carry `s` to the same section, over the
open `AlgebraicGeometry.map_f_tateInvPatchSaturateOpens` identifies. -/
def IsTateInvOverlapCompatibleAt (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) : Prop :=
  (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i j).c.app
      (op (tateInvPatchSaturateOpens hq hI hS))).hom s =
    (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.V (i, j)).presheaf.map
      (eqToHom (congrArg op (map_f_tateInvPatchSaturateOpens hS i j)))).hom
      ((((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i j ≫
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f j i).c.app
        (op (tateInvPatchSaturateOpens hq hI hS))).hom s)

/-- The overlap condition is the conjunction of its instances at each pair. Definitional; it is
stated so that the reductions below can be quoted against a named predicate. -/
theorem isTateInvOverlapCompatible_iff_forall (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    IsTateInvOverlapCompatible hS s ↔ ∀ i j, IsTateInvOverlapCompatibleAt hS s i j :=
  Iff.rfl

/-! ### The two automatic cases -/

/-- **The diagonal is automatic.** `CategoryTheory.GlueData.t_id` makes `t i i` the identity, so
`t i i ≫ f i i` and `f i i` are the same morphism and
`AlgebraicGeometry.LocallyRingedSpace.c_app_eq_of_hom_eq` applies. No property of `f i i` is used;
in particular it is *not* the identity, being `eqToHom (dif_pos rfl)`. -/
theorem isTateInvOverlapCompatibleAt_self (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    IsTateInvOverlapCompatibleAt hS s i i := by
  have h : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.t i i ≫
      (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i i =
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.f i i := by
    rw [CategoryTheory.GlueData.t_id, Category.id_comp]
  exact LocallyRingedSpace.c_app_eq_of_hom_eq h _ s (map_f_tateInvPatchSaturateOpens hS i i)

/-- **The far pairs are automatic.** The overlap is empty
(`isEmpty_tateChainInv_V_of_far`), so its ring of sections is a subsingleton
(`AlgebraicGeometry.LocallyRingedSpace.subsingleton_presheaf_obj_of_isEmpty`) and the two sides of
the condition are equal because there is nothing to tell them apart. -/
theorem isTateInvOverlapCompatibleAt_of_far (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    {i j : ULift.{u} ℤ} (hij : i ≠ j)
    (h1 : j.down - i.down ≠ 1) (h2 : j.down - i.down ≠ -1) :
    IsTateInvOverlapCompatibleAt hS s i j := by
  haveI := isEmpty_tateChainInv_V_of_far (hq := hq) (hI := hI) hij h1 h2
  refine @Subsingleton.elim _ ?_ _ _
  exact LocallyRingedSpace.subsingleton_presheaf_obj_of_isEmpty _

/-! ### The reduction -/

/-- **The overlap condition runs over the adjacent pairs alone.** Everything off the band
`j - i = ±1` is automatic: the diagonal by `isTateInvOverlapCompatibleAt_self` and the rest by
`isTateInvOverlapCompatibleAt_of_far`. This is the section-level form of the four-case split of
`AlgebraicGeometry.tateChainInv_glueMorphisms_compat` (`FormalSchemes.TateChainInvGlue`), which
performs the same split at the level of morphisms. -/
theorem isTateInvOverlapCompatible_iff_adjacent (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    IsTateInvOverlapCompatible hS s ↔
      ∀ i j : ULift.{u} ℤ, j.down - i.down = 1 ∨ j.down - i.down = -1 →
        IsTateInvOverlapCompatibleAt hS s i j := by
  refine ⟨fun h i j _ => h i j, fun h i j => ?_⟩
  by_cases hij : i = j
  · subst hij; exact isTateInvOverlapCompatibleAt_self hS s i
  · by_cases h1 : j.down - i.down = 1
    · exact h i j (Or.inl h1)
    · by_cases h2 : j.down - i.down = -1
      · exact h i j (Or.inr h2)
      · exact isTateInvOverlapCompatibleAt_of_far hS s hij h1 h2

/-! ### The condition in the annulus charts -/

/-- **The two legs see the same open of the `x`-overlap.** The section-level shadow of
`AlgebraicGeometry.map_f_tateInvPatchSaturateOpens`: after the two legs of a forward pair are
factored through one isomorphism of spaces
(`tateChainInv_f_forward`, `tateChainInv_t_comp_f_forward`), that isomorphism may be cancelled by
`AlgebraicGeometry.LocallyRingedSpace.opens_map_eqToHom_comp_base_inj`, leaving an equality of
opens of
`Spf A{1/x}` in which the chain does not occur. Read off the pair `(0, 1)`; any forward pair gives
the same statement. -/
theorem map_annulusOverlapChartY_tateInvPatchSaturateOpens (hS : IsOpen S) :
    (Opens.map ((annulusChartTransitionInvSpf R I q hI).hom ≫
        annulusOverlapChartY R I q).base).obj (tateInvPatchSaturateOpens hq hI hS) =
      (Opens.map (annulusOverlapChart R I q).base).obj (tateInvPatchSaturateOpens hq hI hS) := by
  have hij : (⟨0⟩ : ULift.{u} ℤ) ≠ ⟨1⟩ := fun h => by
    have hd : (0 : ℤ) = 1 := congrArg ULift.down h
    omega
  have h1 : (⟨1⟩ : ULift.{u} ℤ).down - (⟨0⟩ : ULift.{u} ℤ).down = 1 := by
    change (1 : ℤ) - 0 = 1; omega
  have key := map_f_tateInvPatchSaturateOpens (hq := hq) (hI := hI) hS ⟨0⟩ ⟨1⟩
  rw [tateChainInv_f_forward (hq := hq) (hI := hI) hij h1,
    tateChainInv_t_comp_f_forward (hq := hq) (hI := hI) hij h1] at key
  exact LocallyRingedSpace.opens_map_eqToHom_comp_base_inj
    (tateChainInv_V_forward (hq := hq) (hI := hI) hij h1) _ _ _ key

/-- **The mirror statement on the `y`-overlap.**
`map_annulusOverlapChartY_tateInvPatchSaturateOpens` read off the backward pair `(0, -1)`. -/
theorem map_annulusOverlapChart_tateInvPatchSaturateOpens (hS : IsOpen S) :
    (Opens.map ((annulusChartTransitionInvSpf R I q hI).inv ≫
        annulusOverlapChart R I q).base).obj (tateInvPatchSaturateOpens hq hI hS) =
      (Opens.map (annulusOverlapChartY R I q).base).obj (tateInvPatchSaturateOpens hq hI hS) := by
  have hij : (⟨0⟩ : ULift.{u} ℤ) ≠ ⟨-1⟩ := fun h => by
    have hd : (0 : ℤ) = -1 := congrArg ULift.down h
    omega
  have h2 : (⟨-1⟩ : ULift.{u} ℤ).down - (⟨0⟩ : ULift.{u} ℤ).down = -1 := by
    change (-1 : ℤ) - 0 = -1; omega
  have key := map_f_tateInvPatchSaturateOpens (hq := hq) (hI := hI) hS ⟨0⟩ ⟨-1⟩
  rw [tateChainInv_f_backward (hq := hq) (hI := hI) hij h2,
    tateChainInv_t_comp_f_backward (hq := hq) (hI := hI) hij h2] at key
  exact LocallyRingedSpace.opens_map_eqToHom_comp_base_inj
    (tateChainInv_V_backward (hq := hq) (hI := hI) hij h2) _ _ _ key

/-- **The forward condition, on the `x`-chart alone.** `s` pulled back along the `x`-chart equals
`s` pulled back along the `𝔾m`-inversion transition followed by the `y`-chart. This is the
section-level form of `AlgebraicGeometry.tateChainInv_glueMorphisms_compat`'s hypothesis `hf`, and
it names no object of the chain. -/
def IsTateInvChartCompatibleForward (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) : Prop :=
  ((annulusOverlapChart R I q).c.app (op (tateInvPatchSaturateOpens hq hI hS))).hom s =
    ((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (overlapX R I q))).presheaf.map
        (eqToHom (congrArg op (map_annulusOverlapChartY_tateInvPatchSaturateOpens hS)))).hom
      ((((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q).c.app
        (op (tateInvPatchSaturateOpens hq hI hS))).hom s)

/-- **The backward condition, on the `y`-chart alone.** The mirror of
`IsTateInvChartCompatibleForward`, and the section-level form of
`AlgebraicGeometry.tateChainInv_glueMorphisms_compat`'s hypothesis `hb`. -/
def IsTateInvChartCompatibleBackward (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) : Prop :=
  ((annulusOverlapChartY R I q).c.app (op (tateInvPatchSaturateOpens hq hI hS))).hom s =
    ((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (overlapY R I q))).presheaf.map
        (eqToHom (congrArg op (map_annulusOverlapChart_tateInvPatchSaturateOpens hS)))).hom
      ((((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q).c.app
        (op (tateInvPatchSaturateOpens hq hI hS))).hom s)

/-- **A forward pair carries exactly the forward chart condition.** The two legs factor through one
`eqToHom`, so `AlgebraicGeometry.LocallyRingedSpace.c_app_eq_iff_of_eqToHom_comp` cancels it. The
right-hand side does not mention `i` or `j`: every forward pair says the same thing. -/
theorem isTateInvOverlapCompatibleAt_forward_iff (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    {i j : ULift.{u} ℤ} (hij : i ≠ j) (h1 : j.down - i.down = 1) :
    IsTateInvOverlapCompatibleAt hS s i j ↔ IsTateInvChartCompatibleForward hS s :=
  LocallyRingedSpace.c_app_eq_iff_of_eqToHom_comp
    (tateChainInv_V_forward (hq := hq) (hI := hI) hij h1)
    (tateChainInv_f_forward (hq := hq) (hI := hI) hij h1)
    (tateChainInv_t_comp_f_forward (hq := hq) (hI := hI) hij h1)
    (tateInvPatchSaturateOpens hq hI hS) s (map_f_tateInvPatchSaturateOpens hS i j)
    (map_annulusOverlapChartY_tateInvPatchSaturateOpens hS)

/-- **A backward pair carries exactly the backward chart condition.** The mirror of
`isTateInvOverlapCompatibleAt_forward_iff`. -/
theorem isTateInvOverlapCompatibleAt_backward_iff (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    {i j : ULift.{u} ℤ} (hij : i ≠ j) (h2 : j.down - i.down = -1) :
    IsTateInvOverlapCompatibleAt hS s i j ↔ IsTateInvChartCompatibleBackward hS s :=
  LocallyRingedSpace.c_app_eq_iff_of_eqToHom_comp
    (tateChainInv_V_backward (hq := hq) (hI := hI) hij h2)
    (tateChainInv_f_backward (hq := hq) (hI := hI) hij h2)
    (tateChainInv_t_comp_f_backward (hq := hq) (hI := hI) hij h2)
    (tateInvPatchSaturateOpens hq hI hS) s (map_f_tateInvPatchSaturateOpens hS i j)
    (map_annulusOverlapChart_tateInvPatchSaturateOpens hS)

/-- **The overlap condition is two equations on the model patch.** The `ℤ × ℤ`-indexed family of
conditions of `AlgebraicGeometry.IsTateInvOverlapCompatible` collapses to the forward and backward
chart conditions: everything off the band is automatic
(`isTateInvOverlapCompatible_iff_adjacent`) and every pair on the band says one of two things
(`isTateInvOverlapCompatibleAt_forward_iff`, `isTateInvOverlapCompatibleAt_backward_iff`).

This answers, for the chain, the question `FormalSchemes.TateInvNodeChartOverlap` left open —
*which two maps, and over which open* — and the answer names only `annulusOverlapChart`,
`annulusOverlapChartY` and the `𝔾m`-inversion transition
`annulusChartTransitionInvSpf`. Neither of the two morphisms mentions `T_inv` or its glue datum;
the open they are read over, `tateInvPatchSaturateOpens`, is still defined through `ι ⟨0⟩`. -/
theorem isTateInvOverlapCompatible_iff_charts (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    IsTateInvOverlapCompatible hS s ↔
      IsTateInvChartCompatibleForward hS s ∧ IsTateInvChartCompatibleBackward hS s := by
  have hij1 : (⟨0⟩ : ULift.{u} ℤ) ≠ ⟨1⟩ := fun h => by
    have hd : (0 : ℤ) = 1 := congrArg ULift.down h
    omega
  have h1 : (⟨1⟩ : ULift.{u} ℤ).down - (⟨0⟩ : ULift.{u} ℤ).down = 1 := by
    change (1 : ℤ) - 0 = 1; omega
  have hij2 : (⟨0⟩ : ULift.{u} ℤ) ≠ ⟨-1⟩ := fun h => by
    have hd : (0 : ℤ) = -1 := congrArg ULift.down h
    omega
  have h2 : (⟨-1⟩ : ULift.{u} ℤ).down - (⟨0⟩ : ULift.{u} ℤ).down = -1 := by
    change (-1 : ℤ) - 0 = -1; omega
  rw [isTateInvOverlapCompatible_iff_adjacent]
  constructor
  · exact fun h =>
      ⟨(isTateInvOverlapCompatibleAt_forward_iff hS s hij1 h1).1 (h _ _ (Or.inl h1)),
        (isTateInvOverlapCompatibleAt_backward_iff hS s hij2 h2).1 (h _ _ (Or.inr h2))⟩
  · rintro ⟨hf, hb⟩ i j (hadj | hadj)
    · exact (isTateInvOverlapCompatibleAt_forward_iff hS s
        (fun h => by subst h; omega) hadj).2 hf
    · exact (isTateInvOverlapCompatibleAt_backward_iff hS s
        (fun h => by subst h; omega) hadj).2 hb

/-! ### The consequences, over the reduced quantifier -/

/-- **`s` extends to the chain iff it satisfies the condition on the adjacent pairs.**
`AlgebraicGeometry.exists_tateInvConstFamily_iff_tateInvOverlapCompatible`
(`FormalSchemes.TateInvNodeChartOverlap`) with the quantifier reduced. -/
theorem exists_tateInvConstFamily_iff_adjacent
    {W : Opens (tateChainInv R I q hq hI).toLocallyRingedSpace} (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS))) :
    (∃ g : (tateChainInv R I q hq hI).presheaf.obj (op W),
        ∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
          tateInvConstFamily hS hW s i) ↔
      ∀ i j : ULift.{u} ℤ, j.down - i.down = 1 ∨ j.down - i.down = -1 →
        IsTateInvOverlapCompatibleAt hS s i j :=
  (exists_tateInvConstFamily_iff_tateInvOverlapCompatible hS hW s).trans
    (isTateInvOverlapCompatible_iff_adjacent hS s)

/-- **A section satisfying the condition on the adjacent pairs gives a `σ`-invariant section of the
chain.** `AlgebraicGeometry.exists_tateInvShiftAut_zpow_invariant_of_tateInvOverlapCompatible`
(`FormalSchemes.TateInvNodeChartOverlap`) with the quantifier reduced. -/
theorem exists_tateInvShiftAut_zpow_invariant_of_adjacent
    {W : Opens (tateChainInv R I q hq hI).toLocallyRingedSpace} (hS : IsOpen S)
    (hW : W = tateInvSaturateOpens hq hI hS)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)))
    (h : ∀ i j : ULift.{u} ℤ, j.down - i.down = 1 ∨ j.down - i.down = -1 →
      IsTateInvOverlapCompatibleAt hS s i j) :
    ∃ g : (tateChainInv R I q hq hI).presheaf.obj (op W),
      (∀ i, (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app (op W)).hom g =
          tateInvConstFamily hS hW s i) ∧
        ∀ k : ℤ, (((tateInvShiftAut R I q hq hI) ^ k).hom.toShHom.hom.c.app (op W)) g =
          (tateChainInv R I q hq hI).presheaf.map
            (eqToHom (congrArg op (eq_map_tateInvShiftAut_zpow hS hW k))) g :=
  exists_tateInvShiftAut_zpow_invariant_of_tateInvOverlapCompatible hS hW s
    ((isTateInvOverlapCompatible_iff_adjacent hS s).2 h)

/-! ### Non-vacuity -/

/-- **The unit section satisfies the overlap condition.** Both legs' `c`-components and the
transport are ring homomorphisms, so all three carry `1` to `1`. This is what stops
`exists_tateInvShiftAut_zpow_invariant_of_adjacent` and its predecessor from being statements about
an empty set; it is *not* an element that fails to come from `Γ (Spf R, ·)`, which is a separate
question. -/
theorem isTateInvOverlapCompatible_one (hS : IsOpen S) :
    IsTateInvOverlapCompatible (hq := hq) (hI := hI) hS 1 := fun _ _ =>
  (map_one _).trans (Eq.trans (congrArg _ (map_one _)) (map_one _)).symm

end AlgebraicGeometry
