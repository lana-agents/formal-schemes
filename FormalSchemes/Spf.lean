import FormalSchemes.Sections
import FormalSchemes.LimitUnits
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

set_option linter.style.header false

/-!
# The affine formal scheme `Spf R` as a locally ringed space

This file proves that the stalks of the structure sheaf `O_{Spf R}` of the formal spectrum of an
adic ring `R` with ideal of definition `I` are local rings (EGA I, 10.1.6), and packages
`(Spf R, O_{Spf R})` as a `LocallyRingedSpace` — the **affine formal scheme** attached to `R`.

The proof of stalk locality proceeds without any Mittag-Leffler argument:

1. The stalks of each thickening sheaf are local, being (stalks of) structure sheaves of the
   affine schemes `Spec (R ⧸ I ^ (n + 1))` transported along a homeomorphism
   (`FormalSpectrum.thickeningStalkIso`).
2. Units lift through the transition maps of the tower on sections over basic opens: over
   `D(f)` the tower is, by `FormalSpectrum.basicOpenLevelEquiv`, the tower of quotients
   `R_f ⧸ (I·R_f) ^ (n + 1)`, whose transition maps are surjections with nilpotent kernels
   (`FormalSpectrum.isUnit_of_isUnit_stepSheafHom`).
3. A section of `O_{Spf R}` over a basic open all of whose level-`n` components are units is a
   unit, because `Γ(D(f), -)` preserves the limit defining `O_{Spf R}` and an element of a limit
   of rings with invertible projections is invertible (`CommRingCat.isUnit_of_forall_isUnit_π`).
4. Consequently a germ of `O_{Spf R}` whose level-`0` part is invertible in the (local!) stalk
   of the level-`0` sheaf is invertible, which gives the local-ring dichotomy on stalks of
   `O_{Spf R}`.

## Main definitions

* `FormalSpectrum.thickeningStalkIso`: stalks of the thickening sheaves are stalks of the
  structure sheaves of the thickenings; in particular they are local rings.
* `FormalSpectrum.isLocalRing_structureSheaf_stalk`: the stalks of `O_{Spf R}` are local rings
  (EGA I, 10.1.6).
* `FormalSpectrum.sheafedSpaceObj I`, `FormalSpectrum.locallyRingedSpaceObj I`: the (locally)
  ringed space `(Spf R, O_{Spf R})`, i.e. the affine formal scheme of the adic ring `R`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.
* [The Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

namespace FormalSpectrum

/-!
### Stalks of the thickening sheaves are local
-/

section ThickeningStalks

omit [TopologicalSpace R] [IsAdicRing I]

variable (n : ℕ) (x : FormalSpectrum I)

theorem inv_hom_apply : (thickeningTopIso I n).inv ((thickeningTopIso I n).hom x) = x :=
  (thickeningHomeomorph I (n + 1) n.succ_ne_zero).symm_apply_apply x

/-- The stalk of the `n`-th thickening sheaf at `x ∈ Spf R` is the stalk of the structure sheaf
of the thickening `Spec (R ⧸ I ^ (n + 1))` at the corresponding point: pushforward along a
homeomorphism does not change stalks. -/
def thickeningStalkIso :
    (thickeningSheaf I n).presheaf.stalk x ≅
      (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf.stalk ((thickeningTopIso I n).hom x) :=
  ((thickeningSheaf I n).presheaf.stalkCongr
      (Inseparable.of_eq (inv_hom_apply I n x).symm)) ≪≫
    @asIso _ _ _ _
      (TopCat.Presheaf.stalkPushforward CommRingCat (thickeningTopIso I n).inv
        (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf ((thickeningTopIso I n).hom x))
      (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        (C := CommRingCat) (f := (thickeningTopIso I n).inv)
        ((thickeningHomeomorph I (n + 1) n.succ_ne_zero).symm.isInducing)
        ((Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf) ((thickeningTopIso I n).hom x))

instance isLocalRing_thickeningSheaf_stalk :
    IsLocalRing ((thickeningSheaf I n).presheaf.stalk x) :=
  haveI : IsLocalRing ((Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf.stalk
      ((thickeningTopIso I n).hom x)) :=
    (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).isLocalRing
      ((thickeningTopIso I n).hom x)
  (thickeningStalkIso I n x).symm.commRingCatIsoToRingEquiv.isLocalRing

end ThickeningStalks

/-!
### Units lift through the tower of thickening sheaves on basic opens
-/

section UnitsLift

omit [TopologicalSpace R] [IsAdicRing I]

/-- If two ideals `K ≤ L` satisfy `L ^ k ≤ K`, then the projection `A ⧸ K → A ⧸ L` reflects
units: the kernel consists of nilpotent elements and the map is surjective. -/
theorem isUnit_of_isUnit_factor {A : Type*} [CommRing A] {K L : Ideal A} (h : K ≤ L) (k : ℕ)
    (hpow : L ^ k ≤ K) {a : A ⧸ K} (ha : IsUnit (Ideal.Quotient.factor h a)) : IsUnit a := by
  obtain ⟨binv, hbinv⟩ := ha.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.factor_surjective h binv
  have h1 : Ideal.Quotient.factor h (a * b - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hbinv, sub_self]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (a * b - 1)
  have hcL : c ∈ L := by
    rw [← hc, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  have hnil : IsNilpotent (a * b - 1) := by
    refine ⟨k, ?_⟩
    rw [← hc, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hpow (Ideal.pow_mem_pow hcL k)
  have hab : IsUnit (a * b) := by
    have := hnil.isUnit_add_one
    rwa [sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left hab

variable (f : R) (n : ℕ)

/-- The transition maps of the tower of thickening sheaves reflect units on sections over a
basic open `D(f)`: under `basicOpenLevelEquiv` they are the projections
`R_f ⧸ (I·R_f) ^ (n + 2) → R_f ⧸ (I·R_f) ^ (n + 1)`, which are surjective with nilpotent
kernels. -/
theorem isUnit_of_isUnit_stepSheafHom
    (t : (thickeningSheaf I (n + 1)).presheaf.obj (op (basicOpen I f)))
    (ht : IsUnit (((stepSheafHom I n).hom.app (op (basicOpen I f))).hom t)) : IsUnit t := by
  have hkey := DFunLike.congr_fun (basicOpenLevelEquiv_step I f n) t
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe] at hkey
  have h1 : IsUnit (basicOpenLevelEquiv I f n
      (((stepSheafHom I n).hom.app (op (basicOpen I f))).hom t)) := ht.map _
  rw [hkey] at h1
  have h2 : IsUnit (basicOpenLevelEquiv I f (n + 1) t) :=
    isUnit_of_isUnit_factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) 2
      (by
        rw [← pow_mul]
        exact Ideal.pow_le_pow_right (by omega))
      h1
  have h3 := h2.map (basicOpenLevelEquiv I f (n + 1)).symm
  rwa [RingEquiv.symm_apply_apply] at h3

/-- A section of `O_{Spf R}` over a basic open `D(f)` whose level-`0` component is a unit is a
unit: all level components are units by `isUnit_of_isUnit_stepSheafHom`, and `Γ(D(f), -)`
preserves the limit defining `O_{Spf R}`. -/
theorem isUnit_of_isUnit_zero
    (s : (structureSheaf I).presheaf.obj (op (basicOpen I f)))
    (h0 : IsUnit (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
      (op (basicOpen I f))).hom s)) :
    IsUnit s := by
  have hall : ∀ m : ℕ, IsUnit (((limit.π (structureSheafFunctor I) ⟨m⟩).hom.app
      (op (basicOpen I f))).hom s) := by
    intro m
    induction m with
    | zero => exact h0
    | succ m ih =>
      apply isUnit_of_isUnit_stepSheafHom I f m
      have hw := limit.w (structureSheafFunctor I) (homOfLE (Nat.le_add_right m 1)).op
      rw [structureSheafFunctor_map_succ] at hw
      have hw' : ((stepSheafHom I m).hom.app (op (basicOpen I f))).hom
          (((limit.π (structureSheafFunctor I) ⟨m + 1⟩).hom.app (op (basicOpen I f))).hom s) =
          ((limit.π (structureSheafFunctor I) ⟨m⟩).hom.app (op (basicOpen I f))).hom s :=
        DFunLike.congr_fun (congrArg (fun (α : limit (structureSheafFunctor I) ⟶
          thickeningSheaf I m) => (α.hom.app (op (basicOpen I f))).hom) hw) s
      rw [hw']
      exact ih
  -- transport along `sectionsLimitIso` to the categorical limit of the tower of sections
  have hunit : IsUnit ((sectionsLimitIso I (op (basicOpen I f))).hom.hom s) := by
    refine CommRingCat.isUnit_of_forall_isUnit_π
      (limit.isLimit (structureSheafFunctor I ⋙ sectionsFunctor I (op (basicOpen I f)))) _
      fun j => ?_
    have hπ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (sectionsLimitIso_hom_π I (op (basicOpen I f)) j.unop)) s
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hπ
    exact hπ.symm ▸ hall j.unop
  have hinv : (sectionsLimitIso I (op (basicOpen I f))).inv.hom
      ((sectionsLimitIso I (op (basicOpen I f))).hom.hom s) = s := by
    simp
  have h2 := hunit.map (sectionsLimitIso I (op (basicOpen I f))).inv.hom
  rwa [hinv] at h2

end UnitsLift

/-!
### Stalks of `O_{Spf R}` are local rings (EGA I, 10.1.6)
-/

section StalksLocal

omit [TopologicalSpace R] [IsAdicRing I]

variable (x : FormalSpectrum I)

/-- The map from the stalk of `O_{Spf R}` to the stalk of the level-`n` thickening sheaf. -/
def stalkProj (n : ℕ) :
    (structureSheaf I).presheaf.stalk x ⟶ (thickeningSheaf I n).presheaf.stalk x := by
  exact (TopCat.Presheaf.stalkFunctor CommRingCat x).map
    (limit.π (structureSheafFunctor I) ⟨n⟩).hom

/-- A germ of `O_{Spf R}` at `x` whose level-`0` part is invertible in the stalk of the
level-`0` thickening sheaf is invertible. -/
theorem isUnit_stalk_of_isUnit_zero (a : (structureSheaf I).presheaf.stalk x)
    (h : IsUnit ((stalkProj I x 0).hom a)) : IsUnit a := by
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ a
  rw [show (stalkProj I x 0).hom ((structureSheaf I).presheaf.germ U x hxU s) =
      (thickeningSheaf I 0).presheaf.germ U x hxU
        (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op U)).hom s) from
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      (limit.π (structureSheafFunctor I) ⟨0⟩).hom s] at h
  obtain ⟨V, iVU, hxV, hunit⟩ :=
    RingedSpace.isUnit_res_of_isUnit_germ ⟨⟨TopCat.of (FormalSpectrum I),
      (thickeningSheaf I 0).presheaf⟩, (thickeningSheaf I 0).property⟩ U _ x hxU h
  obtain ⟨w, hw, hxw, hwV⟩ := (isTopologicalBasis_basicOpen I).exists_subset_of_mem_open
    hxV V.2
  obtain ⟨f, rfl⟩ := hw
  have hDV : basicOpen I f ≤ V := hwV
  have hDU : basicOpen I f ≤ U := le_trans hDV (leOfHom iVU)
  set s' := (structureSheaf I).presheaf.map (homOfLE hDU).op s with hs'
  -- the level-0 component of `s'` is a unit
  have h0 : IsUnit (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
      (op (basicOpen I f))).hom s') := by
    have hnat : ((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
        (op (basicOpen I f))).hom s' =
        ((thickeningSheaf I 0).presheaf.map (homOfLE hDU).op).hom
          (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op U)).hom s) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        ((limit.π (structureSheafFunctor I) ⟨0⟩).hom.naturality (homOfLE hDU).op)) s
    have hfac : ((thickeningSheaf I 0).presheaf.map (homOfLE hDU).op).hom
        (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op U)).hom s) =
        ((thickeningSheaf I 0).presheaf.map (homOfLE hDV).op).hom
          (((thickeningSheaf I 0).presheaf.map iVU.op).hom
            (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op U)).hom s)) := by
      rw [show (homOfLE hDU).op = iVU.op ≫ (homOfLE hDV).op from Subsingleton.elim _ _,
        Functor.map_comp]
      rfl
    rw [hnat, hfac]
    exact hunit.map _
  have hs'unit : IsUnit s' := isUnit_of_isUnit_zero I f s' h0
  have hgerm : (structureSheaf I).presheaf.germ (basicOpen I f) x hxw s' =
      (structureSheaf I).presheaf.germ U x hxU s :=
    (structureSheaf I).presheaf.germ_res_apply (homOfLE hDU) x hxw s
  rw [← hgerm]
  exact hs'unit.map _

/-- **Stalks of the structure sheaf of a formal spectrum are local rings** (EGA I, 10.1.6). -/
instance isLocalRing_structureSheaf_stalk :
    IsLocalRing ((structureSheaf I).presheaf.stalk x) := by
  haveI : Nontrivial ((structureSheaf I).presheaf.stalk x) :=
    (stalkProj I x 0).hom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((stalkProj I x 0).hom a) with h | h
  · exact Or.inl (isUnit_stalk_of_isUnit_zero I x a h)
  · refine Or.inr (isUnit_stalk_of_isUnit_zero I x (1 - a) ?_)
    rwa [map_sub, map_one]

end StalksLocal

/-!
### `Spf R` as a locally ringed space
-/

/-- The formal spectrum `Spf R` of an adic ring, as a sheafed space: the topological space
`FormalSpectrum I` equipped with the structure sheaf `O_{Spf R}`. -/
def sheafedSpaceObj : SheafedSpace CommRingCat where
  carrier := TopCat.of (FormalSpectrum I)
  presheaf := (structureSheaf I).presheaf
  IsSheaf := (structureSheaf I).property

omit [TopologicalSpace R] [IsAdicRing I] in
@[simp]
theorem sheafedSpaceObj_presheaf :
    (sheafedSpaceObj I).presheaf = (structureSheaf I).presheaf :=
  rfl

/-- The **affine formal scheme** `Spf R` of an adic ring `R` with ideal of definition `I`, as a
locally ringed space (EGA I, 10.1.6): the formal spectrum with its structure sheaf, whose stalks
are local rings. -/
def locallyRingedSpaceObj : LocallyRingedSpace where
  __ := sheafedSpaceObj I
  isLocalRing x := isLocalRing_structureSheaf_stalk I x

end FormalSpectrum
