import FormalSchemes.AwayCompletionInterchange
import FormalSchemes.CompletedTensor
import Mathlib.RingTheory.Localization.Away.Basic

set_option linter.style.header false
-- The `lift`/`mapCompletion`/`extendRingHom` terms live over nested localization/completion
-- towers, which are slow for the elaborator, the instance cache and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The completed-tensor / away-localization interchange

Fix an adic base `(R, I)` with `I` finitely generated, two `R`-algebras `A` and `B`, and an
element `f : A`. Write `C = A ⊗̂_R B = CompletedTensorProduct R I A B` for the completed tensor
product and `f̄ = CompletedTensorProduct.inl R I A B f : C` for the image of `f`. There are two
natural ways to build "the completed tensor product with the `f`-chart of `A`":

* localise-then-tensor: `CompletedTensorProduct R I (A{1/f}) B`, where
  `A{1/f} = FormalSpectrum.awayCompletion (I·A) f` is the completed localization of `A` away
  from `f` (`FormalSchemes/BasicOpenChart.lean`);
* tensor-then-localise: `C{1/f̄} = FormalSpectrum.awayCompletion (idealOfDefinition R I A B) f̄`,
  the completed localization of `C` away from `f̄`.

These are canonically isomorphic as complete adic `R`-algebras, and the isomorphism carries the
ideal of definition of the left onto that of the right. This is the tensored analogue of the
single-ring interchange `AdicCompletion.awayCompletionInterchange`
(`FormalSchemes/AwayCompletionInterchange.lean`), and is the overlap-chart crux for the general
glued fibre product of formal schemes.

The two ring homomorphisms are built directly from the universal properties, imitating
`RestrictedPowerSeries.baseChangeEquiv` (`FormalSchemes/BaseChange.lean`):

* forward `CompletedTensorProduct R I (A{1/f}) B →+* C{1/f̄}`: the universal property of the
  completed tensor product (`CompletedTensorProduct.lift`) applied to the completion
  `A{1/f} → C{1/f̄}` of the localization map `A_f → C_{f̄}` and to the structural map
  `B → C → C{1/f̄}`;
* backward `C{1/f̄} →+* CompletedTensorProduct R I (A{1/f}) B`: the completion
  (`AdicCompletion.extendRingHom`) of the localization `C_{f̄} → ·` extending the
  completed-tensor lift `C → CompletedTensorProduct R I (A{1/f}) B`.

Mutual inverse is proved with the two uniqueness principles
(`CompletedTensorProduct.hom_ext`, `AdicCompletion.hom_ext_of_continuous`) and the universal
property of localization (`IsLocalization.ringHom_ext`).

## Main results

* `CompletedTensorAwayInterchange.forwardHom`, `backwardHom`: the two ring homomorphisms.
* `CompletedTensorAwayInterchange.equiv`: the ring isomorphism
  `CompletedTensorProduct R I (A{1/f}) B ≃+* C{1/f̄}`.
* `CompletedTensorAwayInterchange.equiv_map_idealOfDefinition`: it carries the ideal of definition
  of the left onto that of the right.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal TensorProduct

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (f : A)

/-- Conversion between the completion structure map (`algebraMap`) and `AdicCompletion.of`. -/
private theorem algebraMap_eq_of {D : Type u} [CommRing D] (K : Ideal D) (d : D) :
    algebraMap D (AdicCompletion K D) d = AdicCompletion.of K D d := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-! ### Basic ideal computations -/

/-- The ideal of definition of the base localization `A_f`, expressed as `I·A_f`. -/
theorem srcBaseIdeal_eq :
    (I.map (algebraMap R A)).map (algebraMap A (Localization.Away f)) =
      I.map (algebraMap R (Localization.Away f)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The ideal of definition of `C_{f̄}`, expressed as `I·C_{f̄}`. -/
theorem tensorLocIdeal_eq :
    (CompletedTensorProduct.idealOfDefinition R I A B).map
        (algebraMap (CompletedTensorProduct R I A B)
          (Localization.Away (CompletedTensorProduct.inl R I A B f))) =
      I.map (algebraMap R (Localization.Away (CompletedTensorProduct.inl R I A B f))) := by
  rw [CompletedTensorProduct.idealOfDefinition_eq_map, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- The completion of the localization map carries `I·A_f` onto `I·C_{f̄}`. -/
theorem map_srcBaseIdeal_locMap :
    ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away f))).map
        (Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f).toRingHom =
      (CompletedTensorProduct.idealOfDefinition R I A B).map
        (algebraMap (CompletedTensorProduct R I A B)
          (Localization.Away (CompletedTensorProduct.inl R I A B f))) := by
  rw [srcBaseIdeal_eq, tensorLocIdeal_eq, Ideal.map_map]
  congr 1
  exact (Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f).comp_algebraMap

/-- `I·C{1/f̄}` is exactly the ideal of definition of `C{1/f̄}`.

`FormalSpectrum.map_algebraMap_awayCompletion` (`FormalSchemes.BasicOpenChart`) at
`L := CompletedTensorProduct.idealOfDefinition R I A B`. This is the instance that motivates that
lemma's `h : I·A = L` hypothesis rather than the `rfl` form: the ideal of definition of
`A ⊗̂_R B` is equal to `I·(A ⊗̂_R B)` but is not that term, so `idealOfDefinition_eq_map` has to
supply the identification. -/
theorem idealOfDef_tgt_eq :
    I.map (algebraMap R (FormalSpectrum.awayCompletion
        (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))) =
      FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) :=
  FormalSpectrum.map_algebraMap_awayCompletion _
    (CompletedTensorProduct.idealOfDefinition_eq_map (R := R) (I := I) (A := A) (B := B)).symm

/-! ### The forward homomorphism -/

/-- The `commutes'` proof for `forwardAwayHom`, as a standalone lemma (avoids the `.toFun`
matching issue when building the `AlgHom`). -/
theorem forwardAway_commutes (hI : I.FG) (r : R) :
    AdicCompletion.mapCompletion
        (Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f).toRingHom
        (le_of_eq (map_srcBaseIdeal_locMap I f)) (((hI.map _).map _).map _)
        (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) r) =
      algebraMap R (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) r := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.mapCompletion_of]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- The completion `A{1/f} →ₐ[R] C{1/f̄}` of the localization map `A_f → C_{f̄}`. -/
def forwardAwayHom (hI : I.FG) :
    FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f →ₐ[R]
      FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) :=
  { AdicCompletion.mapCompletion
      (Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f).toRingHom
      (le_of_eq (map_srcBaseIdeal_locMap I f)) (((hI.map _).map _).map _) with
    commutes' := forwardAway_commutes I f hI }

theorem forwardAwayHom_apply (hI : I.FG)
    (x : FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) :
    forwardAwayHom I f hI x =
      AdicCompletion.mapCompletion
        (Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f).toRingHom
        (le_of_eq (map_srcBaseIdeal_locMap I f)) (((hI.map _).map _).map _) x :=
  rfl

/-- Action of `forwardAwayHom` on the image of the base localization `A_f`. -/
theorem forwardAwayHom_algebraMap (hI : I.FG) (y : Localization.Away f) :
    forwardAwayHom I f hI
        (algebraMap (Localization.Away f)
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) y) =
      algebraMap (Localization.Away (CompletedTensorProduct.inl R I A B f))
        (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f))
        (Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f y) := by
  rw [forwardAwayHom_apply, AdicCompletion.mapCompletion_algebraMap]
  rfl

/-- The `commutes'` proof for `forwardHomB`. -/
theorem forwardHomB_commutes (r : R) :
    (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).comp
        (CompletedTensorProduct.inr R I A B).toRingHom (algebraMap R B r) =
      algebraMap R (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) r := by
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [(CompletedTensorProduct.inr R I A B).commutes, ← RingHom.comp_apply,
    FormalSpectrum.awayCompletionHom_comp_algebraMap]

/-- The structural map `B →ₐ[R] C{1/f̄}`, i.e. `B → C → C{1/f̄}`. -/
def forwardHomB :
    B →ₐ[R] FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f) :=
  { (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).comp
        (CompletedTensorProduct.inr R I A B).toRingHom with
    commutes' := forwardHomB_commutes I f }

theorem forwardHomB_apply (b : B) :
    forwardHomB I f b =
      FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) (CompletedTensorProduct.inr R I A B b) :=
  rfl

/-- **The forward homomorphism** `CompletedTensorProduct R I (A{1/f}) B →+* C{1/f̄}`. -/
def forwardHom (hI : I.FG) :
    CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B →+*
      FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) :=
  haveI : IsAdicComplete
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    (AdicCompletion.isAdicRing_map _ (((hI.map _).map _).map _)).toIsAdicComplete
  CompletedTensorProduct.lift
    (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f))
    (le_of_eq (idealOfDef_tgt_eq I f)) (forwardAwayHom I f hI) (forwardHomB I f)

@[simp]
theorem forwardHom_inl (hI : I.FG)
    (a : FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) :
    forwardHom I f hI
        (CompletedTensorProduct.inl R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)
          B a) =
      forwardAwayHom I f hI a := by
  haveI : IsAdicComplete
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    (AdicCompletion.isAdicRing_map _ (((hI.map _).map _).map _)).toIsAdicComplete
  exact CompletedTensorProduct.lift_inl _ _ _ _ a

@[simp]
theorem forwardHom_inr (hI : I.FG) (b : B) :
    forwardHom I f hI
        (CompletedTensorProduct.inr R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)
          B b) =
      forwardHomB I f b := by
  haveI : IsAdicComplete
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    (AdicCompletion.isAdicRing_map _ (((hI.map _).map _).map _)).toIsAdicComplete
  exact CompletedTensorProduct.lift_inr _ _ _ _ b

/-- Continuity of the forward homomorphism. -/
theorem forwardHom_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B}
    (hx : x ∈ (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) ^ m) :
    forwardHom I f hI x ∈
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) ^ m := by
  haveI : IsAdicComplete
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    (AdicCompletion.isAdicRing_map _ (((hI.map _).map _).map _)).toIsAdicComplete
  exact CompletedTensorProduct.lift_mem_pow _ _ _ _ hI m hx

/-! ### The backward homomorphism -/

/-- The image of `a : A` in `A{1/f}` factors through `A_f`. -/
private theorem algebraMap_A_Achart (a : A) :
    algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) a =
      algebraMap (Localization.Away f) (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)
        (algebraMap A (Localization.Away f) a) := by
  rw [AdicCompletion.algebraMap_apply, algebraMap_eq_of]

/-- The `R`-algebra structure on `A{1/f}` factors through `A`. The pointwise form of
`FormalSpectrum.awayCompletionHom_comp_algebraMap`, and like it a direct instance of
`IsScalarTower.algebraMap_apply`: the tower `R → A → A{1/f}` is already an instance, so the
`algebraMap_eq_of`/`AdicCompletion.algebraMap_apply` chain this proof used to carry was never
needed. (Issue 881; found by sweeping for the *shape* of the consolidated lemma rather than its
name, which is how this fourth declaration of the same fact came to light.) -/
private theorem algebraMap_A_Achart_algebraMap (r : R) :
    algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) (algebraMap R A r) =
      algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) r :=
  (IsScalarTower.algebraMap_apply R A _ r).symm

/-- `f` becomes a unit in `A{1/f}`. -/
private theorem isUnit_algebraMap_A_Achart :
    IsUnit (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) f) := by
  rw [algebraMap_A_Achart]
  exact (IsLocalization.Away.algebraMap_isUnit f).map
    (algebraMap (Localization.Away f) (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f))

/-- The localization map `A_f → C_{f̄}` on the image of `a : A` is `(C → C_{f̄}) ∘ inl`. -/
theorem locMap_algebraMap (a : A) :
    Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f
        (algebraMap A (Localization.Away f) a) =
      algebraMap (CompletedTensorProduct R I A B)
        (Localization.Away (CompletedTensorProduct.inl R I A B f))
        (CompletedTensorProduct.inl R I A B a) := by
  rw [Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

/-- The `commutes'` proof for `gA`. -/
theorem gA_commutes (r : R) :
    (CompletedTensorProduct.inl R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom.comp
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f))
        (algebraMap R A r) =
      algebraMap R (CompletedTensorProduct R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) r := by
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [algebraMap_A_Achart_algebraMap, (CompletedTensorProduct.inl R I
    (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).commutes]

/-- The structural map `A →ₐ[R] (A{1/f}) ⊗̂_R B`, given by `A → A{1/f} → ·`. -/
def gA :
    A →ₐ[R] CompletedTensorProduct R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B :=
  { (CompletedTensorProduct.inl R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom.comp
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)) with
    commutes' := gA_commutes I f }

theorem gA_apply (a : A) :
    gA I f a = CompletedTensorProduct.inl R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) a) :=
  rfl

/-- The completed-tensor lift `C = A ⊗̂_R B →+* CompletedTensorProduct R I (A{1/f}) B`. -/
def gCHom (hI : I.FG) :
    CompletedTensorProduct R I A B →+*
      CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B :=
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  CompletedTensorProduct.lift
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
    (le_of_eq (CompletedTensorProduct.idealOfDefinition_eq_map).symm) (gA I f)
    (CompletedTensorProduct.inr R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)

@[simp]
theorem gCHom_inl (hI : I.FG) (a : A) :
    gCHom I f hI (CompletedTensorProduct.inl R I A B a) = gA I f a := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  exact CompletedTensorProduct.lift_inl _ _ _ _ a

@[simp]
theorem gCHom_inr (hI : I.FG) (b : B) :
    gCHom I f hI (CompletedTensorProduct.inr R I A B b) =
      CompletedTensorProduct.inr R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B b := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  exact CompletedTensorProduct.lift_inr _ _ _ _ b

theorem isUnit_gCHom_fbar (hI : I.FG) :
    IsUnit (gCHom I f hI (CompletedTensorProduct.inl R I A B f)) := by
  rw [gCHom_inl, gA_apply]
  exact (isUnit_algebraMap_A_Achart I f).map
    (CompletedTensorProduct.inl R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)

/-- The localization `C_{f̄} →+* CompletedTensorProduct R I (A{1/f}) B` extending `gCHom`. -/
def psiHom (hI : I.FG) :
    Localization.Away (CompletedTensorProduct.inl R I A B f) →+*
      CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B :=
  IsLocalization.Away.lift (CompletedTensorProduct.inl R I A B f) (isUnit_gCHom_fbar I f hI)

theorem psiHom_comp (hI : I.FG) :
    (psiHom I f hI).comp
        (algebraMap (CompletedTensorProduct R I A B)
          (Localization.Away (CompletedTensorProduct.inl R I A B f))) =
      gCHom I f hI :=
  IsLocalization.Away.lift_comp _ _

theorem psiHom_algebraMap (hI : I.FG) (c : CompletedTensorProduct R I A B) :
    psiHom I f hI
        (algebraMap (CompletedTensorProduct R I A B)
          (Localization.Away (CompletedTensorProduct.inl R I A B f)) c) =
      gCHom I f hI c :=
  IsLocalization.Away.lift_eq _ _ _

/-- `psiHom` carries `I·C_{f̄}` into the ideal of definition of the target. -/
theorem psiHom_map_le (hI : I.FG) :
    ((CompletedTensorProduct.idealOfDefinition R I A B).map
          (algebraMap (CompletedTensorProduct R I A B)
            (Localization.Away (CompletedTensorProduct.inl R I A B f)))).map (psiHom I f hI) ≤
      CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro x hx
  simp only [Ideal.mem_comap]
  rw [psiHom_algebraMap]
  have h1 : x ∈ (CompletedTensorProduct.idealOfDefinition R I A B) ^ 1 := by rwa [pow_one]
  have h2 := CompletedTensorProduct.lift_mem_pow
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
    (le_of_eq (CompletedTensorProduct.idealOfDefinition_eq_map).symm) (gA I f)
    (CompletedTensorProduct.inr R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
    hI 1 h1
  rw [pow_one] at h2
  exact h2

/-- Continuity of `psiHom` (the `hψ` hypothesis of `extendRingHom`). -/
theorem psiHom_continuous (hI : I.FG) (m : ℕ) :
    ((CompletedTensorProduct.idealOfDefinition R I A B).map
        (algebraMap (CompletedTensorProduct R I A B)
          (Localization.Away (CompletedTensorProduct.inl R I A B f)))) ^ m ≤
      ((CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) ^ m).comap
        (psiHom I f hI) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (psiHom_map_le I f hI) m

/-- **The backward homomorphism** `C{1/f̄} →+* CompletedTensorProduct R I (A{1/f}) B`. -/
def backwardHom (hI : I.FG) :
    FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) →+*
      CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B :=
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  AdicCompletion.extendRingHom
    ((CompletedTensorProduct.idealOfDefinition R I A B).map
      (algebraMap (CompletedTensorProduct R I A B)
        (Localization.Away (CompletedTensorProduct.inl R I A B f))))
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
    (psiHom I f hI) (psiHom_continuous I f hI)

theorem backwardHom_of (hI : I.FG)
    (z : Localization.Away (CompletedTensorProduct.inl R I A B f)) :
    backwardHom I f hI
        (AdicCompletion.of
          ((CompletedTensorProduct.idealOfDefinition R I A B).map
            (algebraMap (CompletedTensorProduct R I A B)
              (Localization.Away (CompletedTensorProduct.inl R I A B f))))
          (Localization.Away (CompletedTensorProduct.inl R I A B f)) z) =
      psiHom I f hI z := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  exact AdicCompletion.extendRingHom_of _ _ _ _ z

theorem backwardHom_algebraMap (hI : I.FG)
    (z : Localization.Away (CompletedTensorProduct.inl R I A B f)) :
    backwardHom I f hI
        (algebraMap (Localization.Away (CompletedTensorProduct.inl R I A B f))
          (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
            (CompletedTensorProduct.inl R I A B f)) z) =
      psiHom I f hI z := by
  rw [algebraMap_eq_of, backwardHom_of]

/-- Continuity of the backward homomorphism. -/
theorem backwardHom_mem_pow (hI : I.FG) (m : ℕ)
    {x : FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f)}
    (hx : x ∈ (FormalSpectrum.awayCompletionIdeal
      (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f)) ^ m) :
    backwardHom I f hI x ∈
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) ^ m := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at hx
  exact AdicCompletion.extendRingHom_continuous _ _ (psiHom I f hI) (psiHom_continuous I f hI)
    (((hI.map _).map _).map _) m x hx

/-! ### The maps are mutually inverse -/

/-- The ideal of definition of `A{1/f}` (as `AdicCompletion` of `A_f`) equals `I·A{1/f}`.

The left-hand side is `FormalSpectrum.awayCompletionIdeal (I·A) f` unfolded — `awayCompletionIdeal`
is an `abbrev` for exactly this — so this is `map_algebraMap_awayCompletion_eq` read backwards. It
keeps its own name because its six consumers in `FormalSchemes.TateSeparated` meet the unfolded
spelling and `rw` is syntactic. (Issue 895: this was the seventh declaration of one fact, and the
one whose name shares no substring with the other six.) -/
theorem idealOfDef_Achart_eq :
    AdicCompletion.idealOfDefinition
        ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away f))) =
      I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)) :=
  (FormalSpectrum.map_algebraMap_awayCompletion_eq I f).symm

/-- On `C = A ⊗̂_R B`, forward ∘ `gCHom` is the structural map `C → C{1/f̄}`. -/
theorem forward_gCHom (hI : I.FG) :
    (forwardHom I f hI).comp (gCHom I f hI) =
      FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) := by
  haveI : IsAdicComplete
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    (AdicCompletion.isAdicRing_map _ (((hI.map _).map _).map _)).toIsAdicComplete
  refine CompletedTensorProduct.hom_ext
    (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f)) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · simp only [RingHom.comp_apply]
    have h1 : gCHom I f hI x ∈ (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) ^ m := by
      haveI : IsAdicComplete
          (CompletedTensorProduct.idealOfDefinition R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
          (CompletedTensorProduct R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
        (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
      exact CompletedTensorProduct.lift_mem_pow _ _ _ _ hI m hx
    exact forwardHom_mem_pow I f hI m h1
  · have := Ideal.mem_map_of_mem
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) hx
    rwa [Ideal.map_pow, FormalSpectrum.map_awayCompletionHom] at this
  · simp only [RingHom.comp_apply, FormalSpectrum.awayCompletionHom]
    rw [gCHom_inl, gA_apply, forwardHom_inl, algebraMap_A_Achart, forwardAwayHom_algebraMap,
      locMap_algebraMap]
  · simp only [RingHom.comp_apply]
    rw [gCHom_inr, forwardHom_inr, forwardHomB_apply]

/-- On the dense subring `C_{f̄}`, forward ∘ `psiHom` is the map `C_{f̄} → C{1/f̄}`. -/
theorem forward_psiHom (hI : I.FG) :
    (forwardHom I f hI).comp (psiHom I f hI) =
      algebraMap (Localization.Away (CompletedTensorProduct.inl R I A B f))
        (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f)) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (CompletedTensorProduct.inl R I A B f)) ?_
  rw [RingHom.comp_assoc, psiHom_comp, forward_gCHom]
  rfl

/-- On the image of `C`, `backward ∘ awayCompletionHom = gCHom`. -/
theorem backwardHom_awayCompletionHom (hI : I.FG) (c : CompletedTensorProduct R I A B) :
    backwardHom I f hI
        (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f) c) =
      gCHom I f hI c := by
  simp only [FormalSpectrum.awayCompletionHom, RingHom.comp_apply]
  rw [backwardHom_algebraMap, psiHom_algebraMap]

/-- On the first factor `A{1/f}`, backward ∘ forwardAway is the canonical map `inl`. -/
theorem backward_forwardAway (hI : I.FG) :
    (backwardHom I f hI).comp (forwardAwayHom I f hI).toRingHom =
      (CompletedTensorProduct.inl R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  refine AdicCompletion.hom_ext_of_continuous
    ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away f)))
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
    ((hI.map _).map _) (fun m x hx => ?_) (fun m x hx => ?_) (fun y => ?_)
  · simp only [RingHom.coe_comp, AlgHom.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_coe]
    have hfw := AdicCompletion.mapCompletion_mem_pow
      (Localization.awayMapₐ (CompletedTensorProduct.inl R I A B) f).toRingHom
      (le_of_eq (map_srcBaseIdeal_locMap I f)) (((hI.map _).map _).map _) ((hI.map _).map _) m hx
    rw [← forwardAwayHom_apply I f hI] at hfw
    exact backwardHom_mem_pow I f hI m hfw
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have hx' : x ∈ (I.map (algebraMap R
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f))) ^ m := by
      rw [← idealOfDef_Achart_eq]
      exact (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx
    exact CompletedTensorProduct.inl_mem_pow m hx'
  · rw [← algebraMap_eq_of ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away f))) y]
    have key :
        ((backwardHom I f hI).comp (forwardAwayHom I f hI).toRingHom).comp
            (algebraMap (Localization.Away f)
              (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)) =
          (CompletedTensorProduct.inl R I
              (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom.comp
            (algebraMap (Localization.Away f)
              (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [forwardAwayHom_algebraMap, backwardHom_algebraMap, locMap_algebraMap, psiHom_algebraMap,
        gCHom_inl, gA_apply, ← algebraMap_A_Achart]
    exact DFunLike.congr_fun key y

/-- forward ∘ backward = id on `C{1/f̄}`. -/
theorem forward_comp_backward (hI : I.FG) :
    (forwardHom I f hI).comp (backwardHom I f hI) =
      RingHom.id (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) := by
  haveI : IsAdicComplete
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    (AdicCompletion.isAdicRing_map _ (((hI.map _).map _).map _)).toIsAdicComplete
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  refine AdicCompletion.hom_ext_of_continuous
    ((CompletedTensorProduct.idealOfDefinition R I A B).map
      (algebraMap (CompletedTensorProduct R I A B)
        (Localization.Away (CompletedTensorProduct.inl R I A B f))))
    (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f))
    (((hI.map _).map _).map _) (fun m x hx => ?_)
    (fun m x hx => (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx) (fun z => ?_)
  · simp only [RingHom.comp_apply]
    have hb := AdicCompletion.extendRingHom_continuous
      ((CompletedTensorProduct.idealOfDefinition R I A B).map
        (algebraMap (CompletedTensorProduct R I A B)
          (Localization.Away (CompletedTensorProduct.inl R I A B f))))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (psiHom I f hI) (psiHom_continuous I f hI) (((hI.map _).map _).map _) m x hx
    exact forwardHom_mem_pow I f hI m hb
  · rw [RingHom.comp_apply, RingHom.id_apply, backwardHom_of, ← RingHom.comp_apply,
      forward_psiHom, algebraMap_eq_of]

/-- backward ∘ forward = id on `CompletedTensorProduct R I (A{1/f}) B`. -/
theorem backward_comp_forward (hI : I.FG) :
    (backwardHom I f hI).comp (forwardHom I f hI) =
      RingHom.id (CompletedTensorProduct R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  refine CompletedTensorProduct.hom_ext
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) hI
    (fun m x hx => ?_) (fun m x hx => hx) (fun a => ?_) (fun b => ?_)
  · simp only [RingHom.comp_apply]
    exact backwardHom_mem_pow I f hI m (forwardHom_mem_pow I f hI m hx)
  · simp only [RingHom.comp_apply, RingHom.id_apply, forwardHom_inl]
    exact DFunLike.congr_fun (backward_forwardAway I f hI) a
  · simp only [RingHom.comp_apply, RingHom.id_apply, forwardHom_inr, forwardHomB_apply,
      backwardHom_awayCompletionHom, gCHom_inr]

/-- **The completed-tensor / away-localization interchange isomorphism.** -/
def equiv (hI : I.FG) :
    CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B ≃+*
      FormalSpectrum.awayCompletion (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) :=
  RingEquiv.ofRingHom (forwardHom I f hI) (backwardHom I f hI)
    (forward_comp_backward I f hI) (backward_comp_forward I f hI)

theorem equiv_apply (hI : I.FG)
    (x : CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :
    equiv I f hI x = forwardHom I f hI x :=
  rfl

/-- The interchange isomorphism carries the ideal of definition of the left onto that of the
right, so it induces an isomorphism of affine formal schemes. -/
theorem equiv_map_idealOfDefinition (hI : I.FG) :
    Ideal.map (equiv I f hI)
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) =
      FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, equiv_apply]
    have := forwardHom_mem_pow I f hI 1 (by rwa [pow_one] : x ∈ _ ^ 1)
    rwa [pow_one] at this
  · intro z hz
    have hz' : equiv I f hI (backwardHom I f hI z) = z := by
      rw [equiv_apply, ← RingHom.comp_apply, forward_comp_backward, RingHom.id_apply]
    rw [← hz']
    refine Ideal.mem_map_of_mem _ ?_
    have := backwardHom_mem_pow I f hI 1 (by rwa [pow_one] : z ∈ _ ^ 1)
    rwa [pow_one] at this

end CompletedTensorAwayInterchange
