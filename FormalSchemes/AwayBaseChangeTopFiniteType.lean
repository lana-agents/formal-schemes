import FormalSchemes.AdicCompletionCongrIdealAlg
import FormalSchemes.AwayTopFiniteType
import FormalSchemes.CompletedTensorAwayInterchange
import FormalSchemes.TopFiniteTypeBaseChange

set_option linter.style.header false
set_option linter.style.setOption false
-- The composite runs through three nested localization/completion towers (`R{1/c}^ ⊗̂_R A`, the
-- interchange, and `A{1/(c·A)}^`); the `isDefEq` checks that unfold `awayCompletion` and
-- `CompletedTensorProduct` through `AdicCompletion` are what costs the heartbeats.
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The away base change of a topologically-finite-type algebra (EGA I §10.13)

Let `(R, I)` be an adic base with `I` finitely generated, let `A` be an `R`-algebra which is
topologically of finite type over `(R, I)` with ideal of definition `L = I·A`, and let `c : R`.
Shrinking the target chart `Spf R` to the basic open `D(c)` replaces the base by the completed
localization `R{1/c}^` and the source by `A{1/(c·A)}^`. This file proves that the shrunk source is
again topologically of finite type over the shrunk base:

```
A{1/(c·A)}^  is tf-type over  (R{1/c}^, I{1/c}^).
```

This is the **base-side** away statement. The tree already had two others, and all three must stay
apart:

* `IsTopologicallyFiniteType.awayCompletion` (`FormalSchemes.AwayTopFiniteType`) is the
  **source**-side statement: `A{1/g}^` is tf-type over the *unchanged* base `(R, I)`, for `g : A`.
* `IsTopologicallyFiniteType.awayCompletion_base` is that one's specialisation `A = R`, `L = I`.
* This file moves the **base**: both rings are localized, at `c : R` downstairs and at its image
  `algebraMap R A c` upstairs, and the conclusion is a tf-type statement over a *new* base ring.

It is the one new algebraic ingredient that EGA I 10.13's composition law at a non-affine target
needs: an `X`-chart which is tf-type over a target chart `Spf I` has to be re-read as tf-type over
a *shrunk* target chart `Spf (I{1/c})` when two covers of `Y` are refined against each other, and
that re-reading is this statement.

## The algebra structure, and why it is an argument

There is **no** `Algebra (R{1/c}^) (A{1/(c·A)}^)` instance, and none can be found by unification:
`R{1/c}^` and `A{1/(c·A)}^` are completions of localizations of two different rings at two
different elements. The structure has to be built, and this file builds it:

* `FormalSpectrum.awayBaseLocHom`: the localization-level map `R_c → A_{c·A}`, the
  `IsLocalization.Away.lift` of `c`, which is a unit there because it is the image of the away
  element itself;
* `FormalSpectrum.awayBaseHom`: its completion `R{1/c}^ →+* A{1/(c·A)}^`;
* `FormalSpectrum.awayBaseAlgebra`: the induced algebra structure, which the theorem below installs
  with `letI`.

`IsTopologicallyFiniteType.awayCompletion_baseChange_of_algebraMap_eq` is the form for a caller who
already holds an algebra structure — for instance the one an
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn` datum existentially supplies — and can
identify its structure map with `FormalSpectrum.awayBaseHom`.

## Route

The composite is a chain of three surjections out of the completed base change:

1. `IsTopologicallyFiniteType.baseChange` at `S := R{1/c}^` gives that `R{1/c}^ ⊗̂_R A` is tf-type
   over `(R{1/c}^, I·R{1/c}^)`, and `FormalSpectrum.map_algebraMap_awayCompletion` identifies the
   base ideal with `awayCompletionIdeal I c`;
2. `CompletedTensorAwayInterchange.equiv` at interchange-`A := R`, interchange-`B := A`,
   interchange-`f := c` — note the slot assignment: the interchange localizes its *first* tensor
   factor, and the factor being localized here is the **base** `R`, not `A` — identifies
   `R{1/c}^ ⊗̂_R A` with `(R ⊗̂_R A){1/inl c}^`. Its source is spelled
   `awayCompletion (I.map (algebraMap R R)) c`, which is not the *type* `awayCompletion I c`, so
   the chain opens with `AdicCompletion.congrIdealₐ` transporting between them;
3. `CompletedTensorProduct.unitEquiv` absorbs the first factor, `R ⊗̂_R A ≃+* A`, and
   `FormalSpectrum.awayCompletionEquivOfRingEquiv` carries that isomorphism through the completed
   localization, using `CompletedTensorProduct.map_unitEquiv` (the unitor on the ideal of
   definition) and `CompletedTensorProduct.unitEquiv_inl` (the unitor on the away element).

`IsTopologicallyFiniteType.of_surjective` then transports the tf-type predicate along the
composite, which is a surjective `R{1/c}^`-algebra map.

## Main definitions and results

* `FormalSpectrum.awayLocEquivOfRingEquiv` and `FormalSpectrum.awayCompletionEquivOfRingEquiv`:
  transport of a completed localization along a **ring equivalence between different rings**,
  carrying one ideal of definition to the other and one away element to the other. The tree's two
  reusable congruences are both within a single ring —
  `CompletedTensorAwayInterchange.awayCongrHom` in the element and
  `FormalSpectrum.awayCompletionCongrₐ` in the ideal — and neither applies. The construction itself
  is not new: `annulusOverlapTransitionHom` (`FormalSchemes.TateTransition`) is exactly it, for the
  coordinate swap of the annulus algebra, but spelled throughout in Tate-specific abbreviations
  rather than in `awayCompletion`.
* `CompletedTensorProduct.map_unitEquiv`: the left unitor `R ⊗̂_R A ≃+* A` carries the ideal of
  definition of `R ⊗̂_R A` onto `I·A`. The tree had `CompletedTensorProduct.unitEquiv_inl` and
  `CompletedTensorProduct.unitEquiv_inr`, the unitor on elements, but nothing on the ideal.
* `FormalSpectrum.awayBaseHom` and `FormalSpectrum.awayBaseAlgebra`, described above.
* `IsTopologicallyFiniteType.awayCompletion_baseChange`: the theorem.
* `RestrictedPowerSeries.isTopologicallyFiniteType_awayCompletion_baseChange`: the polydisc
  instance — `R{X₁, …, Xₙ}{1/c}^` is tf-type over `(R{1/c}^, I{1/c}^)`.

## Hypotheses, and what is not proved

* The standing `[IsAdicComplete (I.map (algebraMap R A)) A]` is what the left unitor
  `CompletedTensorProduct.unitEquiv` needs, and it is **not** implied by the tf-type predicate: a
  presentation is only known to make `A` complete once its kernel is adically closed
  (`IsTopologicallyFiniteType.isAdicRing`) or the base is Noetherian
  (`IsTopologicallyFiniteType.isAdicRing_of_noetherian`). In the geometric setting it is free —
  there `Spf A` is an affine formal scheme, so `A` carries `IsAdicRing L`.
* **Nothing here mentions formal schemes.** EGA I 10.13's composition law at a non-affine target,
  the assembly of the refined cover it needs, and conservativity of
  `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` are all elsewhere; this file is the ring
  lemma they consume.
* The transport `FormalSpectrum.awayCompletionEquivOfRingEquiv` is stated for a ring equivalence
  only. The one-sided statement — a surjection `C ↠ A` inducing `C{1/k}^ ↠ A{1/σ k}^` — is not
  proved and is not needed here.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/

noncomputable section

open Ideal

universe u

namespace FormalSpectrum

/-! ### Transport of a completed localization along a ring equivalence -/

section Congr

variable {C A : Type u} [CommRing C] [CommRing A]

/-- **The localization transport.** A ring equivalence `σ : C ≃+* A` carries the powers of `k` onto
the powers of `σ k`, hence induces `C_k ≃+* A_{σ k}`. -/
def awayLocEquivOfRingEquiv (σ : C ≃+* A) (k : C) :
    Localization.Away k ≃+* Localization.Away (σ k) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.Away k) (Localization.Away (σ k)) σ
    (show (Submonoid.powers k).map σ.toMonoidHom = Submonoid.powers (σ k) from
      Submonoid.map_powers σ.toMonoidHom k)

@[simp]
theorem awayLocEquivOfRingEquiv_algebraMap (σ : C ≃+* A) (k : C) (x : C) :
    awayLocEquivOfRingEquiv σ k (algebraMap C (Localization.Away k) x) =
      algebraMap A (Localization.Away (σ k)) (σ x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

@[simp]
theorem awayLocEquivOfRingEquiv_symm_algebraMap (σ : C ≃+* A) (k : C) (y : A) :
    (awayLocEquivOfRingEquiv σ k).symm (algebraMap A (Localization.Away (σ k)) y) =
      algebraMap C (Localization.Away k) (σ.symm y) := by
  rw [RingEquiv.symm_apply_eq, awayLocEquivOfRingEquiv_algebraMap, RingEquiv.apply_symm_apply]

/-- The localization transport carries `K·C_k` onto `M·A_{σ k}`, for `σ` carrying `K` onto `M`. -/
theorem map_awayLocEquivOfRingEquiv (σ : C ≃+* A) {K : Ideal C} {M : Ideal A}
    (hKM : K.map (σ : C →+* A) = M) (k : C) :
    (K.map (algebraMap C (Localization.Away k))).map (awayLocEquivOfRingEquiv σ k).toRingHom =
      M.map (algebraMap A (Localization.Away (σ k))) := by
  rw [Ideal.map_map, ← hKM, Ideal.map_map]
  congr 1
  ext x
  simp

/-- The inverse direction of `FormalSpectrum.map_awayLocEquivOfRingEquiv`. -/
theorem map_awayLocEquivOfRingEquiv_symm (σ : C ≃+* A) {K : Ideal C} {M : Ideal A}
    (hKM : K.map (σ : C →+* A) = M) (k : C) :
    (M.map (algebraMap A (Localization.Away (σ k)))).map
        (awayLocEquivOfRingEquiv σ k).symm.toRingHom =
      K.map (algebraMap C (Localization.Away k)) := by
  rw [← map_awayLocEquivOfRingEquiv σ hKM k, Ideal.map_map]
  convert Ideal.map_id _
  ext x
  simp

/-- **Transport of a completed localization along a ring equivalence.** A ring equivalence
`σ : C ≃+* A` carrying the ideal `K` onto `M` and the element `k` to `a` induces
`C{1/k}^ ≃+* A{1/a}^`, obtained by completing the localization transport
`FormalSpectrum.awayLocEquivOfRingEquiv`.

The two reusable congruences already on the tree are both *within a single ring* and neither
applies: `CompletedTensorAwayInterchange.awayCongrHom` varies the away element with the ring fixed,
and `FormalSpectrum.awayCompletionCongrₐ` varies the ideal with the ring fixed. The proof is the
one of `FormalSpectrum.awayCompletionSelfMulRingEquiv` (`FormalSchemes.AwayCompletionSelfMul`),
which is the same construction for the special case `σ = id`, `k = g`, `a = g * g`. -/
def awayCompletionEquivOfRingEquiv (σ : C ≃+* A) {K : Ideal C} {M : Ideal A}
    (hKM : K.map (σ : C →+* A) = M) (hK : K.FG) (hM : M.FG) {k : C} {a : A} (hka : σ k = a) :
    awayCompletion K k ≃+* awayCompletion M a := by
  subst hka
  let φ := (awayLocEquivOfRingEquiv σ k).toRingHom
  let ψ := (awayLocEquivOfRingEquiv σ k).symm.toRingHom
  let KC : Ideal (Localization.Away k) := K.map (algebraMap C (Localization.Away k))
  let KA : Ideal (Localization.Away (σ k)) := M.map (algebraMap A (Localization.Away (σ k)))
  have hKCFG : KC.FG := hK.map _
  have hKAFG : KA.FG := hM.map _
  have hfwd : KC.map φ ≤ KA := le_of_eq (map_awayLocEquivOfRingEquiv σ hKM k)
  have hbwd : KA.map ψ ≤ KC := le_of_eq (map_awayLocEquivOfRingEquiv_symm σ hKM k)
  haveI : IsAdicComplete (AdicCompletion.idealOfDefinition KC) (AdicCompletion KC _) :=
    (AdicCompletion.isAdicRing_map _ hKCFG).toIsAdicComplete
  haveI : IsAdicComplete (AdicCompletion.idealOfDefinition KA) (AdicCompletion KA _) :=
    (AdicCompletion.isAdicRing_map _ hKAFG).toIsAdicComplete
  refine RingEquiv.ofRingHom
    (AdicCompletion.mapCompletion φ hfwd hKAFG)
    (AdicCompletion.mapCompletion ψ hbwd hKCFG) ?_ ?_
  · refine AdicCompletion.hom_ext_of_continuous KA (AdicCompletion.idealOfDefinition KA) hKAFG
      (fun m x hx => ?_)
      (fun m x hx => (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx) (fun y => ?_)
    · have h1 := AdicCompletion.mapCompletion_mem_pow ψ hbwd hKCFG hKAFG m hx
      rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
      exact AdicCompletion.mapCompletion_mem_pow φ hfwd hKAFG hKCFG m h1
    · rw [RingHom.comp_apply, AdicCompletion.mapCompletion_of,
        AdicCompletion.mapCompletion_algebraMap,
        show φ (ψ y) = y from (awayLocEquivOfRingEquiv σ k).apply_symm_apply y,
        AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        RingHom.id_apply]
  · refine AdicCompletion.hom_ext_of_continuous KC (AdicCompletion.idealOfDefinition KC) hKCFG
      (fun m x hx => ?_)
      (fun m x hx => (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx) (fun y => ?_)
    · have h1 := AdicCompletion.mapCompletion_mem_pow φ hfwd hKAFG hKCFG m hx
      rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
      exact AdicCompletion.mapCompletion_mem_pow ψ hbwd hKCFG hKAFG m h1
    · rw [RingHom.comp_apply, AdicCompletion.mapCompletion_of,
        AdicCompletion.mapCompletion_algebraMap,
        show ψ (φ y) = y from (awayLocEquivOfRingEquiv σ k).symm_apply_apply y,
        AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        RingHom.id_apply]

/-- The transport fixes the structural image of `C`, read through `σ`. -/
theorem awayCompletionEquivOfRingEquiv_algebraMap (σ : C ≃+* A) {K : Ideal C} {M : Ideal A}
    (hKM : K.map (σ : C →+* A) = M) (hK : K.FG) (hM : M.FG) {k : C} {a : A} (hka : σ k = a)
    (x : C) :
    awayCompletionEquivOfRingEquiv σ hKM hK hM hka (algebraMap C (awayCompletion K k) x) =
      algebraMap A (awayCompletion M a) (σ x) := by
  subst hka
  have happ : ∀ y, awayCompletionEquivOfRingEquiv σ hKM hK hM (rfl : σ k = σ k) y =
      AdicCompletion.mapCompletion (awayLocEquivOfRingEquiv σ k).toRingHom
        (le_of_eq (map_awayLocEquivOfRingEquiv σ hKM k)) (hM.map _) y := fun _ => rfl
  rw [IsScalarTower.algebraMap_apply C (Localization.Away k) (awayCompletion K k), happ,
    AdicCompletion.mapCompletion_algebraMap, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, awayLocEquivOfRingEquiv_algebraMap,
    ← IsScalarTower.algebraMap_apply A (Localization.Away (σ k)) (awayCompletion M (σ k))]

end Congr

end FormalSpectrum

/-! ### The left unitor on the ideal of definition -/

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A]
variable [IsAdicComplete (I.map (algebraMap R A)) A]

/-- **The left unitor carries the ideal of definition onto `I·A`.** `CompletedTensorProduct`'s
`CompletedTensorProduct.unitEquiv_inl` and `CompletedTensorProduct.unitEquiv_inr` compute the
unitor on elements; this is the corresponding statement for the ideal of definition, which is what
makes `CompletedTensorProduct.unitEquiv` an isomorphism of *adic* rings and hence usable as an
input to `FormalSpectrum.awayCompletionEquivOfRingEquiv`. -/
theorem map_unitEquiv (hI : I.FG) :
    (idealOfDefinition R I R A).map
        ((unitEquiv (A := A) hI : CompletedTensorProduct R I R A ≃+* A) :
          CompletedTensorProduct R I R A →+* A) =
      I.map (algebraMap R A) := by
  rw [idealOfDefinition_eq_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply,
    show algebraMap R (CompletedTensorProduct R I R A) r = inl R I R A r by
      rw [← (inl R I R A).commutes r, Algebra.algebraMap_self, RingHom.id_apply]]
  exact unitEquiv_inl hI r

end CompletedTensorProduct

/-! ### The structural map `R{1/c}^ → A{1/(c·A)}^` -/

namespace FormalSpectrum

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}

/-- The base element `c` becomes a unit in `A_{c·A}`: its image there is the image of the away
element `algebraMap R A c` itself. -/
theorem isUnit_algebraMap_awayLocBase (c : R) :
    IsUnit (algebraMap R (Localization.Away (algebraMap R A c)) c) := by
  rw [IsScalarTower.algebraMap_apply R A (Localization.Away (algebraMap R A c))]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The localization-level structural map `R_c → A_{c·A}`, the `IsLocalization.Away.lift` of `c`. -/
def awayBaseLocHom (A : Type u) [CommRing A] [Algebra R A] (c : R) :
    Localization.Away c →+* Localization.Away (algebraMap R A c) :=
  IsLocalization.Away.lift (S := Localization.Away c) c (isUnit_algebraMap_awayLocBase (A := A) c)

theorem awayBaseLocHom_comp_algebraMap (c : R) :
    (awayBaseLocHom A c).comp (algebraMap R (Localization.Away c)) =
      algebraMap R (Localization.Away (algebraMap R A c)) :=
  IsLocalization.Away.lift_comp c _

theorem map_awayBaseLocHom (c : R) (hL : I.map (algebraMap R A) = L) :
    (I.map (algebraMap R (Localization.Away c))).map (awayBaseLocHom A c) =
      L.map (algebraMap A (Localization.Away (algebraMap R A c))) := by
  rw [Ideal.map_map, awayBaseLocHom_comp_algebraMap, ← hL, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

theorem fg_map_awayLoc (c : R) (hI : I.FG) (hL : I.map (algebraMap R A) = L) :
    (L.map (algebraMap A (Localization.Away (algebraMap R A c)))).FG := by
  rw [← map_awayBaseLocHom c hL]
  exact (hI.map _).map _

/-- **The structural map `R{1/c}^ → A{1/(c·A)}^`** of the away base change: the completion of
`FormalSpectrum.awayBaseLocHom`. There is no
`Algebra (awayCompletion I c) (awayCompletion L (algebraMap R A c))` instance — the two rings are
completions of localizations of two different rings at two different elements — so this map, and
the algebra structure `FormalSpectrum.awayBaseAlgebra` it induces, are what the away base-change
theorem's statement is *relative to*. -/
def awayBaseHom (c : R) (hI : I.FG) (hL : I.map (algebraMap R A) = L) :
    awayCompletion I c →+* awayCompletion L (algebraMap R A c) :=
  AdicCompletion.mapCompletion (awayBaseLocHom A c) (le_of_eq (map_awayBaseLocHom c hL))
    (fg_map_awayLoc c hI hL)

theorem awayBaseHom_apply (c : R) (hI : I.FG) (hL : I.map (algebraMap R A) = L)
    (x : awayCompletion I c) :
    awayBaseHom c hI hL x =
      AdicCompletion.mapCompletion (awayBaseLocHom A c) (le_of_eq (map_awayBaseLocHom c hL))
        (fg_map_awayLoc c hI hL) x :=
  rfl

/-- The structural map is a map of `R`-algebras: it is the completion of a localization map
under `R`. -/
theorem awayBaseHom_comp_algebraMap (c : R) (hI : I.FG) (hL : I.map (algebraMap R A) = L) :
    (awayBaseHom c hI hL).comp (algebraMap R (awayCompletion I c)) =
      algebraMap R (awayCompletion L (algebraMap R A c)) := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply R (Localization.Away c) (awayCompletion I c),
    awayBaseHom_apply, AdicCompletion.mapCompletion_algebraMap,
    show awayBaseLocHom A c (algebraMap R (Localization.Away c) r) =
        algebraMap R (Localization.Away (algebraMap R A c)) r from
      RingHom.congr_fun (awayBaseLocHom_comp_algebraMap (A := A) c) r,
    ← IsScalarTower.algebraMap_apply R (Localization.Away (algebraMap R A c))
      (awayCompletion L (algebraMap R A c))]

/-- **The `R{1/c}^`-algebra structure on `A{1/(c·A)}^`** induced by `FormalSpectrum.awayBaseHom`.
Not an instance: it depends on the proof-arguments `hI` and `hL`, and the pair
`(R{1/c}^, A{1/(c·A)}^)` carries no canonical structure findable by unification. -/
@[reducible]
def awayBaseAlgebra (c : R) (hI : I.FG) (hL : I.map (algebraMap R A) = L) :
    Algebra (awayCompletion I c) (awayCompletion L (algebraMap R A c)) :=
  (awayBaseHom c hI hL).toAlgebra

end FormalSpectrum

/-! ### The composite `R{1/c}^ ⊗̂_R A ↠ A{1/(c·A)}^` -/

namespace FormalSpectrum

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}

/-- Ideal-extension bookkeeping used for every continuity obligation below: a map of `R`-algebras
carries the `m`-th power of `I·X` into the `m`-th power of `I·Y`. -/
theorem mem_map_pow_of_comp_algebraMap {X Y : Type u} [CommRing X] [CommRing Y] [Algebra R X]
    [Algebra R Y] (F : X →+* Y) (hF : F.comp (algebraMap R X) = algebraMap R Y) (m : ℕ) {x : X}
    (hx : x ∈ (I.map (algebraMap R X)) ^ m) : F x ∈ (I.map (algebraMap R Y)) ^ m := by
  have h := Ideal.mem_map_of_mem F hx
  rwa [Ideal.map_pow, Ideal.map_map, hF] at h

variable [IsAdicComplete (I.map (algebraMap R A)) A]

/-- The interchange isomorphism spells its source chart with the ideal `I.map (algebraMap R R)`
rather than with `I`; this is the transport between the two spellings, which are equal ideals of
the same ring. -/
def awayBaseSelfCongr (c : R) :
    awayCompletion (I.map (algebraMap R R)) c ≃ₐ[R] awayCompletion I c :=
  AdicCompletion.congrIdealₐ R
    (show (I.map (algebraMap R R)).map (algebraMap R (Localization.Away c)) =
        I.map (algebraMap R (Localization.Away c)) by
      rw [Algebra.algebraMap_self, Ideal.map_id])

/-- **The away base change, as a surjection out of the completed base change**: the composite

```
R{1/c}^ ⊗̂_R A  →  R{1/c}^ ⊗̂_R A  ≃  (R ⊗̂_R A){1/inl c}^  ≃  A{1/(c·A)}^
```

of the ideal-spelling transport, the completed-tensor/away interchange at interchange-`A := R` and
interchange-`B := A`, and the transport of the left unitor `R ⊗̂_R A ≃+* A` through the completed
localization. -/
def awayBaseTensorHom (c : R) (hI : I.FG) (hL : I.map (algebraMap R A) = L) :
    CompletedTensorProduct R I (awayCompletion I c) A →+* awayCompletion L (algebraMap R A c) :=
  ((awayCompletionEquivOfRingEquiv (CompletedTensorProduct.unitEquiv (A := A) hI)
      ((CompletedTensorProduct.map_unitEquiv hI).trans hL) ((hI.map _).map _) (hL ▸ hI.map _)
      (CompletedTensorProduct.unitEquiv_inl hI c)).toRingHom).comp
    (((CompletedTensorAwayInterchange.equiv (A := R) (B := A) I c hI).toRingHom).comp
      (CompletedTensorProduct.map hI (awayBaseSelfCongr c).symm.toAlgHom (AlgHom.id R A)))

theorem awayBaseTensorHom_surjective (c : R) (hI : I.FG) (hL : I.map (algebraMap R A) = L) :
    Function.Surjective (awayBaseTensorHom c hI hL) := by
  simp only [awayBaseTensorHom, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp
    ((RingEquiv.surjective _).comp
      (CompletedTensorProduct.map_surjective hI (AlgEquiv.surjective _) Function.surjective_id))

/-- The composite is a map of `R`-algebras: each of its three factors is. -/
theorem awayBaseTensorHom_comp_algebraMap (c : R) (hI : I.FG)
    (hL : I.map (algebraMap R A) = L) :
    (awayBaseTensorHom c hI hL).comp
        (algebraMap R (CompletedTensorProduct R I (awayCompletion I c) A)) =
      algebraMap R (awayCompletion L (algebraMap R A c)) := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply]
  simp only [awayBaseTensorHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [show algebraMap R (CompletedTensorProduct R I (awayCompletion I c) A) r =
        CompletedTensorProduct.inl R I (awayCompletion I c) A (algebraMap R (awayCompletion I c) r)
      from ((CompletedTensorProduct.inl R I (awayCompletion I c) A).commutes r).symm,
    CompletedTensorProduct.map_inl,
    show (awayBaseSelfCongr (I := I) c).symm.toAlgHom (algebraMap R (awayCompletion I c) r) =
        algebraMap R (awayCompletion (I.map (algebraMap R R)) c) r from
      (awayBaseSelfCongr (I := I) c).symm.commutes r,
    CompletedTensorAwayInterchange.equiv_apply, CompletedTensorAwayInterchange.forwardHom_inl,
    AlgHom.commutes,
    IsScalarTower.algebraMap_apply R (CompletedTensorProduct R I R A)
      (awayCompletion (CompletedTensorProduct.idealOfDefinition R I R A)
        (CompletedTensorProduct.inl R I R A c)),
    awayCompletionEquivOfRingEquiv_algebraMap,
    show CompletedTensorProduct.unitEquiv (A := A) hI
          (algebraMap R (CompletedTensorProduct R I R A) r) = algebraMap R A r by
      rw [show algebraMap R (CompletedTensorProduct R I R A) r =
            CompletedTensorProduct.inl R I R A r by
          rw [← (CompletedTensorProduct.inl R I R A).commutes r, Algebra.algebraMap_self,
            RingHom.id_apply]]
      exact CompletedTensorProduct.unitEquiv_inl hI r,
    ← IsScalarTower.algebraMap_apply R A (awayCompletion L (algebraMap R A c))]

/-- **The composite restricts on the base factor to `FormalSpectrum.awayBaseHom`**, so it is a map
of `R{1/c}^`-algebras for the structure `FormalSpectrum.awayBaseAlgebra`. Both sides are ring
homomorphisms out of the completion `R{1/c}^` which preserve the filtration and agree on the image
of `R`; the completion's uniqueness principle `AdicCompletion.hom_ext_of_continuous` and the
localization's (`IsLocalization.ringHom_ext`) then identify them. -/
theorem awayBaseTensorHom_comp_algebraMap_base (c : R) (hI : I.FG)
    (hL : I.map (algebraMap R A) = L) :
    (awayBaseTensorHom c hI hL).comp
        (algebraMap (awayCompletion I c) (CompletedTensorProduct R I (awayCompletion I c) A)) =
      awayBaseHom c hI hL := by
  have hFalg : ((awayBaseTensorHom c hI hL).comp
        (algebraMap (awayCompletion I c)
          (CompletedTensorProduct R I (awayCompletion I c) A))).comp
        (algebraMap R (awayCompletion I c)) =
      algebraMap R (awayCompletion L (algebraMap R A c)) := by
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, awayBaseTensorHom_comp_algebraMap]
  have hGalg := awayBaseHom_comp_algebraMap (A := A) c hI hL
  have hIc : I.map (algebraMap R (awayCompletion I c)) = awayCompletionIdeal I c :=
    map_algebraMap_awayCompletion c (by rw [Algebra.algebraMap_self, Ideal.map_id])
  have hLa : I.map (algebraMap R (awayCompletion L (algebraMap R A c))) =
      awayCompletionIdeal L (algebraMap R A c) := map_algebraMap_awayCompletion _ hL
  haveI : IsAdicComplete (awayCompletionIdeal L (algebraMap R A c))
      (awayCompletion L (algebraMap R A c)) :=
    (AdicCompletion.isAdicRing_map _ (fg_map_awayLoc c hI hL)).toIsAdicComplete
  refine AdicCompletion.hom_ext_of_continuous (I.map (algebraMap R (Localization.Away c)))
    (awayCompletionIdeal L (algebraMap R A c)) (hI.map _) (fun m x hx => ?_) (fun m x hx => ?_)
    (fun y => ?_)
  · rw [← hLa]
    refine mem_map_pow_of_comp_algebraMap _ hFalg m ?_
    rw [hIc]
    exact (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx
  · rw [← hLa]
    refine mem_map_pow_of_comp_algebraMap _ hGalg m ?_
    rw [hIc]
    exact (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx
  · have key : ((awayBaseTensorHom c hI hL).comp
          (algebraMap (awayCompletion I c)
            (CompletedTensorProduct R I (awayCompletion I c) A))).comp
          (algebraMap (Localization.Away c) (awayCompletion I c)) =
        (awayBaseHom c hI hL).comp (algebraMap (Localization.Away c) (awayCompletion I c)) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers c) (RingHom.ext fun r => ?_)
      have h1 := RingHom.congr_fun hFalg r
      have h2 := RingHom.congr_fun hGalg r
      simp only [RingHom.comp_apply] at h1 h2 ⊢
      rw [← IsScalarTower.algebraMap_apply R (Localization.Away c) (awayCompletion I c), h1, h2]
    have hy := RingHom.congr_fun key y
    rwa [RingHom.comp_apply, RingHom.comp_apply,
      show algebraMap (Localization.Away c) (awayCompletion I c) y =
          AdicCompletion.of (I.map (algebraMap R (Localization.Away c))) (Localization.Away c) y by
        rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]] at hy

end FormalSpectrum

/-! ### The theorem -/

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}
variable [IsAdicComplete (I.map (algebraMap R A)) A]

/-- **The away base change of a tf-type algebra, for a given algebra structure** (EGA I §10.13):
if `A` is topologically of finite type over `(R, I)` and the `R{1/c}^`-algebra structure on
`A{1/(c·A)}^` is the one induced by `FormalSpectrum.awayBaseHom`, then `A{1/(c·A)}^` is
topologically of finite type over `(R{1/c}^, I{1/c}^)`.

This is the form for a caller who already holds an algebra structure — for instance the one an
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn` datum existentially supplies — and can
identify its structure map with `FormalSpectrum.awayBaseHom`. The unprimed
`IsTopologicallyFiniteType.awayCompletion_baseChange` below is the form that installs the structure
itself.

Every chart type below is spelled `FormalSpectrum.awayCompletion` in full. That is not decoration:
inside a declaration whose name lies in the `IsTopologicallyFiniteType` namespace, a bare
`awayCompletion` resolves to the *source*-side theorem
`IsTopologicallyFiniteType.awayCompletion` instead. -/
theorem _root_.IsTopologicallyFiniteType.awayCompletion_baseChange_of_algebraMap_eq
    (hI : I.FG) (h : IsTopologicallyFiniteType R I A L) (c : R)
    [Algebra (FormalSpectrum.awayCompletion I c)
      (FormalSpectrum.awayCompletion L (algebraMap R A c))]
    (halg : algebraMap (FormalSpectrum.awayCompletion I c)
        (FormalSpectrum.awayCompletion L (algebraMap R A c)) =
      FormalSpectrum.awayBaseHom c hI h.map_eq) :
    IsTopologicallyFiniteType (FormalSpectrum.awayCompletion I c)
      (FormalSpectrum.awayCompletionIdeal I c)
      (FormalSpectrum.awayCompletion L (algebraMap R A c))
      (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) := by
  have hbase : IsTopologicallyFiniteType (FormalSpectrum.awayCompletion I c)
      (FormalSpectrum.awayCompletionIdeal I c)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion I c) A)
      (CompletedTensorProduct.idealOfDefinition R I (FormalSpectrum.awayCompletion I c) A) := by
    have hbc := IsTopologicallyFiniteType.baseChange
      (S := FormalSpectrum.awayCompletion I c) hI h
    rwa [FormalSpectrum.map_algebraMap_awayCompletion c
      (by rw [Algebra.algebraMap_self, Ideal.map_id])] at hbc
  let π : CompletedTensorProduct R I (FormalSpectrum.awayCompletion I c) A →ₐ[
        FormalSpectrum.awayCompletion I c] FormalSpectrum.awayCompletion L (algebraMap R A c) :=
    { FormalSpectrum.awayBaseTensorHom c hI h.map_eq with
      commutes' := fun s => by
        rw [halg]
        exact RingHom.congr_fun
          (FormalSpectrum.awayBaseTensorHom_comp_algebraMap_base c hI h.map_eq) s }
  have hπ : π.toRingHom = FormalSpectrum.awayBaseTensorHom c hI h.map_eq := rfl
  refine IsTopologicallyFiniteType.of_surjective hbase π
    (FormalSpectrum.awayBaseTensorHom_surjective c hI h.map_eq) ?_
  rw [CompletedTensorProduct.idealOfDefinition_eq_map, hπ, Ideal.map_map,
    FormalSpectrum.awayBaseTensorHom_comp_algebraMap,
    FormalSpectrum.map_algebraMap_awayCompletion _ h.map_eq]

/-- **The away base change of a tf-type algebra** (EGA I §10.13): if `A` is topologically of finite
type over `(R, I)` with ideal of definition `L = I·A` and `c : R`, then the completed localization
`A{1/(c·A)}^` is topologically of finite type over the completed localization `(R{1/c}^, I{1/c}^)`
of the base, for the algebra structure `FormalSpectrum.awayBaseAlgebra`.

This is the base-side companion of
`IsTopologicallyFiniteType.awayCompletion`, which localizes the *source* `A` and keeps the base
`(R, I)` fixed, and of its specialisation `IsTopologicallyFiniteType.awayCompletion_base`, which is
that source-side statement at `A = R`. Here **both** rings are localized: `R` at `c` and `A` at the
image `algebraMap R A c`.

The hypothesis `[IsAdicComplete (I.map (algebraMap R A)) A]` is what the left unitor
`CompletedTensorProduct.unitEquiv` needs, and it is not implied by the tf-type predicate — a
presentation is only known to make `A` complete once its kernel is adically closed
(`IsTopologicallyFiniteType.isAdicRing`). In the geometric setting it is free: there `Spf A` is an
affine formal scheme, so `A` carries `IsAdicRing L`. -/
theorem _root_.IsTopologicallyFiniteType.awayCompletion_baseChange (hI : I.FG)
    (h : IsTopologicallyFiniteType R I A L) (c : R) :
    letI := FormalSpectrum.awayBaseAlgebra c hI h.map_eq
    IsTopologicallyFiniteType (FormalSpectrum.awayCompletion I c)
      (FormalSpectrum.awayCompletionIdeal I c)
      (FormalSpectrum.awayCompletion L (algebraMap R A c))
      (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) :=
  letI := FormalSpectrum.awayBaseAlgebra c hI h.map_eq
  IsTopologicallyFiniteType.awayCompletion_baseChange_of_algebraMap_eq hI h c rfl

end AlgebraicGeometry

/-! ### A first consumer: the polydisc -/

namespace RestrictedPowerSeries

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- **The away base change of the formal polydisc**: `R{X₁, …, Xₙ}{1/c}^` is topologically of
finite type over `(R{1/c}^, I{1/c}^)`, for `c : R` a *base* element.

The first consumer of
`IsTopologicallyFiniteType.awayCompletion_baseChange`, and a non-vacuity witness for it: the
conclusion is a genuinely new statement about a genuinely new ring, and its proof does nothing but
instantiate the theorem at the polydisc's identity presentation
(`RestrictedPowerSeries.isTopologicallyFiniteType`). The polydisc is complete
(`RestrictedPowerSeries.isAdicRing`), which is what discharges the theorem's standing
`IsAdicComplete` hypothesis. -/
theorem isTopologicallyFiniteType_awayCompletion_baseChange (hI : I.FG) (n : ℕ) (c : R) :
    letI : IsAdicComplete (I.map (algebraMap R (RestrictedPowerSeries R I n)))
        (RestrictedPowerSeries R I n) :=
      idealOfDefinition_eq_map R I n ▸ (isAdicRing R I n hI).toIsAdicComplete
    letI := FormalSpectrum.awayBaseAlgebra c hI (isTopologicallyFiniteType R I n).map_eq
    IsTopologicallyFiniteType (FormalSpectrum.awayCompletion I c)
      (FormalSpectrum.awayCompletionIdeal I c)
      (FormalSpectrum.awayCompletion (idealOfDefinition R I n)
        (algebraMap R (RestrictedPowerSeries R I n) c))
      (FormalSpectrum.awayCompletionIdeal (idealOfDefinition R I n)
        (algebraMap R (RestrictedPowerSeries R I n) c)) :=
  letI : IsAdicComplete (I.map (algebraMap R (RestrictedPowerSeries R I n)))
      (RestrictedPowerSeries R I n) :=
    idealOfDefinition_eq_map R I n ▸ (isAdicRing R I n hI).toIsAdicComplete
  IsTopologicallyFiniteType.awayCompletion_baseChange hI
    (isTopologicallyFiniteType R I n) c

end RestrictedPowerSeries

end
