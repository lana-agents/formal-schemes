import FormalSchemes.CompletedTensorAwayInterchangeRight

set_option linter.style.header false
-- The formal-spectrum morphisms range over the nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The geometric completed-tensor / away-localization interchange, both factors

The left-factor interchange `CompletedTensorAwayInterchange.interchangeOpenImmersion`
(`FormalSchemes/CompletedTensorAwayInterchangeSpf.lean`) realises the patch `Spf((A{1/a}) ⊗̂_R B)`
as the open subscheme `D(inl a) ⊆ Spf(A ⊗̂_R B)`, and the second-factor mirror
`CompletedTensorAwayInterchange.rightInterchangeOpenImmersion`
(`FormalSchemes/CompletedTensorAwayInterchangeRight.lean`) realises `Spf(A ⊗̂_R (B{1/b}))` as
`D(inr b)`. This file composes the two: for `a : A`, `b : B` it produces the **both-localized**
open immersion

  `Spf((A{1/a}) ⊗̂_R (B{1/b})) ⟶ Spf(A ⊗̂_R B)`

with underlying-space range the intersection `D(inl a) ⊓ D(inr b) ⊆ Spf(A ⊗̂_R B)` (the locus where
both `inl a` and `inr b` are invertible).

The immersion is the composite of the first-factor immersion (localising `A` at `a`, over the base
`B{1/b}`) with the second-factor immersion (localising `B` at `b`):

  `interchangeOpenImmersion (B := B{1/b}) a ≫ rightInterchangeOpenImmersion b`.

Being a composite of two open immersions it is an open immersion; its range is computed by
transporting the range `D(inl a)` of the first factor across the second immersion, which
identifies `(rightInterchangeOpenImmersion b)⁻¹ D(inl a) = D(inl a)` (the first-factor coordinate is
untouched by the second-factor localization) and intersects with the range `D(inr b)` of the second
immersion (`Set.image_preimage_eq_inter_range`).

## Main results

* `CompletedTensorAwayInterchange.bothInterchangeOpenImmersion`: the both-factor interchange
  morphism `Spf((A{1/a}) ⊗̂_R (B{1/b})) ⟶ Spf(A ⊗̂_R B)`.
* `CompletedTensorAwayInterchange.isOpenImmersion_bothInterchangeOpenImmersion`: it is a
  `LocallyRingedSpace.IsOpenImmersion`.
* `CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base`: its underlying-space
  range is `D(inl a) ⊓ D(inr b) ⊆ Spf(A ⊗̂_R B)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **The both-factor interchange open immersion** `Spf((A{1/a}) ⊗̂_R (B{1/b})) ⟶ Spf(A ⊗̂_R B)`,
the composite of the first-factor immersion `interchangeOpenImmersion` (localising `A` at `a`, over
the base `B{1/b}`) with the second-factor immersion `rightInterchangeOpenImmersion` (localising `B`
at `b`). It realises the both-localized patch `Spf((A{1/a}) ⊗̂_R (B{1/b}))` as the open subscheme
`D(inl a) ⊓ D(inr b) ⊆ Spf(A ⊗̂_R B)`. -/
def bothInterchangeOpenImmersion (a : A) (b : B) (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a)
        (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) ⟶
      FormalSpectrum.locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I A B) :=
  interchangeOpenImmersion (A := A)
      (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI ≫
    rightInterchangeOpenImmersion (A := A) I b hI

/-- **The both-factor interchange open immersion is a `LocallyRingedSpace.IsOpenImmersion`**: it is
the composite of the first-factor open immersion (`isOpenImmersion_interchangeOpenImmersion`) with
the second-factor open immersion (`isOpenImmersion_rightInterchangeOpenImmersion`), and a composite
of open immersions is an open immersion. -/
theorem isOpenImmersion_bothInterchangeOpenImmersion (a : A) (b : B) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion
      (bothInterchangeOpenImmersion (A := A) (B := B) I a b hI) := by
  haveI := isOpenImmersion_interchangeOpenImmersion (A := A)
    (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
  unfold bothInterchangeOpenImmersion
  infer_instance

/-! ### Single-leg preimage-of-basic-open computations

The second-factor interchange immersion factors as three legs
`commSpfIso(A, B{1/b}).hom ≫ interchangeOpenImmersion(B, A) ≫ commSpfIso(B, A).hom`. Each leg's
preimage of a basic open is again a basic open, computed via `FormalSpectrum.map_preimage_basicOpen`
(the maps are `locallyRingedSpaceMap`s, whose base is `mapTop`). The three lemmas here transport the
first-factor coordinate `inl a` across the legs, following the chase
`D(inl_{A,B} a) ↦ D(inr_{B,A} a) ↦ D(inr_{B{1/b},A} a) ↦ D(inl_{A,B{1/b}} a)`. -/

/-- **Leg `commSpfIso(B, A).hom`:** its base preimage of `D(inl_{A,B} a) ⊆ Spf(A ⊗̂_R B)` is
`D(inr_{B,A} a) ⊆ Spf(B ⊗̂_R A)`. The level map is `mapTop` of `commEquiv(B,A).symm`, which sends
the class of `inl_{A,B} a` to that of `inr_{B,A} a` (`commEquiv_inr` read backwards). -/
private theorem commSpfIso_hom_base_preimage_inl (a : A) (hI : I.FG) :
    ⇑(commSpfIso (A := B) (B := A) I hI).hom.base ⁻¹'
        (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B a) :
          Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B))) =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.inr R I B A a) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I B A))) := by
  have hval :
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := B) (B := A) hI).symm.toRingHom
        (CompletedTensorProduct.inl R I A B a) = CompletedTensorProduct.inr R I B A a := by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq,
      CompletedTensorProduct.commEquiv_inr]
  have hpre := FormalSpectrum.map_preimage_basicOpen
    (CompletedTensorProduct.idealOfDefinition R I A B)
    (CompletedTensorProduct.idealOfDefinition R I B A)
    (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := B) (B := A) hI).symm.toRingHom
    (FormalSpectrum.isAdicHom_ringEquiv_symm
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := B) (B := A) hI)
      (isAdicHom_commEquiv (A := B) (B := A) I hI)).le_comap
    (CompletedTensorProduct.inl R I A B a)
  rw [hval] at hpre
  exact congrArg SetLike.coe hpre

/-- **Leg `commSpfIso(A, B{1/b}).hom`:** its base preimage of the basic open
`D(inr_{B{1/b},A} a) ⊆ Spf(B{1/b} ⊗̂ A)` is `D(inl_{A,B{1/b}} a) ⊆ Spf(A ⊗̂ B{1/b})`. The level map
is `mapTop` of `commEquiv(A,B{1/b}).symm`, which sends the class of `inr_{B{1/b},A} a` to that of
`inl_{A,B{1/b}} a` (`commEquiv_inl` backwards). -/
private theorem commSpfIso_hom_base_preimage_inr (a : A) (b : B) (hI : I.FG) :
    ⇑(commSpfIso (A := A)
        (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I hI).hom.base ⁻¹'
        (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A)
          (CompletedTensorProduct.inr R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A a) :
          Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A))) =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b))
        (CompletedTensorProduct.inl R I A
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) a) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)))) := by
  have hval :
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A)
          (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) hI).symm.toRingHom
        (CompletedTensorProduct.inr R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A a) =
      CompletedTensorProduct.inl R I A
        (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) a := by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq,
      CompletedTensorProduct.commEquiv_inl]
  have hpre := FormalSpectrum.map_preimage_basicOpen
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A)
    (CompletedTensorProduct.idealOfDefinition R I A
      (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b))
    (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A)
      (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) hI).symm.toRingHom
    (FormalSpectrum.isAdicHom_ringEquiv_symm
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A)
        (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) hI)
      (isAdicHom_commEquiv (A := A)
        (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I hI)).le_comap
    (CompletedTensorProduct.inr R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A a)
  rw [hval] at hpre
  exact congrArg SetLike.coe hpre

/-- **Middle leg `interchangeOpenImmersion(B, A)`:** its base preimage of
`D(inr_{B,A} a) ⊆ Spf(B ⊗̂ A)` is `D(inr_{B{1/b},A} a) ⊆ Spf(B{1/b} ⊗̂ A)`. This immersion localizes
only the *first* factor `B` at `b`; the orthogonal second-factor coordinate `inr a` is preserved.
It factors as `equivSpfIso(B,A).hom ≫ basicOpenChart`; the chart leg carries `inr_{B,A} a` to
`awayCompletionHom (inr_{B,A} a)`, and the `equivSpfIso` leg (level map `equiv(B,A).symm =
backwardHom`) carries that back to `inr_{B{1/b},A} a` (`backwardHom_awayCompletionHom`,
`gCHom_inr`). -/
private theorem interchange_base_preimage_inr (a : A) (b : B) (hI : I.FG) :
    ⇑(interchangeOpenImmersion (A := B) (B := A) I b hI).base ⁻¹'
        (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inr R I B A a) :
          Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I B A))) =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A)
        (CompletedTensorProduct.inr R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A a) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A))) := by
  have hchart :
      ⇑(FormalSpectrum.basicOpenChart (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inl R I B A b)).base ⁻¹'
        (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inr R I B A a) :
          Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I B A))) =
      (FormalSpectrum.basicOpen
          (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I B A)
            (CompletedTensorProduct.inl R I B A b))
          (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I B A)
            (CompletedTensorProduct.inl R I B A b) (CompletedTensorProduct.inr R I B A a)) :
          Set (FormalSpectrum (FormalSpectrum.awayCompletionIdeal
            (CompletedTensorProduct.idealOfDefinition R I B A)
            (CompletedTensorProduct.inl R I B A b)))) := by
    have hpre := FormalSpectrum.map_preimage_basicOpen
      (CompletedTensorProduct.idealOfDefinition R I B A)
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.inl R I B A b))
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.inl R I B A b))
      (FormalSpectrum.le_comap_awayCompletionHom
        (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.inl R I B A b))
      (CompletedTensorProduct.inr R I B A a)
    exact congrArg SetLike.coe hpre
  have hval :
      (equiv (A := B) (B := A) I b hI).symm.toRingHom
        (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inl R I B A b) (CompletedTensorProduct.inr R I B A a)) =
      CompletedTensorProduct.inr R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A a := by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, equiv_apply,
      forwardHom_inr, forwardHomB_apply]
  have hequiv :
      ⇑(equivSpfIso (A := B) (B := A) I b hI).hom.base ⁻¹'
        (FormalSpectrum.basicOpen
          (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I B A)
            (CompletedTensorProduct.inl R I B A b))
          (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I B A)
            (CompletedTensorProduct.inl R I B A b) (CompletedTensorProduct.inr R I B A a)) :
          Set (FormalSpectrum (FormalSpectrum.awayCompletionIdeal
            (CompletedTensorProduct.idealOfDefinition R I B A)
            (CompletedTensorProduct.inl R I B A b)))) =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A)
        (CompletedTensorProduct.inr R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A a) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A))) := by
    have hpre := FormalSpectrum.map_preimage_basicOpen
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.inl R I B A b))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) A)
      (equiv (A := B) (B := A) I b hI).symm.toRingHom
      (FormalSpectrum.isAdicHom_ringEquiv_symm (equiv (A := B) (B := A) I b hI)
        (isAdicHom_equiv (A := B) (B := A) I b hI)).le_comap
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.inl R I B A b) (CompletedTensorProduct.inr R I B A a))
    rw [hval] at hpre
    exact congrArg SetLike.coe hpre
  have hcomp : ⇑(interchangeOpenImmersion (A := B) (B := A) I b hI).base =
      ⇑(FormalSpectrum.basicOpenChart (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inl R I B A b)).base ∘
        ⇑(equivSpfIso (A := B) (B := A) I b hI).hom.base := by
    unfold interchangeOpenImmersion
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.preimage_comp, hchart, hequiv]

/-- **The preimage of the first-factor basic open `D(inl a)` under the second-factor interchange
immersion is `D(inl a)`.** The second-factor immersion `rightInterchangeOpenImmersion b` localizes
only the *second* tensor factor, so it leaves the first-factor coordinate `inl a` untouched:
`(rightInterchangeOpenImmersion b)⁻¹ D(inl_{A,B} a) = D(inl_{A,B{1/b}} a)`. -/
theorem rightInterchange_base_preimage_inl (a : A) (b : B) (hI : I.FG) :
    ⇑(rightInterchangeOpenImmersion (A := A) I b hI).base ⁻¹'
        (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B a) :
          Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B)))
      = (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b))
          (CompletedTensorProduct.inl R I A
            (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) a) :
          Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A
            (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)))) := by
  have hcomp : ⇑(rightInterchangeOpenImmersion (A := A) I b hI).base =
      ⇑(commSpfIso (A := B) (B := A) I hI).hom.base ∘
        ⇑(interchangeOpenImmersion (A := B) (B := A) I b hI).base ∘
          ⇑(commSpfIso (A := A)
            (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I hI).hom.base := by
    unfold rightInterchangeOpenImmersion
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.preimage_comp, Set.preimage_comp,
    commSpfIso_hom_base_preimage_inl I a hI,
    interchange_base_preimage_inr I a b hI,
    commSpfIso_hom_base_preimage_inr I a b hI]

/-- **The underlying-space range of the both-factor interchange open immersion** is the intersection
`D(inl a) ⊓ D(inr b) ⊆ Spf(A ⊗̂_R B)`. The base map factors as the first-factor immersion (range
`D(inl a)`) followed by the second-factor immersion (range `D(inr b)`); the image of `D(inl a)`
under the second immersion is `D(inl a) ∩ range = D(inl a) ⊓ D(inr b)`
(`Set.image_preimage_eq_inter_range`, using `rightInterchange_base_preimage_inl` and
`range_rightInterchangeOpenImmersion_base`). -/
theorem range_bothInterchangeOpenImmersion_base (a : A) (b : B) (hI : I.FG) :
    Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I a b hI).base =
      (↑(FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B a) ⊓
        FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inr R I A B b)) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B))) := by
  unfold bothInterchangeOpenImmersion
  have hcomp : ⇑(interchangeOpenImmersion (A := A)
        (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI ≫
        rightInterchangeOpenImmersion (A := A) I b hI).base =
      ⇑(rightInterchangeOpenImmersion (A := A) I b hI).base ∘
        ⇑(interchangeOpenImmersion (A := A)
          (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI).base := by
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.range_comp,
    range_interchangeOpenImmersion_base (A := A)
      (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI,
    ← rightInterchange_base_preimage_inl (A := A) (B := B) I a b hI,
    Set.image_preimage_eq_inter_range,
    range_rightInterchangeOpenImmersion_base (A := A) I b hI]
  exact (TopologicalSpace.Opens.coe_inf _ _).symm

end CompletedTensorAwayInterchange
