import FormalSchemes.CompletedTensorAwayInterchangeRightPullback
import FormalSchemes.CompletedTensorAwayInterchangeBoth
import FormalSchemes.CompletedTensorAwayInterchangePullbackLegs

set_option linter.style.header false
-- The interchange open immersions range over the nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The mixed (first × second) interchange triple overlap, and its two legs

This is the **mixed** analogue of `FormalSchemes.CompletedTensorAwayInterchangePullback` (which
overlaps two *first*-factor charts) and `FormalSchemes.CompletedTensorAwayInterchangeRightPullback`
(which overlaps two *second*-factor charts). Fix an adic base `(R, I)` with `I` finitely generated,
`R`-algebras `A B`, and away elements `a : A`, `b : B`. Write `C = A ⊗̂_R B`. The two charts

* `f₁ = interchangeOpenImmersion I a hI : Spf(A{1/a} ⊗̂_R B) ⟶ Spf C`, range `D(inl a)`, and
* `f₂ = rightInterchangeOpenImmersion I b hI : Spf(A ⊗̂_R B{1/b}) ⟶ Spf C`, range `D(inr b)`,

localise *different* tensor factors. This file records that their **pullback** (triple overlap) is
the both-localized chart `both = bothInterchangeOpenImmersion I a b hI`, whose range is
`D(inl a) ⊓ D(inr b)`, together with the identification of the two projection legs.

## Main results

* `CompletedTensorAwayInterchange.range_interchange_inter_rightInterchange`: the range of `both` is
  the intersection of the ranges of `f₁` and `f₂`.
* `CompletedTensorAwayInterchange.mixedInterchangePullbackIso`: the isomorphism
  `Spf(A{1/a} ⊗̂_R B{1/b}) ≅ pullback f₁ f₂`.
* `CompletedTensorAwayInterchange.mixedInterchange_fst_key`: the commutativity square
  "localise `B` then `A` = localise `A` then `B`", the crux behind the `fst` leg. Both interchange
  charts are `mapSpf` of the localization `R`-algebra maps, so the square is `mapSpf`-functoriality.
* `CompletedTensorAwayInterchange.mixedInterchangePullbackIso_hom_fst` / `_hom_snd`: the two legs of
  the pullback isomorphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

namespace CompletedTensorAwayInterchange

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-! ### The interchange charts as `mapSpf` of the localization `R`-algebra maps

The first-factor interchange chart at `a` localises `A` at `a` and is untouched on `B`; the
second-factor chart at `b` localises `B` at `b` and is untouched on `A`. Recorded here as `mapSpf`
of the completed-localization `R`-algebra maps `A →ₐ[R] A{1/a}` and `B →ₐ[R] B{1/b}`
(`IsScalarTower.toAlgHom`). This makes both charts objects of the `mapSpf` functor calculus, so the
mixed commutativity square reduces to `mapSpf`-functoriality. -/

/-- **The completed-tensor lift `gCHom` is `map` of the localization algebra map.** The ring shadow
of "the first-factor interchange chart is `mapSpf` of the `A`-localization": on generators both send
`inl x ↦ inl (loc_a x)` and `inr y ↦ inr y`. -/
theorem gCHom_eq_map (f : A) (hI : I.FG) :
    gCHom I f hI =
      CompletedTensorProduct.map hI
        (IsScalarTower.toAlgHom R A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f))
        (AlgHom.id R B) := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  refine CompletedTensorProduct.hom_ext
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) hI
    (fun m x hx => ?_) (fun m x hx => ?_) (fun a => ?_) (fun b => ?_)
  · exact gCHom_mem_pow I f hI m hx
  · exact CompletedTensorProduct.map_mem_pow hI _ _ m hx
  · rw [gCHom_inl I f hI a, gA_apply I f a, CompletedTensorProduct.map_inl,
      IsScalarTower.toAlgHom_apply]
  · rw [gCHom_inr I f hI b, CompletedTensorProduct.map_inr, AlgHom.id_apply]

/-- **The first-factor interchange open immersion is `mapSpf` of the `A`-localization.**
`interchangeOpenImmersion I a hI = mapSpf hI (A →ₐ A{1/a}) (id B)`. -/
theorem interchangeOpenImmersion_eq_mapSpf (f : A) (hI : I.FG) :
    interchangeOpenImmersion (B := B) I f hI =
      CompletedTensorProduct.mapSpf hI
        (IsScalarTower.toAlgHom R A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f))
        (AlgHom.id R B) := by
  rw [interchangeOpenImmersion_eq_map I f hI, CompletedTensorProduct.mapSpf_eq]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ (gCHom_eq_map I f hI)

/-! ### The commutativity isomorphism `hom` as an `inv`, and the double-swap identity -/

/-- The `hom` leg of `commSpfIso (A, B)` is the `inv` leg of the flipped `commSpfIso (B, A)`.
Both are `Spf` of the same underlying ring map `commEquiv (A, B).symm = commHom (B, A)`; only the
(propositional) continuity witnesses differ, and `locallyRingedSpaceMap` ignores those. -/
theorem commSpfIso_hom_eq_inv (hI : I.FG) :
    (commSpfIso (A := A) (B := B) I hI).hom = (commSpfIso (A := B) (B := A) I hI).inv :=
  rfl

/-- **The double swap is the identity.** `commSpfIso (A, B).hom ≫ commSpfIso (B, A).hom = 𝟙`, since
the second leg is the inverse of the first (`commSpfIso_hom_eq_inv`). -/
theorem commSpfIso_hom_comp_hom (hI : I.FG) :
    (commSpfIso (A := A) (B := B) I hI).hom ≫ (commSpfIso (A := B) (B := A) I hI).hom =
      𝟙 (FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I A B)) := by
  rw [commSpfIso_hom_eq_inv I hI]
  exact Iso.inv_hom_id _

/-- **The second-factor interchange open immersion is `mapSpf` of the `B`-localization.**
`rightInterchangeOpenImmersion I b hI = mapSpf hI (id A) (B →ₐ B{1/b})`. Its conjugation definition
turns, via `interchangeOpenImmersion_eq_mapSpf` (localising the *first* factor `B` of `B ⊗̂_R A`),
`commSpfIso_hom_naturality`, and the double-swap identity, into the plain second-factor `mapSpf`. -/
theorem rightInterchangeOpenImmersion_eq_mapSpf (b : B) (hI : I.FG) :
    rightInterchangeOpenImmersion (A := A) I b hI =
      CompletedTensorProduct.mapSpf hI (AlgHom.id R A)
        (IsScalarTower.toAlgHom R B
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) := by
  unfold rightInterchangeOpenImmersion
  rw [interchangeOpenImmersion_eq_mapSpf (A := B) (B := A) I b hI,
    commSpfIso_hom_naturality I
      (IsScalarTower.toAlgHom R B (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b))
      (AlgHom.id R A) hI,
    ← Category.assoc, commSpfIso_hom_comp_hom I hI, Category.id_comp]

/-! ### The range identity and the pullback isomorphism -/

/-- **The range of the both-factor chart is the intersection of the two mixed charts' ranges.**
`range both = range f₁ ∩ range f₂`, the shadow of `D(inl a) ⊓ D(inr b)`. -/
theorem range_interchange_inter_rightInterchange (a : A) (b : B) (hI : I.FG) :
    Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I a b hI).base =
      Set.range (interchangeOpenImmersion (B := B) I a hI).base ∩
        Set.range (rightInterchangeOpenImmersion (A := A) I b hI).base := by
  rw [range_bothInterchangeOpenImmersion_base I a b hI,
    range_interchangeOpenImmersion_base (B := B) I a hI,
    range_rightInterchangeOpenImmersion_base (A := A) I b hI]
  exact TopologicalSpace.Opens.coe_inf _ _

/-- **The mixed triple overlap is the both-localized chart.** The pullback of the first-factor chart
at `a` and the second-factor chart at `b` is canonically isomorphic to `Spf(A{1/a} ⊗̂_R B{1/b})`,
via `pullbackIsoOfRangeEq`. -/
def mixedInterchangePullbackIso (a : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
    (FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a)
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) ≅
      pullback (interchangeOpenImmersion (B := B) I a hI)
        (rightInterchangeOpenImmersion (A := A) I b hI)) :=
  letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a hI
  letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
  letI := isOpenImmersion_bothInterchangeOpenImmersion I a b hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (interchangeOpenImmersion (B := B) I a hI)
    (rightInterchangeOpenImmersion (A := A) I b hI)
    (bothInterchangeOpenImmersion (A := A) (B := B) I a b hI)
    (range_interchange_inter_rightInterchange I a b hI)

/-- Unfolding of `mixedInterchangePullbackIso` as the generic `pullbackIsoOfRangeEq`. -/
theorem mixedInterchangePullbackIso_eq (a : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a b hI
    mixedInterchangePullbackIso I a b hI =
      LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
        (interchangeOpenImmersion (B := B) I a hI)
        (rightInterchangeOpenImmersion (A := A) I b hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a b hI)
        (range_interchange_inter_rightInterchange I a b hI) :=
  rfl

/-! ### The residual leg identities down to `Spf C` -/

/-- The `snd`-leg residual identity: the first-factor chart at `a` (over `B{1/b}`) followed by the
second-factor chart at `b` equals the both-factor chart. Definitional. -/
theorem mixedInterchange_snd_key (a : A) (b : B) (hI : I.FG) :
    interchangeOpenImmersion (A := A)
        (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI ≫
        rightInterchangeOpenImmersion (A := A) I b hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I a b hI :=
  rfl

/-- **The mixed commutativity square (crux).** Localising `B` first then `A` equals localising `A`
first then `B`: the second-factor chart at `b` (over `A{1/a}`) followed by the first-factor chart at
`a` equals the both-factor chart. Since every interchange chart is `mapSpf` of a localization
`R`-algebra map (`interchangeOpenImmersion_eq_mapSpf`, `rightInterchangeOpenImmersion_eq_mapSpf`),
both composites are `mapSpf hI (A →ₐ A{1/a}) (B →ₐ B{1/b})` by `mapSpf`-functoriality. -/
theorem mixedInterchange_fst_key (a : A) (b : B) (hI : I.FG) :
    rightInterchangeOpenImmersion
        (A := FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a) I b hI ≫
        interchangeOpenImmersion (B := B) I a hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I a b hI := by
  unfold bothInterchangeOpenImmersion
  rw [interchangeOpenImmersion_eq_mapSpf (B := B) I a hI,
    interchangeOpenImmersion_eq_mapSpf
      (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI,
    rightInterchangeOpenImmersion_eq_mapSpf
      (A := FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a) I b hI,
    rightInterchangeOpenImmersion_eq_mapSpf (A := A) I b hI,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp]
  simp only [AlgHom.id_comp, AlgHom.comp_id]

/-! ### The two legs of `mixedInterchangePullbackIso` -/

/-- **The `pullback.snd` leg of the mixed triple-overlap isomorphism.** It equals the first-factor
interchange chart at `a` over the localised base `B{1/b}`. -/
theorem mixedInterchangePullbackIso_hom_snd (a : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
    (mixedInterchangePullbackIso I a b hI).hom ≫
        pullback.snd (interchangeOpenImmersion (B := B) I a hI)
          (rightInterchangeOpenImmersion (A := A) I b hI) =
      interchangeOpenImmersion (A := A)
        (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I a hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a b hI
  rw [mixedInterchangePullbackIso_eq I a b hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (mixedInterchange_snd_key I a b hI)).symm

/-- **The `pullback.fst` leg of the mixed triple-overlap isomorphism.** It equals the second-factor
interchange chart at `b` over the localised base `A{1/a}`; the identification is the mixed
commutativity square `mixedInterchange_fst_key`. -/
theorem mixedInterchangePullbackIso_hom_fst (a : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
    (mixedInterchangePullbackIso I a b hI).hom ≫
        pullback.fst (interchangeOpenImmersion (B := B) I a hI)
          (rightInterchangeOpenImmersion (A := A) I b hI) =
      rightInterchangeOpenImmersion
        (A := FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a) I b hI := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I a hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a b hI
  rw [mixedInterchangePullbackIso_eq I a b hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (mixedInterchange_fst_key I a b hI)).symm

end CompletedTensorAwayInterchange

end
