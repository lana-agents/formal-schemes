import FormalSchemes.CompletedTensorAwayInterchangePullbackLegs
import FormalSchemes.CompletedTensorAwayInterchangeRight

set_option linter.style.header false
-- The interchange open immersions range over the nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The triple overlap of two second-factor interchange charts, and its two legs

This is the **B-factor mirror** of `FormalSchemes.CompletedTensorAwayInterchangePullback` (+ its
`…Legs`): where the left files localise the *first* tensor factor of `C = A ⊗̂_R B`, here we
localise the *second* factor. Fix an adic base `(R, I)` with `I` finitely generated, an `R`-algebra
`A`, an
affine base change `B`. For an away element `g : B` the **second-factor interchange open immersion**
`CompletedTensorAwayInterchange.rightInterchangeOpenImmersion I g hI`
(`FormalSchemes.CompletedTensorAwayInterchangeRight`) realises `Spf(A ⊗̂_R (B{1/g}))` as the basic
open `D(inr g) ⊆ Spf C`.

This file records that the **pullback** (triple overlap) of two such charts, cut out by away
elements `g₁, g₂ : B`, is again a second-factor interchange chart — the one at the *product*
`g₁ · g₂` — together with the identification of its two projection legs with the geometric
further-localization maps.

## Main results

* `CompletedTensorAwayInterchange.range_rightInterchangeOpenImmersion_mul`: the range of the chart
  at `g₁ · g₂` is the intersection of the ranges of the charts at `g₁` and `g₂` (shadow of
  `inr (g₁ g₂) = inr g₁ · inr g₂`).
* `CompletedTensorAwayInterchange.rightInterchangePullbackIso`: the isomorphism
  `Spf(A ⊗̂_R (B{1/(g₁ g₂)})) ≅ pullback` of the two charts.
* `CompletedTensorAwayInterchange.commSpfIso_hom_naturality`: naturality of the commutativity
  isomorphism of formal spectra with respect to `mapSpf`. This is the crux that transports the
  established left-factor leg laws (`interchange_fst_key` / `interchange_snd_key`) across the
  conjugation defining `rightInterchangeOpenImmersion`.
* `CompletedTensorAwayInterchange.rightInterchangePullbackIso_hom_fst` / `_hom_snd`: the two legs of
  the pullback isomorphism, each equal to `mapSpf hI (AlgHom.id R A) (furtherLoc… I g₁ g₂ hI)`.

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

/-! ### Naturality of the commutativity isomorphism with respect to `mapSpf` -/

section Naturality

variable {A' B' : Type u} [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']

/-- **Ring-level naturality of the swap under functoriality.** For `φ : A →ₐ[R] A'` and
`ψ : B →ₐ[R] B'`, the completed-tensor functorial map intertwines with the commutativity
isomorphism: `(map ψ φ) ∘ commEquiv(A,B) = commEquiv(A',B') ∘ (map φ ψ)` as ring homomorphisms
`A ⊗̂_R B →+* B' ⊗̂_R A'`. Proved by the completed-tensor universal property, checking on the two
canonical generators via `map_inl`/`map_inr` and `commEquiv_inl`/`commEquiv_inr`. -/
private theorem map_commEquiv_fwd (hI : I.FG) (φ : A →ₐ[R] A') (ψ : B →ₐ[R] B') :
    (CompletedTensorProduct.map hI ψ φ).comp
        (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).toRingHom =
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A') (B := B') hI).toRingHom.comp
        (CompletedTensorProduct.map hI φ ψ) := by
  haveI : IsAdicComplete (CompletedTensorProduct.idealOfDefinition R I B' A')
      (CompletedTensorProduct R I B' A') :=
    (CompletedTensorProduct.isAdicRing R I B' A' hI).toIsAdicComplete
  refine CompletedTensorProduct.hom_ext
    (CompletedTensorProduct.idealOfDefinition R I B' A') hI
    (fun m x hx => ?_) (fun m x hx => ?_) (fun a => ?_) (fun b => ?_)
  · rw [RingHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI ψ φ m
      (CompletedTensorProduct.commHom_mem_pow hI m hx)
  · rw [RingHom.comp_apply]
    exact CompletedTensorProduct.commHom_mem_pow hI m
      (CompletedTensorProduct.map_mem_pow hI φ ψ m hx)
  · simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe,
      CompletedTensorProduct.commEquiv_inl,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr]
  · simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe,
      CompletedTensorProduct.commEquiv_inr,
      CompletedTensorProduct.map_inl, CompletedTensorProduct.map_inr]

/-- Unfolding of the `Iso.inv` leg of `CompletedTensorAwayInterchange.commSpfIso` to the raw
`locallyRingedSpaceMap` of `CompletedTensorProduct.commEquiv`. -/
theorem commSpfIso_inv_eq (hI : I.FG) :
    (commSpfIso (A := A) (B := B) I hI).inv =
      FormalSpectrum.locallyRingedSpaceMap (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).toRingHom
        (isAdicHom_commEquiv I hI).le_comap :=
  rfl

/-- **Naturality of the commutativity iso of formal spectra (`Iso.inv` form).**
`mapSpf hI ψ φ ≫ commSpfIso(A,B).inv = commSpfIso(A',B').inv ≫ mapSpf hI φ ψ`. Reduces, through
`locallyRingedSpaceMap_comp`, to the ring-level naturality `map_commEquiv_fwd`. -/
theorem commSpfIso_inv_naturality (φ : A →ₐ[R] A') (ψ : B →ₐ[R] B') (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI ψ φ ≫ (commSpfIso (A := A) (B := B) I hI).inv =
      (commSpfIso (A := A') (B := B') I hI).inv ≫ CompletedTensorProduct.mapSpf hI φ ψ := by
  rw [CompletedTensorProduct.mapSpf_eq, CompletedTensorProduct.mapSpf_eq, commSpfIso_inv_eq,
    commSpfIso_inv_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.idealOfDefinition R I B A)
      (CompletedTensorProduct.idealOfDefinition R I B' A')
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).toRingHom
      (CompletedTensorProduct.map hI ψ φ) _ _
      ((isAdicHom_commEquiv I hI).comp (CompletedTensorProduct.map_isAdicHom hI ψ φ)).le_comap,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.idealOfDefinition R I A' B')
      (CompletedTensorProduct.idealOfDefinition R I B' A')
      (CompletedTensorProduct.map hI φ ψ)
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A') (B := B') hI).toRingHom _ _
      ((CompletedTensorProduct.map_isAdicHom hI φ ψ).comp
        (isAdicHom_commEquiv (A := A') (B := B') I hI)).le_comap]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ (map_commEquiv_fwd I hI φ ψ)

/-- **Naturality of the commutativity iso of formal spectra (`hom` form).**
`mapSpf hI φ ψ ≫ commSpfIso(A,B).hom = commSpfIso(A',B').hom ≫ mapSpf hI ψ φ`. Obtained from the
`Iso.inv` form by cancelling the isomorphisms. -/
theorem commSpfIso_hom_naturality (φ : A →ₐ[R] A') (ψ : B →ₐ[R] B') (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI φ ψ ≫ (commSpfIso (A := A) (B := B) I hI).hom =
      (commSpfIso (A := A') (B := B') I hI).hom ≫ CompletedTensorProduct.mapSpf hI ψ φ := by
  have h : (commSpfIso (A := A') (B := B') I hI).inv ≫ CompletedTensorProduct.mapSpf hI φ ψ =
      CompletedTensorProduct.mapSpf hI ψ φ ≫ (commSpfIso (A := A) (B := B) I hI).inv :=
    (commSpfIso_inv_naturality I φ ψ hI).symm
  rw [Iso.inv_comp_eq] at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Naturality

/-! ### The range identity and the pullback isomorphism -/

/-- **The range of the second-factor interchange chart at a product equals the intersection of the
ranges.** The B-factor mirror of `range_interchangeOpenImmersion_mul`: geometrically the basic-open
product rule `D(inr (g₁ g₂)) = D(inr g₁) ∩ D(inr g₂)`, using that `inr` is a ring homomorphism. -/
theorem range_rightInterchangeOpenImmersion_mul (g₁ g₂ : B) (hI : I.FG) :
    Set.range (rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI).base =
      Set.range (rightInterchangeOpenImmersion (A := A) I g₁ hI).base ∩
        Set.range (rightInterchangeOpenImmersion (A := A) I g₂ hI).base := by
  rw [range_rightInterchangeOpenImmersion_base (A := A) I (g₁ * g₂) hI,
    range_rightInterchangeOpenImmersion_base (A := A) I g₁ hI,
    range_rightInterchangeOpenImmersion_base (A := A) I g₂ hI,
    map_mul (CompletedTensorProduct.inr R I A B) g₁ g₂, FormalSpectrum.basicOpen_mul]
  exact TopologicalSpace.Opens.coe_inf _ _

/-- **The triple overlap of two second-factor interchange charts is a second-factor interchange
chart.** The pullback of the charts at `g₁` and `g₂` is canonically isomorphic to the chart
`Spf(A ⊗̂_R (B{1/(g₁ g₂)}))` at the product, via `pullbackIsoOfRangeEq`. -/
def rightInterchangePullbackIso (g₁ g₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₁ hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₂ hI
    (FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I A
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) (g₁ * g₂))) ≅
      pullback (rightInterchangeOpenImmersion (A := A) I g₁ hI)
        (rightInterchangeOpenImmersion (A := A) I g₂ hI)) :=
  letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₁ hI
  letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₂ hI
  letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (rightInterchangeOpenImmersion (A := A) I g₁ hI)
    (rightInterchangeOpenImmersion (A := A) I g₂ hI)
    (rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI)
    (range_rightInterchangeOpenImmersion_mul I g₁ g₂ hI)

/-- Unfolding of `rightInterchangePullbackIso` as the generic `pullbackIsoOfRangeEq`. -/
theorem rightInterchangePullbackIso_eq (g₁ g₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₁ hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₂ hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI
    rightInterchangePullbackIso I g₁ g₂ hI =
      LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
        (rightInterchangeOpenImmersion (A := A) I g₁ hI)
        (rightInterchangeOpenImmersion (A := A) I g₂ hI)
        (rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI)
        (range_rightInterchangeOpenImmersion_mul I g₁ g₂ hI) :=
  rfl

/-! ### The residual leg identities down to `Spf C` -/

/-- The `fst`-leg residual identity for the second-factor charts: `mapSpf hI id φ₁` followed by the
right-interchange chart at `g₁` equals the chart at `g₁ · g₂`. Transported from the left-factor
`interchange_fst_key` (at `(A := B) (B := A)`) across the `commSpfIso` conjugation defining
`rightInterchangeOpenImmersion`, using `commSpfIso_hom_naturality`. -/
theorem rightInterchange_fst_key (g₁ g₂ : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (AlgHom.id R A) (furtherLocFst (A := B) I g₁ g₂ hI) ≫
        rightInterchangeOpenImmersion (A := A) I g₁ hI =
      rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI := by
  unfold rightInterchangeOpenImmersion
  rw [← Category.assoc,
    commSpfIso_hom_naturality I (AlgHom.id R A) (furtherLocFst (A := B) I g₁ g₂ hI) hI,
    Category.assoc,
    reassoc_of% (interchange_fst_key (A := B) (B := A) I g₁ g₂ hI)]

/-- The `snd`-leg residual identity for the second-factor charts: `mapSpf hI id φ₂` followed by the
right-interchange chart at `g₂` equals the chart at `g₁ · g₂`. Mirror of `rightInterchange_fst_key`
using the left-factor `interchange_snd_key`. -/
theorem rightInterchange_snd_key (g₁ g₂ : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (AlgHom.id R A) (furtherLocSnd (A := B) I g₁ g₂ hI) ≫
        rightInterchangeOpenImmersion (A := A) I g₂ hI =
      rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI := by
  unfold rightInterchangeOpenImmersion
  rw [← Category.assoc,
    commSpfIso_hom_naturality I (AlgHom.id R A) (furtherLocSnd (A := B) I g₁ g₂ hI) hI,
    Category.assoc,
    reassoc_of% (interchange_snd_key (A := B) (B := A) I g₁ g₂ hI)]

/-! ### The two legs of `rightInterchangePullbackIso` -/

/-- **The `pullback.fst` leg of the second-factor triple-overlap isomorphism.** It equals the
geometric further-localization map `mapSpf hI (AlgHom.id R A) φ₁` with
`φ₁ = furtherLocFst (A := B) I g₁ g₂ hI : B{1/g₁} →ₐ[R] B{1/(g₁·g₂)}`. -/
theorem rightInterchangePullbackIso_hom_fst (g₁ g₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₁ hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₂ hI
    (rightInterchangePullbackIso I g₁ g₂ hI).hom ≫
        pullback.fst (rightInterchangeOpenImmersion (A := A) I g₁ hI)
          (rightInterchangeOpenImmersion (A := A) I g₂ hI) =
      CompletedTensorProduct.mapSpf hI (AlgHom.id R A) (furtherLocFst (A := B) I g₁ g₂ hI) := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₁ hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₂ hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI
  rw [rightInterchangePullbackIso_eq I g₁ g₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (rightInterchange_fst_key I g₁ g₂ hI)).symm

/-- **The `pullback.snd` leg of the second-factor triple-overlap isomorphism.** It equals the
geometric further-localization map `mapSpf hI (AlgHom.id R A) φ₂` with
`φ₂ = furtherLocSnd (A := B) I g₁ g₂ hI : B{1/g₂} →ₐ[R] B{1/(g₁·g₂)}`. -/
theorem rightInterchangePullbackIso_hom_snd (g₁ g₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₁ hI
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₂ hI
    (rightInterchangePullbackIso I g₁ g₂ hI).hom ≫
        pullback.snd (rightInterchangeOpenImmersion (A := A) I g₁ hI)
          (rightInterchangeOpenImmersion (A := A) I g₂ hI) =
      CompletedTensorProduct.mapSpf hI (AlgHom.id R A) (furtherLocSnd (A := B) I g₁ g₂ hI) := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₁ hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I g₂ hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I (g₁ * g₂) hI
  rw [rightInterchangePullbackIso_eq I g₁ g₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (rightInterchange_snd_key I g₁ g₂ hI)).symm

end CompletedTensorAwayInterchange

end
