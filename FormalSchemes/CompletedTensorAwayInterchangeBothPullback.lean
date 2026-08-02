import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.CompletedTensorAwayInterchangeRightPullback

set_option linter.style.header false
-- The interchange open immersions range over the nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The both-involving interchange pullbacks: the 1st × both overlap and its two legs

This continues `FormalSchemes.CompletedTensorAwayInterchangeMixedPullback` (the mixed 1st × 2nd
overlap) and the same-factor pullbacks `…InterchangePullback(Legs)` (LEFT, two first-factor charts)
/ `…InterchangeRightPullback` (RIGHT, two second-factor charts). It handles the overlap of a
first-factor chart with a **both-factor** chart. Fix an adic base `(R, I)` with `I` finitely
generated, `R`-algebras `A B`, and away elements `a₁ a₂ : A`, `b : B`. Write `C = A ⊗̂_R B`. The two
charts

* `f₁ = interchangeOpenImmersion I a₁ hI : Spf(A{1/a₁} ⊗̂_R B) ⟶ Spf C`, range `D(inl a₁)`, and
* `f₂ = bothInterchangeOpenImmersion I a₂ b hI : Spf(A{1/a₂} ⊗̂_R B{1/b}) ⟶ Spf C`, range
  `D(inl a₂) ⊓ D(inr b)`,

overlap in `D(inl a₁) ⊓ D(inl a₂) ⊓ D(inr b) = D(inl (a₁·a₂)) ⊓ D(inr b)`, the range of the
both-localized chart `both = bothInterchangeOpenImmersion I (a₁·a₂) b hI`.

The proof reuses the observation unlocked by the mixed file: every interchange chart is `mapSpf` of
the localization `R`-algebra maps, so each leg identity is `mapSpf`-functoriality composed with the
further-localization algebra identity `furtherLoc ∘ loc = loc`.

## Main results

* `CompletedTensorAwayInterchange.bothInterchangeOpenImmersion_eq_mapSpf`: the both-factor chart is
  `mapSpf hI (A →ₐ A{1/a}) (B →ₐ B{1/b})` — the reusable brick for all both-involving legs.
* `CompletedTensorAwayInterchange.range_interchange_inter_both`: the range of `both (a₁·a₂) b` is
  the intersection of the ranges of `f₁` and `f₂`.
* `CompletedTensorAwayInterchange.firstBothInterchangePullbackIso`: the isomorphism
  `Spf(A{1/(a₁·a₂)} ⊗̂_R B{1/b}) ≅ pullback f₁ f₂`.
* `CompletedTensorAwayInterchange.firstBothInterchangePullbackIso_hom_fst` / `_hom_snd`: the two
  legs of the pullback isomorphism, each `mapSpf` of a further-localization on `A` and a
  localization on `B`.

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

/-! ### The both-factor chart as `mapSpf` of the two localization maps -/

/-- **The both-factor interchange open immersion is `mapSpf` of the two localizations.**
`bothInterchangeOpenImmersion I a b hI = mapSpf hI (A →ₐ A{1/a}) (B →ₐ B{1/b})`. It is defined as
the composite `interchange (B := B{1/b}) a ≫ right b`, and both factors are `mapSpf` of a single
localization (`interchangeOpenImmersion_eq_mapSpf`, `rightInterchangeOpenImmersion_eq_mapSpf`), so
`mapSpf`-functoriality collapses the composite to the two-sided localization. -/
theorem bothInterchangeOpenImmersion_eq_mapSpf (a : A) (b : B) (hI : I.FG) :
    bothInterchangeOpenImmersion (A := A) (B := B) I a b hI =
      CompletedTensorProduct.mapSpf hI
        (IsScalarTower.toAlgHom R A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a))
        (IsScalarTower.toAlgHom R B
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) := by
  unfold bothInterchangeOpenImmersion
  rw [interchangeOpenImmersion_eq_mapSpf
      (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b) I a hI,
    rightInterchangeOpenImmersion_eq_mapSpf (A := A) I b hI,
    ← CompletedTensorProduct.mapSpf_comp]
  simp only [AlgHom.id_comp, AlgHom.comp_id]

/-! ### The further-localization algebra identities -/

/-- The first further localization composed with the localization at `g₁` is the localization at
`g₁ · g₂`: `furtherLocFst ∘ (A →ₐ A{1/g₁}) = (A →ₐ A{1/(g₁·g₂)})`. -/
theorem furtherLocFst_comp_toAlgHom (g₁ g₂ : A) (hI : I.FG) :
    (furtherLocFst I g₁ g₂ hI).comp
        (IsScalarTower.toAlgHom R A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₁)) =
      IsScalarTower.toAlgHom R A
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂)) := by
  ext a
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply,
    furtherLocFst_algebraMap I g₁ g₂ hI a]

/-- The second further localization composed with the localization at `g₂` is the localization at
`g₁ · g₂`: `furtherLocSnd ∘ (A →ₐ A{1/g₂}) = (A →ₐ A{1/(g₁·g₂)})`. -/
theorem furtherLocSnd_comp_toAlgHom (g₁ g₂ : A) (hI : I.FG) :
    (furtherLocSnd I g₁ g₂ hI).comp
        (IsScalarTower.toAlgHom R A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₂)) =
      IsScalarTower.toAlgHom R A
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂)) := by
  ext a
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply,
    furtherLocSnd_algebraMap I g₁ g₂ hI a]

/-! ### The range identity and the pullback isomorphism (1st × both) -/

/-- **The range of the both-factor chart at `(a₁·a₂, b)` is the intersection of the first-factor
chart at `a₁` and the both-factor chart at `(a₂, b)`.** -/
theorem range_interchange_inter_both (a₁ a₂ : A) (b : B) (hI : I.FG) :
    Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) b hI).base =
      Set.range (interchangeOpenImmersion (B := B) I a₁ hI).base ∩
        Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b hI).base := by
  rw [range_bothInterchangeOpenImmersion_base I (a₁ * a₂) b hI,
    range_interchangeOpenImmersion_base (B := B) I a₁ hI,
    range_bothInterchangeOpenImmersion_base I a₂ b hI,
    map_mul (CompletedTensorProduct.inl R I A B) a₁ a₂,
    FormalSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf,
    TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_inf]
  exact Set.inter_assoc _ _ _

/-- **The 1st × both triple overlap is the both-localized chart at `(a₁·a₂, b)`.** The pullback of
the first-factor chart at `a₁` and the both-factor chart at `(a₂, b)` is canonically isomorphic to
`Spf(A{1/(a₁·a₂)} ⊗̂_R B{1/b})`, via `pullbackIsoOfRangeEq`. -/
def firstBothInterchangePullbackIso (a₁ a₂ : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b hI
    (FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (a₁ * a₂))
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) ≅
      pullback (interchangeOpenImmersion (B := B) I a₁ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b hI)) :=
  letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a₁ hI
  letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b hI
  letI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) b hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (interchangeOpenImmersion (B := B) I a₁ hI)
    (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b hI)
    (bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) b hI)
    (range_interchange_inter_both I a₁ a₂ b hI)

/-- Unfolding of `firstBothInterchangePullbackIso` as the generic `pullbackIsoOfRangeEq`. -/
theorem firstBothInterchangePullbackIso_eq (a₁ a₂ : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) b hI
    firstBothInterchangePullbackIso I a₁ a₂ b hI =
      LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
        (interchangeOpenImmersion (B := B) I a₁ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) b hI)
        (range_interchange_inter_both I a₁ a₂ b hI) :=
  rfl

/-! ### The residual leg identities down to `Spf C` (1st × both) -/

/-- The `fst`-leg residual identity: the further-localization on `A` (from `a₁` to `a₁·a₂`) together
with the localization on `B` at `b`, followed by the first-factor chart at `a₁`, equals the
both-factor chart at `(a₁·a₂, b)`. Pure `mapSpf`-functoriality. -/
theorem firstBoth_fst_key (a₁ a₂ : A) (b : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (furtherLocFst I a₁ a₂ hI)
        (IsScalarTower.toAlgHom R B (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) ≫
        interchangeOpenImmersion (B := B) I a₁ hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) b hI := by
  rw [interchangeOpenImmersion_eq_mapSpf (B := B) I a₁ hI,
    bothInterchangeOpenImmersion_eq_mapSpf I (a₁ * a₂) b hI,
    ← CompletedTensorProduct.mapSpf_comp, furtherLocFst_comp_toAlgHom I a₁ a₂ hI]
  simp only [AlgHom.comp_id]

/-- The `snd`-leg residual identity: the further-localization on `A` (from `a₂` to `a₁·a₂`) with the
identity on `B{1/b}`, followed by the both-factor chart at `(a₂, b)`, equals the both-factor chart
at `(a₁·a₂, b)`. Pure `mapSpf`-functoriality. -/
theorem firstBoth_snd_key (a₁ a₂ : A) (b : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (furtherLocSnd I a₁ a₂ hI)
        (AlgHom.id R (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) ≫
        bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) b hI := by
  rw [bothInterchangeOpenImmersion_eq_mapSpf I a₂ b hI,
    bothInterchangeOpenImmersion_eq_mapSpf I (a₁ * a₂) b hI,
    ← CompletedTensorProduct.mapSpf_comp, furtherLocSnd_comp_toAlgHom I a₁ a₂ hI]
  simp only [AlgHom.id_comp]

/-! ### The two legs of `firstBothInterchangePullbackIso` -/

/-- **The `pullback.fst` leg of the 1st × both triple-overlap isomorphism.** It equals
`mapSpf hI φ₁ (B →ₐ B{1/b})` with `φ₁ = furtherLocFst I a₁ a₂ hI : A{1/a₁} →ₐ[R] A{1/(a₁·a₂)}`. -/
theorem firstBothInterchangePullbackIso_hom_fst (a₁ a₂ : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b hI
    (firstBothInterchangePullbackIso I a₁ a₂ b hI).hom ≫
        pullback.fst (interchangeOpenImmersion (B := B) I a₁ hI)
          (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b hI) =
      CompletedTensorProduct.mapSpf hI (furtherLocFst I a₁ a₂ hI)
        (IsScalarTower.toAlgHom R B
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I a₁ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) b hI
  rw [firstBothInterchangePullbackIso_eq I a₁ a₂ b hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (firstBoth_fst_key I a₁ a₂ b hI)).symm

/-- **The `pullback.snd` leg of the 1st × both triple-overlap isomorphism.** It equals
`mapSpf hI φ₂ (id_{B{1/b}})` with `φ₂ = furtherLocSnd I a₁ a₂ hI : A{1/a₂} →ₐ[R] A{1/(a₁·a₂)}`. -/
theorem firstBothInterchangePullbackIso_hom_snd (a₁ a₂ : A) (b : B) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I a₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b hI
    (firstBothInterchangePullbackIso I a₁ a₂ b hI).hom ≫
        pullback.snd (interchangeOpenImmersion (B := B) I a₁ hI)
          (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b hI) =
      CompletedTensorProduct.mapSpf hI (furtherLocSnd I a₁ a₂ hI)
        (AlgHom.id R (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) b)) := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I a₁ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) b hI
  rw [firstBothInterchangePullbackIso_eq I a₁ a₂ b hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (firstBoth_snd_key I a₁ a₂ b hI)).symm

/-! ### The range identity and the pullback isomorphism (2nd × both) -/

/-- **The range of the both-factor chart at `(a, b₁·b₂)` is the intersection of the second-factor
chart at `b₁` and the both-factor chart at `(a, b₂)`.** -/
theorem range_rightInterchange_inter_both (a : A) (b₁ b₂ : B) (hI : I.FG) :
    Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I a (b₁ * b₂) hI).base =
      Set.range (rightInterchangeOpenImmersion (A := A) I b₁ hI).base ∩
        Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I a b₂ hI).base := by
  rw [range_bothInterchangeOpenImmersion_base I a (b₁ * b₂) hI,
    range_rightInterchangeOpenImmersion_base (A := A) I b₁ hI,
    range_bothInterchangeOpenImmersion_base I a b₂ hI,
    map_mul (CompletedTensorProduct.inr R I A B) b₁ b₂, FormalSpectrum.basicOpen_mul]
  simp only [TopologicalSpace.Opens.coe_inf]
  exact Set.inter_left_comm _ _ _

/-- **The 2nd × both triple overlap is the both-localized chart at `(a, b₁·b₂)`.** -/
def rightBothInterchangePullbackIso (a : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a b₂ hI
    (FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a)
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) (b₁ * b₂))) ≅
      pullback (rightInterchangeOpenImmersion (A := A) I b₁ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a b₂ hI)) :=
  letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b₁ hI
  letI := isOpenImmersion_bothInterchangeOpenImmersion I a b₂ hI
  letI := isOpenImmersion_bothInterchangeOpenImmersion I a (b₁ * b₂) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (rightInterchangeOpenImmersion (A := A) I b₁ hI)
    (bothInterchangeOpenImmersion (A := A) (B := B) I a b₂ hI)
    (bothInterchangeOpenImmersion (A := A) (B := B) I a (b₁ * b₂) hI)
    (range_rightInterchange_inter_both I a b₁ b₂ hI)

/-- Unfolding of `rightBothInterchangePullbackIso` as the generic `pullbackIsoOfRangeEq`. -/
theorem rightBothInterchangePullbackIso_eq (a : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a b₂ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a (b₁ * b₂) hI
    rightBothInterchangePullbackIso I a b₁ b₂ hI =
      LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
        (rightInterchangeOpenImmersion (A := A) I b₁ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a b₂ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a (b₁ * b₂) hI)
        (range_rightInterchange_inter_both I a b₁ b₂ hI) :=
  rfl

/-- The `fst`-leg residual identity for the 2nd × both overlap. -/
theorem rightBoth_fst_key (a : A) (b₁ b₂ : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI
        (IsScalarTower.toAlgHom R A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a))
        (furtherLocFst (A := B) I b₁ b₂ hI) ≫
        rightInterchangeOpenImmersion (A := A) I b₁ hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I a (b₁ * b₂) hI := by
  rw [rightInterchangeOpenImmersion_eq_mapSpf (A := A) I b₁ hI,
    bothInterchangeOpenImmersion_eq_mapSpf I a (b₁ * b₂) hI,
    ← CompletedTensorProduct.mapSpf_comp, furtherLocFst_comp_toAlgHom (A := B) I b₁ b₂ hI]
  simp only [AlgHom.comp_id]

/-- The `snd`-leg residual identity for the 2nd × both overlap. -/
theorem rightBoth_snd_key (a : A) (b₁ b₂ : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI
        (AlgHom.id R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a))
        (furtherLocSnd (A := B) I b₁ b₂ hI) ≫
        bothInterchangeOpenImmersion (A := A) (B := B) I a b₂ hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I a (b₁ * b₂) hI := by
  rw [bothInterchangeOpenImmersion_eq_mapSpf I a b₂ hI,
    bothInterchangeOpenImmersion_eq_mapSpf I a (b₁ * b₂) hI,
    ← CompletedTensorProduct.mapSpf_comp, furtherLocSnd_comp_toAlgHom (A := B) I b₁ b₂ hI]
  simp only [AlgHom.id_comp]

/-- **The `pullback.fst` leg of the 2nd × both triple-overlap isomorphism.** -/
theorem rightBothInterchangePullbackIso_hom_fst (a : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a b₂ hI
    (rightBothInterchangePullbackIso I a b₁ b₂ hI).hom ≫
        pullback.fst (rightInterchangeOpenImmersion (A := A) I b₁ hI)
          (bothInterchangeOpenImmersion (A := A) (B := B) I a b₂ hI) =
      CompletedTensorProduct.mapSpf hI
        (IsScalarTower.toAlgHom R A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a))
        (furtherLocFst (A := B) I b₁ b₂ hI) := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b₁ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a b₂ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a (b₁ * b₂) hI
  rw [rightBothInterchangePullbackIso_eq I a b₁ b₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (rightBoth_fst_key I a b₁ b₂ hI)).symm

/-- **The `pullback.snd` leg of the 2nd × both triple-overlap isomorphism.** -/
theorem rightBothInterchangePullbackIso_hom_snd (a : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a b₂ hI
    (rightBothInterchangePullbackIso I a b₁ b₂ hI).hom ≫
        pullback.snd (rightInterchangeOpenImmersion (A := A) I b₁ hI)
          (bothInterchangeOpenImmersion (A := A) (B := B) I a b₂ hI) =
      CompletedTensorProduct.mapSpf hI
        (AlgHom.id R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) a))
        (furtherLocSnd (A := B) I b₁ b₂ hI) := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A) I b₁ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a b₂ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a (b₁ * b₂) hI
  rw [rightBothInterchangePullbackIso_eq I a b₁ b₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (rightBoth_snd_key I a b₁ b₂ hI)).symm

/-! ### The range identity and the pullback isomorphism (both × both) -/

/-- **The range of the both-factor chart at `(a₁·a₂, b₁·b₂)` is the intersection of the both-factor
charts at `(a₁, b₁)` and `(a₂, b₂)`.** -/
theorem range_both_inter_both (a₁ a₂ : A) (b₁ b₂ : B) (hI : I.FG) :
    Set.range
        (bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) (b₁ * b₂) hI).base =
      Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I a₁ b₁ hI).base ∩
        Set.range (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b₂ hI).base := by
  rw [range_bothInterchangeOpenImmersion_base I (a₁ * a₂) (b₁ * b₂) hI,
    range_bothInterchangeOpenImmersion_base I a₁ b₁ hI,
    range_bothInterchangeOpenImmersion_base I a₂ b₂ hI,
    map_mul (CompletedTensorProduct.inl R I A B) a₁ a₂,
    map_mul (CompletedTensorProduct.inr R I A B) b₁ b₂,
    FormalSpectrum.basicOpen_mul, FormalSpectrum.basicOpen_mul]
  simp only [TopologicalSpace.Opens.coe_inf]
  exact Set.inter_inter_inter_comm _ _ _ _

/-- **The both × both triple overlap is the both-localized chart at `(a₁·a₂, b₁·b₂)`.** -/
def bothBothInterchangePullbackIso (a₁ a₂ : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₁ b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b₂ hI
    (FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (a₁ * a₂))
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) (b₁ * b₂))) ≅
      pullback (bothInterchangeOpenImmersion (A := A) (B := B) I a₁ b₁ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b₂ hI)) :=
  letI := isOpenImmersion_bothInterchangeOpenImmersion I a₁ b₁ hI
  letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b₂ hI
  letI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) (b₁ * b₂) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (bothInterchangeOpenImmersion (A := A) (B := B) I a₁ b₁ hI)
    (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b₂ hI)
    (bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) (b₁ * b₂) hI)
    (range_both_inter_both I a₁ a₂ b₁ b₂ hI)

/-- Unfolding of `bothBothInterchangePullbackIso` as the generic `pullbackIsoOfRangeEq`. -/
theorem bothBothInterchangePullbackIso_eq (a₁ a₂ : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₁ b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b₂ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) (b₁ * b₂) hI
    bothBothInterchangePullbackIso I a₁ a₂ b₁ b₂ hI =
      LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
        (bothInterchangeOpenImmersion (A := A) (B := B) I a₁ b₁ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b₂ hI)
        (bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) (b₁ * b₂) hI)
        (range_both_inter_both I a₁ a₂ b₁ b₂ hI) :=
  rfl

/-- The `fst`-leg residual identity for the both × both overlap. -/
theorem bothBoth_fst_key (a₁ a₂ : A) (b₁ b₂ : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (furtherLocFst (A := A) I a₁ a₂ hI)
        (furtherLocFst (A := B) I b₁ b₂ hI) ≫
        bothInterchangeOpenImmersion (A := A) (B := B) I a₁ b₁ hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) (b₁ * b₂) hI := by
  rw [bothInterchangeOpenImmersion_eq_mapSpf I a₁ b₁ hI,
    bothInterchangeOpenImmersion_eq_mapSpf I (a₁ * a₂) (b₁ * b₂) hI,
    ← CompletedTensorProduct.mapSpf_comp, furtherLocFst_comp_toAlgHom (A := A) I a₁ a₂ hI,
    furtherLocFst_comp_toAlgHom (A := B) I b₁ b₂ hI]

/-- The `snd`-leg residual identity for the both × both overlap. -/
theorem bothBoth_snd_key (a₁ a₂ : A) (b₁ b₂ : B) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (furtherLocSnd (A := A) I a₁ a₂ hI)
        (furtherLocSnd (A := B) I b₁ b₂ hI) ≫
        bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b₂ hI =
      bothInterchangeOpenImmersion (A := A) (B := B) I (a₁ * a₂) (b₁ * b₂) hI := by
  rw [bothInterchangeOpenImmersion_eq_mapSpf I a₂ b₂ hI,
    bothInterchangeOpenImmersion_eq_mapSpf I (a₁ * a₂) (b₁ * b₂) hI,
    ← CompletedTensorProduct.mapSpf_comp, furtherLocSnd_comp_toAlgHom (A := A) I a₁ a₂ hI,
    furtherLocSnd_comp_toAlgHom (A := B) I b₁ b₂ hI]

/-- **The `pullback.fst` leg of the both × both triple-overlap isomorphism.** -/
theorem bothBothInterchangePullbackIso_hom_fst (a₁ a₂ : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₁ b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b₂ hI
    (bothBothInterchangePullbackIso I a₁ a₂ b₁ b₂ hI).hom ≫
        pullback.fst (bothInterchangeOpenImmersion (A := A) (B := B) I a₁ b₁ hI)
          (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b₂ hI) =
      CompletedTensorProduct.mapSpf hI (furtherLocFst (A := A) I a₁ a₂ hI)
        (furtherLocFst (A := B) I b₁ b₂ hI) := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a₁ b₁ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b₂ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) (b₁ * b₂) hI
  rw [bothBothInterchangePullbackIso_eq I a₁ a₂ b₁ b₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (bothBoth_fst_key I a₁ a₂ b₁ b₂ hI)).symm

/-- **The `pullback.snd` leg of the both × both triple-overlap isomorphism.** -/
theorem bothBothInterchangePullbackIso_hom_snd (a₁ a₂ : A) (b₁ b₂ : B) (hI : I.FG) :
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₁ b₁ hI
    letI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b₂ hI
    (bothBothInterchangePullbackIso I a₁ a₂ b₁ b₂ hI).hom ≫
        pullback.snd (bothInterchangeOpenImmersion (A := A) (B := B) I a₁ b₁ hI)
          (bothInterchangeOpenImmersion (A := A) (B := B) I a₂ b₂ hI) =
      CompletedTensorProduct.mapSpf hI (furtherLocSnd (A := A) I a₁ a₂ hI)
        (furtherLocSnd (A := B) I b₁ b₂ hI) := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a₁ b₁ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I a₂ b₂ hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (a₁ * a₂) (b₁ * b₂) hI
  rw [bothBothInterchangePullbackIso_eq I a₁ a₂ b₁ b₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (bothBoth_snd_key I a₁ a₂ b₁ b₂ hI)).symm

end CompletedTensorAwayInterchange

end
