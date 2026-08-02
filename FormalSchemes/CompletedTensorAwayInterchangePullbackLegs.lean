import FormalSchemes.CompletedTensorAwayInterchangePullback
import FormalSchemes.PullbackIsoRangeLegs
import FormalSchemes.CompletedTensorMapSpf

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The two legs of the interchange triple-overlap isomorphism

Fix an adic base `(R, I)` with `I` finitely generated, an `R`-algebra `A`, an affine base change
`B`, and write `C = A ⊗̂_R B = CompletedTensorProduct R I A B`. For an away element `g : A` write
`A{1/g} = FormalSpectrum.awayCompletion (I·A) g` and recall the interchange open immersion
`CompletedTensorAwayInterchange.interchangeOpenImmersion I g hI : Spf(A{1/g} ⊗̂_R B) ↪ Spf C`
realising `Spf(A{1/g} ⊗̂_R B)` as the basic open `D(inl g) ⊆ Spf C`
(`FormalSchemes.CompletedTensorAwayInterchangeSpf`).

For two away elements `g₁, g₂ : A` the pullback (triple overlap) of the interchange charts at `g₁`
and `g₂` is again the interchange chart at the product `g₁ · g₂`
(`CompletedTensorAwayInterchange.interchangePullbackIso`,
`FormalSchemes.CompletedTensorAwayInterchangePullback`). This file identifies the two legs of that
isomorphism down to the charts with the geometric maps `mapSpf` of the *further localizations*

* `φ₁ = furtherLocFst I g₁ g₂ hI : A{1/g₁} →ₐ[R] A{1/(g₁·g₂)}` (invert `g₂` after `g₁`), and
* `φ₂ = furtherLocSnd I g₁ g₂ hI : A{1/g₂} →ₐ[R] A{1/(g₁·g₂)}` (invert `g₁` after `g₂`),

built by completing the localization-transitivity ring maps `IsLocalization.Away.awayToAwayRight`
and `IsLocalization.Away.awayToAwayLeft`.

## Main results

* `CompletedTensorAwayInterchange.interchangePullbackIso_hom_fst`: the `pullback.fst` leg of
  `interchangePullbackIso` equals `mapSpf hI φ₁ (AlgHom.id R B)`.
* `CompletedTensorAwayInterchange.interchangePullbackIso_hom_snd`: the `pullback.snd` leg equals
  `mapSpf hI φ₂ (AlgHom.id R B)`.

The route is: the isolated-leg form `pullbackIsoOfRangeEq_hom_fst`
(`FormalSchemes.PullbackIsoRangeLegs`) rewrites the leg as an open-immersion `lift`; then the
open-immersion `lift`-uniqueness reduces the identification to a morphism identity down to `Spf C`,
which is `mapSpf`/`interchangeOpenImmersion` naturality and finally the ring-level identity
`(map hI φ₁ id) ∘ gCHom(g₁) = gCHom(g₁·g₂)` proved by the completed-tensor universal property.

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

/-! ### The further-localization algebra maps `A{1/s} →ₐ[R] A{1/t}` -/

/-- The completion of a localization ring map `ρ : A_s → A_t` (compatible with the structure maps
from `A`, i.e. `ρ ∘ (A → A_s) = (A → A_t)`) to a map of completed localizations
`A{1/s} →+* A{1/t}`. -/
def furtherLocRingHom (s t : A) (hI : I.FG)
    (ρ : Localization.Away s →+* Localization.Away t)
    (hρ : ρ.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t)) :
    FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s →+*
      FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t :=
  AdicCompletion.mapCompletion ρ
    (le_of_eq (by
      rw [Ideal.map_map, hρ]))
    ((hI.map (algebraMap R A)).map (algebraMap A (Localization.Away t)))

/-- The completed localization map sends `A → A{1/s} → A{1/t}` to `A → A{1/t}`. -/
theorem furtherLocRingHom_algebraMap_A (s t : A) (hI : I.FG)
    (ρ : Localization.Away s →+* Localization.Away t)
    (hρ : ρ.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t))
    (a : A) :
    furtherLocRingHom I s t hI ρ hρ
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s) a) =
      algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t) a := by
  have hρa : ρ (algebraMap A (Localization.Away s) a) = algebraMap A (Localization.Away t) a :=
    DFunLike.congr_fun hρ a
  rw [AdicCompletion.algebraMap_apply, furtherLocRingHom, AdicCompletion.mapCompletion_of, hρa,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← AdicCompletion.algebraMap_apply]

/-- The completed localization map is an `R`-algebra map: `A → A{1/s} → A{1/t}` restricts on the
image of `R` to `R → A{1/t}`. -/
theorem furtherLocRingHom_algebraMap_R (s t : A) (hI : I.FG)
    (ρ : Localization.Away s →+* Localization.Away t)
    (hρ : ρ.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t))
    (r : R) :
    furtherLocRingHom I s t hI ρ hρ
        (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s) r) =
      algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t) r := by
  rw [IsScalarTower.algebraMap_apply R A
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s),
    furtherLocRingHom_algebraMap_A,
    ← IsScalarTower.algebraMap_apply R A
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t)]

/-- The completion of a compatible localization ring map, packaged as an `R`-algebra map
`A{1/s} →ₐ[R] A{1/t}`. -/
def furtherLocAlgHom (s t : A) (hI : I.FG)
    (ρ : Localization.Away s →+* Localization.Away t)
    (hρ : ρ.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t)) :
    FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s →ₐ[R]
      FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t :=
  { furtherLocRingHom I s t hI ρ hρ with
    commutes' := furtherLocRingHom_algebraMap_R I s t hI ρ hρ }

theorem furtherLocAlgHom_algebraMap (s t : A) (hI : I.FG)
    (ρ : Localization.Away s →+* Localization.Away t)
    (hρ : ρ.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t))
    (a : A) :
    furtherLocAlgHom I s t hI ρ hρ
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s) a) =
      algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t) a :=
  furtherLocRingHom_algebraMap_A I s t hI ρ hρ a

/-- **The first further localization** `A{1/g₁} →ₐ[R] A{1/(g₁·g₂)}` (invert `g₂` after `g₁`),
completing `IsLocalization.Away.awayToAwayRight`. -/
def furtherLocFst (g₁ g₂ : A) (hI : I.FG) :
    FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₁ →ₐ[R]
      FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂) :=
  furtherLocAlgHom I g₁ (g₁ * g₂) hI (IsLocalization.Away.awayToAwayRight g₁ g₂)
    (RingHom.ext fun a => by
      rw [RingHom.comp_apply]
      exact IsLocalization.Away.awayToAwayRight_eq g₁ g₂ a)

theorem furtherLocFst_algebraMap (g₁ g₂ : A) (hI : I.FG) (a : A) :
    furtherLocFst I g₁ g₂ hI
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₁) a) =
      algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂)) a :=
  furtherLocAlgHom_algebraMap I g₁ (g₁ * g₂) hI _ _ a

/-- **The second further localization** `A{1/g₂} →ₐ[R] A{1/(g₁·g₂)}` (invert `g₁` after `g₂`),
completing `IsLocalization.Away.awayToAwayLeft`. -/
def furtherLocSnd (g₁ g₂ : A) (hI : I.FG) :
    FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₂ →ₐ[R]
      FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂) :=
  furtherLocAlgHom I g₂ (g₁ * g₂) hI (IsLocalization.Away.awayToAwayLeft g₂ g₁)
    (RingHom.ext fun a => by
      rw [RingHom.comp_apply]
      exact IsLocalization.Away.awayToAwayLeft_eq g₂ g₁ a)

theorem furtherLocSnd_algebraMap (g₁ g₂ : A) (hI : I.FG) (a : A) :
    furtherLocSnd I g₁ g₂ hI
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₂) a) =
      algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂)) a :=
  furtherLocAlgHom_algebraMap I g₂ (g₁ * g₂) hI _ _ a

/-! ### The ring-level naturality of the completed-tensor lift `gCHom` -/

/-- Continuity of the completed-tensor lift `gCHom I f hI : C →+* A{1/f} ⊗̂_R B`. -/
theorem gCHom_mem_pow (f : A) (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I A B}
    (hx : x ∈ (CompletedTensorProduct.idealOfDefinition R I A B) ^ m) :
    gCHom I f hI x ∈
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) ^ m := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  exact CompletedTensorProduct.lift_mem_pow _ _ _ _ hI m hx

/-- The completed-tensor lift `gCHom I f hI` carries the ideal of definition of `C` into that of
`A{1/f} ⊗̂_R B` (its continuity witness at level `1`). -/
theorem gCHom_le_comap (f : A) (hI : I.FG) :
    CompletedTensorProduct.idealOfDefinition R I A B ≤
      (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).comap (gCHom I f hI) := by
  intro x hx
  rw [Ideal.mem_comap]
  have h2 := gCHom_mem_pow I f hI 1 (by rwa [pow_one] : x ∈ _ ^ 1)
  rwa [pow_one] at h2

/-- **Key ring identity.** For any further-localization algebra map `φ : A{1/s} →ₐ[R] A{1/t}`
compatible with the structure maps from `A`, the base-change map `map hI φ id_B` intertwines the
two completed-tensor lifts: `(map hI φ id) ∘ gCHom(s) = gCHom(t)`. This is the ring shadow of the
leg identification. -/
theorem gCHom_map_comp (s t : A) (hI : I.FG)
    (φ : FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s →ₐ[R]
      FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t)
    (hφ : ∀ a : A, φ (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s) a) =
      algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t) a) :
    (CompletedTensorProduct.map hI φ (AlgHom.id R B)).comp (gCHom I s hI) = gCHom I t hI := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t) B)
      (CompletedTensorProduct R I (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t) B) :=
    (CompletedTensorProduct.isAdicRing R I _ B hI).toIsAdicComplete
  refine CompletedTensorProduct.hom_ext
    (CompletedTensorProduct.idealOfDefinition R I
      (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) t) B) hI
    (fun m x hx => ?_) (fun m x hx => ?_) (fun a => ?_) (fun b => ?_)
  · rw [RingHom.comp_apply]
    exact CompletedTensorProduct.map_mem_pow hI φ (AlgHom.id R B) m (gCHom_mem_pow I s hI m hx)
  · exact gCHom_mem_pow I t hI m hx
  · rw [RingHom.comp_apply, gCHom_inl I s hI a, gA_apply I s a, CompletedTensorProduct.map_inl,
      hφ a, gCHom_inl I t hI a, gA_apply I t a]
  · rw [RingHom.comp_apply, gCHom_inr I s hI b, CompletedTensorProduct.map_inr, AlgHom.id_apply,
      gCHom_inr I t hI b]

/-! ### The interchange open immersion as `Spf` of `gCHom` -/

/-- The interchange isomorphism's `symm` composed with the structural map `C → C{1/f̄}` is exactly
the completed-tensor lift `gCHom`. The underlying ring map of `(equiv I f hI).symm` is
definitionally `backwardHom I f hI`. -/
theorem interchange_ringHom (f : A) (hI : I.FG) :
    (equiv I f hI).symm.toRingHom.comp
        (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f)) =
      gCHom I f hI := by
  refine RingHom.ext fun c => ?_
  rw [RingHom.comp_apply]
  exact backwardHom_awayCompletionHom I f hI c

/-- **The interchange open immersion is `Spf` of `gCHom`.** It equals the morphism of formal
spectra induced by the completed-tensor lift `gCHom I f hI : C →+* A{1/f} ⊗̂_R B`. -/
theorem interchangeOpenImmersion_eq_map (f : A) (hI : I.FG) :
    interchangeOpenImmersion (B := B) I f hI =
      FormalSpectrum.locallyRingedSpaceMap (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
        (gCHom I f hI) (gCHom_le_comap I f hI) := by
  have h1 : (equivSpfIso I f hI).hom =
      FormalSpectrum.locallyRingedSpaceMap
        (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f))
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
        (equiv I f hI).symm.toRingHom
        (FormalSpectrum.isAdicHom_ringEquiv_symm (equiv I f hI)
          (isAdicHom_equiv I f hI)).le_comap :=
    rfl
  rw [interchangeOpenImmersion, h1, FormalSpectrum.basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (CompletedTensorProduct.idealOfDefinition R I A B)
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (equiv I f hI).symm.toRingHom
      (FormalSpectrum.le_comap_awayCompletionHom
        (CompletedTensorProduct.idealOfDefinition R I A B) (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.isAdicHom_ringEquiv_symm (equiv I f hI) (isAdicHom_equiv I f hI)).le_comap
      (by
        rw [interchange_ringHom I f hI]
        exact gCHom_le_comap I f hI)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ (interchange_ringHom I f hI)

/-! ### The residual leg identities down to `Spf C` -/

/-- The `fst`-leg residual identity: `mapSpf hI φ₁ id` followed by the interchange chart at `g₁`
equals the interchange chart at `g₁ · g₂`. -/
theorem interchange_fst_key (g₁ g₂ : A) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (furtherLocFst I g₁ g₂ hI) (AlgHom.id R B) ≫
        interchangeOpenImmersion (B := B) I g₁ hI =
      interchangeOpenImmersion (B := B) I (g₁ * g₂) hI := by
  rw [interchangeOpenImmersion_eq_map I g₁ hI, interchangeOpenImmersion_eq_map I (g₁ * g₂) hI,
    CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₁) B)
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂)) B)
      (gCHom I g₁ hI) (CompletedTensorProduct.map hI (furtherLocFst I g₁ g₂ hI) (AlgHom.id R B))
      (gCHom_le_comap I g₁ hI)
      (CompletedTensorProduct.map_isAdicHom hI (furtherLocFst I g₁ g₂ hI) (AlgHom.id R B)).le_comap
      (by
        rw [gCHom_map_comp I g₁ (g₁ * g₂) hI (furtherLocFst I g₁ g₂ hI)
          (furtherLocFst_algebraMap I g₁ g₂ hI)]
        exact gCHom_le_comap I (g₁ * g₂) hI)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (gCHom_map_comp I g₁ (g₁ * g₂) hI (furtherLocFst I g₁ g₂ hI)
      (furtherLocFst_algebraMap I g₁ g₂ hI))

/-- The `snd`-leg residual identity: `mapSpf hI φ₂ id` followed by the interchange chart at `g₂`
equals the interchange chart at `g₁ · g₂`. -/
theorem interchange_snd_key (g₁ g₂ : A) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (furtherLocSnd I g₁ g₂ hI) (AlgHom.id R B) ≫
        interchangeOpenImmersion (B := B) I g₂ hI =
      interchangeOpenImmersion (B := B) I (g₁ * g₂) hI := by
  rw [interchangeOpenImmersion_eq_map I g₂ hI, interchangeOpenImmersion_eq_map I (g₁ * g₂) hI,
    CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) g₂) B)
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂)) B)
      (gCHom I g₂ hI) (CompletedTensorProduct.map hI (furtherLocSnd I g₁ g₂ hI) (AlgHom.id R B))
      (gCHom_le_comap I g₂ hI)
      (CompletedTensorProduct.map_isAdicHom hI (furtherLocSnd I g₁ g₂ hI) (AlgHom.id R B)).le_comap
      (by
        rw [gCHom_map_comp I g₂ (g₁ * g₂) hI (furtherLocSnd I g₁ g₂ hI)
          (furtherLocSnd_algebraMap I g₁ g₂ hI)]
        exact gCHom_le_comap I (g₁ * g₂) hI)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (gCHom_map_comp I g₂ (g₁ * g₂) hI (furtherLocSnd I g₁ g₂ hI)
      (furtherLocSnd_algebraMap I g₁ g₂ hI))

/-! ### The two legs of `interchangePullbackIso` -/

/-- Unfolding of `interchangePullbackIso` as the generic `pullbackIsoOfRangeEq`. -/
theorem interchangePullbackIso_eq (g₁ g₂ : A) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₁ hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₂ hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g₁ * g₂) hI
    interchangePullbackIso I g₁ g₂ hI =
      LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
        (interchangeOpenImmersion (B := B) I g₁ hI) (interchangeOpenImmersion (B := B) I g₂ hI)
        (interchangeOpenImmersion (B := B) I (g₁ * g₂) hI)
        (range_interchangeOpenImmersion_mul I g₁ g₂ hI) :=
  rfl

/-- **The `pullback.fst` leg of the interchange triple-overlap isomorphism.** It equals the
geometric further-localization map `mapSpf hI φ₁ (AlgHom.id R B)` with
`φ₁ = furtherLocFst I g₁ g₂ hI : A{1/g₁} →ₐ[R] A{1/(g₁·g₂)}`. -/
theorem interchangePullbackIso_hom_fst (g₁ g₂ : A) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₁ hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₂ hI
    (interchangePullbackIso I g₁ g₂ hI).hom ≫
        pullback.fst (interchangeOpenImmersion (B := B) I g₁ hI)
          (interchangeOpenImmersion (B := B) I g₂ hI) =
      CompletedTensorProduct.mapSpf hI (furtherLocFst I g₁ g₂ hI) (AlgHom.id R B) := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₁ hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₂ hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g₁ * g₂) hI
  rw [interchangePullbackIso_eq I g₁ g₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (interchange_fst_key I g₁ g₂ hI)).symm

/-- **The `pullback.snd` leg of the interchange triple-overlap isomorphism.** It equals the
geometric further-localization map `mapSpf hI φ₂ (AlgHom.id R B)` with
`φ₂ = furtherLocSnd I g₁ g₂ hI : A{1/g₂} →ₐ[R] A{1/(g₁·g₂)}`. -/
theorem interchangePullbackIso_hom_snd (g₁ g₂ : A) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₁ hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₂ hI
    (interchangePullbackIso I g₁ g₂ hI).hom ≫
        pullback.snd (interchangeOpenImmersion (B := B) I g₁ hI)
          (interchangeOpenImmersion (B := B) I g₂ hI) =
      CompletedTensorProduct.mapSpf hI (furtherLocSnd I g₁ g₂ hI) (AlgHom.id R B) := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₁ hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₂ hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g₁ * g₂) hI
  rw [interchangePullbackIso_eq I g₁ g₂ hI,
    LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd]
  exact (LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _
    (interchange_snd_key I g₁ g₂ hI)).symm

end CompletedTensorAwayInterchange

end
