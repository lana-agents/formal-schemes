import FormalSchemes.RestrictedPowerSeries
import FormalSchemes.AdicExtend
import FormalSchemes.SpfMap
import FormalSchemes.SpfFunctorial

set_option linter.style.header false

/-!
# The formal completion of an affine scheme along a closed subscheme

For a commutative ring `R` and a finitely generated ideal `I`, the **formal completion of
`Spec R` along the closed subscheme `V(I)`** is the formal spectrum of the `I`-adic completion
`R^ = AdicCompletion I R` (EGA I, 10.8; Stacks, Tag 0AIX). This file constructs it and
identifies its underlying space.

The key algebraic input is that completion does not change the infinitesimal thickenings:
`R^ ⧸ (I·R^) ^ n ≅ R ⧸ I ^ n` (`AdicCompletion.quotientEquivPow`), because the kernel of
`evalₐ I n : R^ → R ⧸ I ^ n` is exactly `(I·R^) ^ n` when `I` is finitely generated. Level `1`
of this identification says that the underlying space of the completion is `Spec (R ⧸ I)`,
i.e. the closed subset `V(I) ⊆ Spec R` — the formal completion is supported on the closed
subscheme one completes along, as it must be.

## Main definitions and results

* `AdicCompletion.idealOfDefinition I`: the ideal of definition `I·R^` of the completion.
* `AdicCompletion.ker_evalₐ`: `ker (evalₐ I n) = (I·R^) ^ n` for finitely generated `I`.
* `AdicCompletion.quotientEquivPow`: `R^ ⧸ (I·R^) ^ n ≃+* R ⧸ I ^ n`.
* `AdicCompletion.mapCompletion f hf hJ`: the ring map `R^ →+* S^` induced on completions by
  `f : R →+* S` with `I.map f ≤ J`, with functor laws `mapCompletion_id`, `mapCompletion_comp`.
* `formalCompletion R I hI : FormalScheme`: the formal completion of `Spec R` along `V(I)`.
* `formalCompletion.map`: functoriality in `(X, Z)` — the induced morphism of formal schemes
  `formalCompletion S J ⟶ formalCompletion R I`.
* `formalCompletionHomeo`: its underlying space is homeomorphic to `Spec (R ⧸ I)`.
* `range_toPrimeSpectrum_formalCompletion`: which sits inside `Spec R` as the closed subset
  `V(I)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open Ideal AlgebraicGeometry

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The ideal of definition `I·R^` of the `I`-adic completion of `R`. -/
abbrev idealOfDefinition : Ideal (AdicCompletion I R) :=
  I.map (algebraMap R (AdicCompletion I R))

/-- The powers of the ideal of definition of the completion are exactly the kernels of the
evaluation maps to the thickenings, for `I` finitely generated. -/
theorem ker_evalₐ (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n).toRingHom = (idealOfDefinition I) ^ n := by
  have heq : ((I ^ n • ⊤ : Ideal R)) = I ^ n := by ext y; simp
  have hsmul : ((idealOfDefinition I) ^ n • ⊤ : Submodule (AdicCompletion I R)
      (AdicCompletion I R)) = ((idealOfDefinition I) ^ n : Ideal (AdicCompletion I R)) := by
    ext y
    simp
  -- `evalₐ` is `eval` followed by an isomorphism of the two quotient presentations
  have hcompute : ∀ x : AdicCompletion I R,
      evalₐ I n x = Ideal.quotientEquivAlgOfEq R heq (eval I R n x) := fun _ => rfl
  ext x
  rw [RingHom.mem_ker]
  change evalₐ I n x = 0 ↔ _
  rw [hcompute x, map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R heq).injective]
  rw [show ((0 : R ⧸ (I ^ n • ⊤ : Ideal R)) = 0) from rfl]
  constructor
  · intro hx
    have hmem : x ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
      exact hx
    rw [← Ideal.mem_map_pow_iff_mem_smul_top I n x, hsmul] at hmem
    exact hmem
  · intro hx
    rw [← hsmul, Ideal.mem_map_pow_iff_mem_smul_top I n x,
      AdicCompletion.pow_smul_top_eq_ker_eval hI] at hx
    exact hx

/-- **Completion does not change the infinitesimal thickenings**: the `n`-th thickening of the
completion `R^` is the `n`-th thickening `R ⧸ I ^ n` of `R` itself. -/
def quotientEquivPow (hI : I.FG) (n : ℕ) :
    AdicCompletion I R ⧸ (idealOfDefinition I) ^ n ≃+* R ⧸ I ^ n :=
  (Ideal.quotEquivOfEq (ker_evalₐ I hI n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (evalₐ I n).toRingHom) (surjective_evalₐ I n))

theorem quotientEquivPow_mk (hI : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    quotientEquivPow I hI n (Ideal.Quotient.mk _ x) = evalₐ I n x :=
  rfl

/-- Level `1`: the residue ring of the completion is the residue ring of `R`. -/
def quotientEquiv (hI : I.FG) :
    AdicCompletion I R ⧸ (idealOfDefinition I) ≃+* R ⧸ I :=
  (Ideal.quotEquivOfEq (pow_one (idealOfDefinition I)).symm).trans
    ((quotientEquivPow I hI 1).trans (Ideal.quotEquivOfEq (pow_one I)))

/-!
### Functoriality of the completion

Completion is a functor on adic ring maps: a ring homomorphism `f : R →+* S` carrying `I` into
`J` (`I.map f ≤ J`, i.e. a map of pairs `(Spec S, V(J)) → (Spec R, V(I))`) induces a continuous
ring homomorphism `R^ →+* S^` between the completions, functorially. This is built from the
continuous-extension engine `AdicCompletion.extendRingHom` (`FormalSchemes/AdicExtend.lean`);
uniqueness of continuous extensions (`hom_ext_of_continuous`) gives the functor laws.
-/

section Functoriality

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {I : Ideal R} {J : Ideal S} {K : Ideal T}

/-- Membership in the powers of the ideal of definition, expressed through the module
filtration `I ^ m • ⊤` used by the completion API (`extendRingHom_continuous`,
`hom_ext_of_continuous`). -/
theorem mem_idealOfDefinition_pow_iff (m : ℕ) (x : AdicCompletion I R) :
    x ∈ (idealOfDefinition I) ^ m ↔
      x ∈ (I ^ m • ⊤ : Submodule R (AdicCompletion I R)) := by
  rw [← Ideal.mem_map_pow_iff_mem_smul_top I m x, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem, Algebra.algebraMap_self, Ideal.map_id]

/-- **Functoriality of the completion**: a ring homomorphism `f : R →+* S` carrying `I` into `J`
(`I.map f ≤ J`) induces a ring homomorphism `R^ →+* S^` on the `I`- and `J`-adic completions.
The target ideal `J` is finitely generated so that `S^` is complete. -/
def mapCompletion (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) :
    AdicCompletion I R →+* AdicCompletion J S :=
  haveI : IsAdicComplete (idealOfDefinition J) (AdicCompletion J S) :=
    (isAdicRing_map J hJ).toIsAdicComplete
  extendRingHom I (idealOfDefinition J) ((algebraMap S (AdicCompletion J S)).comp f)
    (fun m => by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ m
      rw [← Ideal.map_map]
      exact Ideal.map_mono hf)

theorem mapCompletion_of (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) (r : R) :
    mapCompletion f hf hJ (AdicCompletion.of I R r) =
      algebraMap S (AdicCompletion J S) (f r) := by
  haveI : IsAdicComplete (idealOfDefinition J) (AdicCompletion J S) :=
    (isAdicRing_map J hJ).toIsAdicComplete
  exact extendRingHom_of I (idealOfDefinition J) _ _ r

@[simp]
theorem mapCompletion_algebraMap (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) (r : R) :
    mapCompletion f hf hJ (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion J S) (f r) := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    mapCompletion_of]

theorem mapCompletion_comp_algebraMap (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) :
    (mapCompletion f hf hJ).comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f :=
  RingHom.ext fun r => by
    rw [RingHom.comp_apply, RingHom.comp_apply, mapCompletion_algebraMap]

/-- The induced map carries the ideal of definition of `R^` into that of `S^`: `mapCompletion`
is an adic ring homomorphism. -/
theorem idealOfDefinition_map_le (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) :
    (idealOfDefinition I).map (mapCompletion f hf hJ) ≤ idealOfDefinition J := by
  change (I.map (algebraMap R (AdicCompletion I R))).map (mapCompletion f hf hJ) ≤ _
  rw [Ideal.map_map, mapCompletion_comp_algebraMap, ← Ideal.map_map]
  exact Ideal.map_mono hf

/-- Continuity of `mapCompletion`, in the filtration form consumed by
`hom_ext_of_continuous`. -/
theorem mapCompletion_mem_pow (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) (hI : I.FG)
    (m : ℕ) {x : AdicCompletion I R}
    (hx : x ∈ (I ^ m • ⊤ : Submodule R (AdicCompletion I R))) :
    mapCompletion f hf hJ x ∈ (idealOfDefinition J) ^ m := by
  haveI : IsAdicComplete (idealOfDefinition J) (AdicCompletion J S) :=
    (isAdicRing_map J hJ).toIsAdicComplete
  exact extendRingHom_continuous I (idealOfDefinition J) _ _ hI m x hx

/-- Completion sends the identity to the identity (functoriality). -/
theorem mapCompletion_id (hI : I.FG) :
    mapCompletion (RingHom.id R) (le_of_eq (Ideal.map_id I)) hI =
      RingHom.id (AdicCompletion I R) := by
  haveI : IsAdicComplete (idealOfDefinition I) (AdicCompletion I R) :=
    (isAdicRing_map I hI).toIsAdicComplete
  refine hom_ext_of_continuous I (idealOfDefinition I) hI
    (fun m x hx => mapCompletion_mem_pow _ _ _ hI m hx)
    (fun m x hx => (mem_idealOfDefinition_pow_iff m x).mpr hx) fun r => ?_
  simp only [mapCompletion_of, RingHom.id_apply, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self]

/-- Completion respects composition (functoriality, contravariant on formal spectra). -/
theorem mapCompletion_comp (f : R →+* S) (g : S →+* T) (hf : I.map f ≤ J) (hg : J.map g ≤ K)
    (hJ : J.FG) (hK : K.FG) (hI : I.FG) :
    (mapCompletion g hg hK).comp (mapCompletion f hf hJ) =
      mapCompletion (g.comp f)
        (by rw [← Ideal.map_map]; exact le_trans (Ideal.map_mono hf) hg) hK := by
  haveI : IsAdicComplete (idealOfDefinition K) (AdicCompletion K T) :=
    (isAdicRing_map K hK).toIsAdicComplete
  haveI : IsAdicComplete (idealOfDefinition J) (AdicCompletion J S) :=
    (isAdicRing_map J hJ).toIsAdicComplete
  refine hom_ext_of_continuous I (idealOfDefinition K) hI (fun m x hx => ?_)
    (fun m x hx => mapCompletion_mem_pow _ _ _ hI m hx) fun r => ?_
  · have h1 := mapCompletion_mem_pow f hf hJ hI m hx
    rw [mem_idealOfDefinition_pow_iff] at h1
    exact mapCompletion_mem_pow g hg hK hJ m h1
  · simp only [RingHom.comp_apply, mapCompletion_of, mapCompletion_algebraMap]

end Functoriality

end AdicCompletion

/-- The **formal completion of `Spec R` along `V(I)`** (EGA I, 10.8): the formal spectrum of the
`I`-adic completion of `R`, for a finitely generated ideal `I`. -/
def formalCompletion (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) : FormalScheme :=
  haveI := AdicCompletion.isAdicRing_map I hI
  FormalScheme.Spf (AdicCompletion.idealOfDefinition I)

namespace formalCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)

/-- The underlying space of the formal completion of `Spec R` along `V(I)` is `Spec (R ⧸ I)`:
the completion is supported on the closed subscheme one completes along. -/
def homeo :
    FormalSpectrum (AdicCompletion.idealOfDefinition I) ≃ₜ PrimeSpectrum (R ⧸ I) :=
  PrimeSpectrum.homeomorphOfRingEquiv (AdicCompletion.quotientEquiv I hI)

/-- The formal completion sits inside `Spec R` as the closed subset `V(I)`: composing the
identification of its space with `Spec (R ⧸ I)` and the closed embedding of the latter, the
range is the zero locus of `I`. -/
theorem range_comap_mk :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I) ∘ (homeo I hI)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [Set.range_comp, (homeo I hI).surjective.range_eq, Set.image_univ]
  have h := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rwa [Ideal.mk_ker] at h

/-- **Functoriality of the formal completion in `(X, Z)`** (EGA I, 10.8): a ring homomorphism
`f : R →+* S` carrying `I` into `J` (`I.map f ≤ J`) — a morphism of pairs
`(Spec S, V(J)) → (Spec R, V(I))` — induces a morphism of formal schemes
`formalCompletion S J ⟶ formalCompletion R I` on the completions (contravariantly), namely `Spf`
of the induced map `R^ →+* S^` on completions.

The functor laws hold on the underlying completion ring maps (`AdicCompletion.mapCompletion_id`,
`AdicCompletion.mapCompletion_comp`). They are packaged as equalities of formal-scheme morphisms
below — `map_id` (via `FormalSpectrum.locallyRingedSpaceMap_id`) and `map_comp` (via
`FormalSpectrum.locallyRingedSpaceMap_comp`) — transporting the structure-sheaf component along the
propositional equality of base maps. -/
def map {S : Type u} [CommRing S] {I : Ideal R} {J : Ideal S} (hI : I.FG) (hJ : J.FG)
    (f : R →+* S) (hf : I.map f ≤ J) :
    formalCompletion S J hJ ⟶ formalCompletion R I hI :=
  haveI := AdicCompletion.isAdicRing_map I hI
  haveI := AdicCompletion.isAdicRing_map J hJ
  FormalScheme.Hom.mk
    (FormalSpectrum.locallyRingedSpaceMap (AdicCompletion.idealOfDefinition I)
      (AdicCompletion.idealOfDefinition J) (AdicCompletion.mapCompletion f hf hJ)
      (Ideal.map_le_iff_le_comap.mp (AdicCompletion.idealOfDefinition_map_le f hf hJ)))

open CategoryTheory in
/-- **The formal completion respects the identity** (functoriality, EGA I 10.8):
`map id = id`. -/
theorem map_id :
    formalCompletion.map hI hI (RingHom.id R) (le_of_eq (Ideal.map_id I)) =
      𝟙 (formalCompletion R I hI) := by
  haveI := AdicCompletion.isAdicRing_map I hI
  apply FormalScheme.Hom.ext'
  change FormalSpectrum.locallyRingedSpaceMap (AdicCompletion.idealOfDefinition I)
      (AdicCompletion.idealOfDefinition I)
      (AdicCompletion.mapCompletion (RingHom.id R) (le_of_eq (Ideal.map_id I)) hI) _ =
    𝟙 (FormalSpectrum.locallyRingedSpaceObj (AdicCompletion.idealOfDefinition I))
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (AdicCompletion.idealOfDefinition I)
    (AdicCompletion.idealOfDefinition I) (AdicCompletion.mapCompletion (RingHom.id R)
      (le_of_eq (Ideal.map_id I)) hI) (RingHom.id (AdicCompletion I R)) _ _
    (AdicCompletion.mapCompletion_id hI)]
  exact FormalSpectrum.locallyRingedSpaceMap_id (AdicCompletion.idealOfDefinition I)

open CategoryTheory in
/-- **The formal completion respects composition** (functoriality, EGA I 10.8):
`map (g ∘ f) = map g ≫ map f` (contravariantly). -/
theorem map_comp {S T : Type u} [CommRing S] [CommRing T] {J : Ideal S} {K : Ideal T}
    (hJ : J.FG) (hK : K.FG) (f : R →+* S) (g : S →+* T) (hf : I.map f ≤ J) (hg : J.map g ≤ K) :
    formalCompletion.map hI hK (g.comp f)
        (by rw [← Ideal.map_map]; exact le_trans (Ideal.map_mono hf) hg) =
      formalCompletion.map hJ hK g hg ≫ formalCompletion.map hI hJ f hf := by
  haveI := AdicCompletion.isAdicRing_map I hI
  haveI := AdicCompletion.isAdicRing_map J hJ
  haveI := AdicCompletion.isAdicRing_map K hK
  apply FormalScheme.Hom.ext'
  change FormalSpectrum.locallyRingedSpaceMap (AdicCompletion.idealOfDefinition I)
      (AdicCompletion.idealOfDefinition K)
      (AdicCompletion.mapCompletion (g.comp f) _ hK) _ =
    FormalSpectrum.locallyRingedSpaceMap (AdicCompletion.idealOfDefinition J)
        (AdicCompletion.idealOfDefinition K) (AdicCompletion.mapCompletion g hg hK) _ ≫
      FormalSpectrum.locallyRingedSpaceMap (AdicCompletion.idealOfDefinition I)
        (AdicCompletion.idealOfDefinition J) (AdicCompletion.mapCompletion f hf hJ) _
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (AdicCompletion.idealOfDefinition I)
    (AdicCompletion.idealOfDefinition K) (AdicCompletion.mapCompletion (g.comp f) _ hK)
    ((AdicCompletion.mapCompletion g hg hK).comp (AdicCompletion.mapCompletion f hf hJ)) _
    (by rw [AdicCompletion.mapCompletion_comp f g hf hg hJ hK hI]
        exact Ideal.map_le_iff_le_comap.mp (AdicCompletion.idealOfDefinition_map_le (g.comp f)
          (by rw [← Ideal.map_map]; exact le_trans (Ideal.map_mono hf) hg) hK))
    (AdicCompletion.mapCompletion_comp f g hf hg hJ hK hI).symm]
  exact FormalSpectrum.locallyRingedSpaceMap_comp (AdicCompletion.idealOfDefinition I)
    (AdicCompletion.idealOfDefinition J) (AdicCompletion.idealOfDefinition K)
    (AdicCompletion.mapCompletion f hf hJ) (AdicCompletion.mapCompletion g hg hK) _ _ _

end formalCompletion
