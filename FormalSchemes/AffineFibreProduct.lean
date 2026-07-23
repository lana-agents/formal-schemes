import FormalSchemes.CompletedTensorFunctor
import FormalSchemes.SpfFunctorial

set_option linter.style.header false

/-!
# The affine fibre product of formal spectra

For a base adic ring `(R, I)` (with `I` finitely generated) and two complete adic `R`-algebras
`A`, `B` whose ideals of definition are the extensions `I·A`, `I·B`, the completed tensor product
`A ⊗̂_R B` (`FormalSchemes.CompletedTensor`) is the coordinate ring of the **fibre product**
`Spf A ×_{Spf R} Spf B` (EGA I, 10.7). This file packages that geometric structure at the level of
locally ringed spaces, entirely from the merged algebraic universal property of the completed
tensor product (`inl`/`inr`/`lift`/`lift_inl`/`lift_inr`) and the merged functor laws for `Spf`
(`FormalSpectrum.locallyRingedSpaceMap_comp`/`_congr`, issue 60).

## Main definitions and results

* `CompletedTensorProduct.inl_isAdicHom`, `inr_isAdicHom`: the canonical maps `A → A ⊗̂_R B`,
  `B → A ⊗̂_R B` are adic morphisms.
* `CompletedTensorProduct.fibrePr₁`, `fibrePr₂`: the two projections
  `Spf (A ⊗̂_R B) ⟶ Spf A`, `Spf (A ⊗̂_R B) ⟶ Spf B`.
* `CompletedTensorProduct.fibreStructMap`: the structural morphism `Spf (A ⊗̂_R B) ⟶ Spf R`.
* `CompletedTensorProduct.fibrePr₁_comp_structMap`, `fibrePr₂_comp_structMap`,
  `fibre_cone_comm`: the fibre-product square commutes over `Spf R`.
* `CompletedTensorProduct.fibreLift`: the mediating morphism `Spf S ⟶ Spf (A ⊗̂_R B)` induced by a
  pair of `R`-algebra maps `f : A →ₐ[R] S`, `g : B →ₐ[R] S` into a complete adic `R`-algebra `S`,
  with `fibreLift_comp_pr₁`/`fibreLift_comp_pr₂` witnessing that it recovers `f` and `g` after the
  two projections.

**Scope.** This delivers the existence and commutativity halves of the fibre-product universal
property. Full uniqueness of the mediating morphism *in the category of locally ringed spaces*
requires the Spf–Γ adjunction (recognising an arbitrary locally-ringed-space morphism into
`Spf (A ⊗̂_R B)` as `Spf` of a ring homomorphism, issue 96); among `Spf`-of-ring-map morphisms
uniqueness is `CompletedTensorProduct.hom_ext`. Packaging as a `Limits.IsLimit` is left as a
follow-up gated on issue 96.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-!
### Adicity of the canonical maps (pure algebra)
-/

/-- The canonical map `A → A ⊗̂_R B` is an adic morphism: it carries the ideal of definition
`I·A` of `A` onto the ideal of definition of `A ⊗̂_R B`. -/
theorem inl_isAdicHom :
    IsAdicHom (I.map (algebraMap R A)) (idealOfDefinition R I A B) (inl R I A B).toRingHom := by
  unfold IsAdicHom
  rw [Ideal.map_map,
    show (inl R I A B).toRingHom.comp (algebraMap R A) =
      algebraMap R (CompletedTensorProduct R I A B) from AlgHom.comp_algebraMap (inl R I A B),
    idealOfDefinition_eq_map]

/-- The canonical map `B → A ⊗̂_R B` is an adic morphism. -/
theorem inr_isAdicHom :
    IsAdicHom (I.map (algebraMap R B)) (idealOfDefinition R I A B) (inr R I A B).toRingHom := by
  unfold IsAdicHom
  rw [Ideal.map_map,
    show (inr R I A B).toRingHom.comp (algebraMap R B) =
      algebraMap R (CompletedTensorProduct R I A B) from AlgHom.comp_algebraMap (inr R I A B),
    idealOfDefinition_eq_map]

/-- The structural map `R → A ⊗̂_R B` is an adic morphism. -/
theorem algebraMap_isAdicHom :
    IsAdicHom I (idealOfDefinition R I A B)
      (algebraMap R (CompletedTensorProduct R I A B)) :=
  idealOfDefinition_eq_map.symm

section LiftAlgebra

variable {S : Type u} [CommRing S] [Algebra R S] {L : Ideal S}

/-- An `R`-algebra map `f : A →ₐ[R] S` into a complete adic `R`-algebra `S` carries the ideal of
definition `I·A` into `L`, hence induces a morphism of formal spectra `Spf S ⟶ Spf A`. -/
theorem algHom_le_comap (f : A →ₐ[R] S) (hIL : I.map (algebraMap R S) ≤ L) :
    I.map (algebraMap R A) ≤ L.comap f.toRingHom := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap,
    show f.toRingHom.comp (algebraMap R A) = algebraMap R S from AlgHom.comp_algebraMap f,
    ← Ideal.map_le_iff_le_comap]
  exact hIL

variable [IsAdicComplete L S]

/-- The universal map `lift : A ⊗̂_R B → S` carries the ideal of definition into `L`, hence induces
a morphism of formal spectra. -/
theorem lift_le_comap (hIL : I.map (algebraMap R S) ≤ L) (f : A →ₐ[R] S) (g : B →ₐ[R] S)
    (hI : I.FG) :
    idealOfDefinition R I A B ≤ L.comap (lift L hIL f g) := fun x hx => by
  have h := lift_mem_pow L hIL f g hI 1 (by rwa [pow_one])
  rw [pow_one] at h
  exact h

end LiftAlgebra

/-!
### The geometric fibre-product cone
-/

section Geometric

variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))]
variable [TopologicalSpace (CompletedTensorProduct R I A B)]
  [IsAdicRing (idealOfDefinition R I A B)]

/-- The **first projection** `Spf (A ⊗̂_R B) ⟶ Spf A` of the affine fibre product, induced by the
canonical adic map `inl : A → A ⊗̂_R B`. The `IsAdicRing (idealOfDefinition R I A B)` instance is
`CompletedTensorProduct.isAdicRing hI` for `hI : I.FG`; supply it with `haveI` at the call site. -/
def fibrePr₁ :
    locallyRingedSpaceObj (idealOfDefinition R I A B) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R A)) :=
  inl_isAdicHom.spfMap

/-- The **second projection** `Spf (A ⊗̂_R B) ⟶ Spf B` of the affine fibre product. -/
def fibrePr₂ :
    locallyRingedSpaceObj (idealOfDefinition R I A B) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R B)) :=
  inr_isAdicHom.spfMap

/-- The **structural morphism** `Spf (A ⊗̂_R B) ⟶ Spf R` of the affine fibre product. -/
def fibreStructMap :
    locallyRingedSpaceObj (idealOfDefinition R I A B) ⟶ locallyRingedSpaceObj I :=
  algebraMap_isAdicHom.spfMap

set_option linter.unusedSectionVars false in
/-- The fibre-product square commutes over `Spf R` on the first factor: the first projection
followed by the structural morphism of `Spf A` is the structural morphism of `Spf (A ⊗̂_R B)`. -/
theorem fibrePr₁_comp_structMap :
    fibrePr₁ (R := R) (A := A) (B := B) ≫ (IsAdicHom.of_map I (A := A)).spfMap =
      fibreStructMap := by
  simp only [fibrePr₁, fibreStructMap, IsAdicHom.spfMap]
  rw [← locallyRingedSpaceMap_comp (I := I) (J := I.map (algebraMap R A))
    (K := idealOfDefinition R I A B) (φ := algebraMap R A) (ψ := (inl R I A B).toRingHom)
    (hIJ := (IsAdicHom.of_map I (A := A)).le_comap) (hJK := inl_isAdicHom.le_comap)
    (hIK := ((IsAdicHom.of_map I (A := A)).comp inl_isAdicHom).le_comap)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ (AlgHom.comp_algebraMap (inl R I A B))

set_option linter.unusedSectionVars false in
/-- The fibre-product square commutes over `Spf R` on the second factor. -/
theorem fibrePr₂_comp_structMap :
    fibrePr₂ (R := R) (A := A) (B := B) ≫ (IsAdicHom.of_map I (A := B)).spfMap =
      fibreStructMap := by
  simp only [fibrePr₂, fibreStructMap, IsAdicHom.spfMap]
  rw [← locallyRingedSpaceMap_comp (I := I) (J := I.map (algebraMap R B))
    (K := idealOfDefinition R I A B) (φ := algebraMap R B) (ψ := (inr R I A B).toRingHom)
    (hIJ := (IsAdicHom.of_map I (A := B)).le_comap) (hJK := inr_isAdicHom.le_comap)
    (hIK := ((IsAdicHom.of_map I (A := B)).comp inr_isAdicHom).le_comap)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ (AlgHom.comp_algebraMap (inr R I A B))

/-- The fibre-product square commutes: the two projections agree over `Spf R`. -/
theorem fibre_cone_comm :
    fibrePr₁ (R := R) (A := A) (B := B) ≫ (IsAdicHom.of_map I (A := A)).spfMap =
      fibrePr₂ ≫ (IsAdicHom.of_map I (A := B)).spfMap := by
  rw [fibrePr₁_comp_structMap, fibrePr₂_comp_structMap]

section Lift

variable {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
variable (hIL : I.map (algebraMap R S) ≤ L) (f : A →ₐ[R] S) (g : B →ₐ[R] S)

/-- The **mediating morphism** `Spf S ⟶ Spf (A ⊗̂_R B)` of the fibre-product universal property,
induced by a pair of `R`-algebra maps `f : A →ₐ[R] S`, `g : B →ₐ[R] S`. -/
def fibreLift (hI : I.FG) :
    locallyRingedSpaceObj L ⟶ locallyRingedSpaceObj (idealOfDefinition R I A B) :=
  locallyRingedSpaceMap (idealOfDefinition R I A B) L (lift L hIL f g)
    (lift_le_comap hIL f g hI)

set_option linter.style.setOption false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 800000 in
-- The `lift` term unfolds into the completion's continuous-extension machinery, which is slow for
-- the kernel when comparing the composite structure-sheaf maps against `Spf f`.
/-- The mediating morphism recovers `f` after the first projection. -/
theorem fibreLift_comp_pr₁ (hI : I.FG) :
    fibreLift hIL f g hI ≫ fibrePr₁ =
      locallyRingedSpaceMap (I.map (algebraMap R A)) L f.toRingHom (algHom_le_comap f hIL) := by
  have hik : I.map (algebraMap R A) ≤
      L.comap ((lift L hIL f g).comp (inl R I A B).toRingHom) := by
    rw [← Ideal.comap_comap, ← Ideal.map_le_iff_le_comap,
      show Ideal.map (inl R I A B).toRingHom (I.map (algebraMap R A)) =
        idealOfDefinition R I A B from inl_isAdicHom]
    exact lift_le_comap hIL f g hI
  change locallyRingedSpaceMap (idealOfDefinition R I A B) L (lift L hIL f g)
        (lift_le_comap hIL f g hI) ≫
      locallyRingedSpaceMap (I.map (algebraMap R A)) (idealOfDefinition R I A B)
        (inl R I A B).toRingHom inl_isAdicHom.le_comap =
      locallyRingedSpaceMap (I.map (algebraMap R A)) L f.toRingHom (algHom_le_comap f hIL)
  rw [← locallyRingedSpaceMap_comp (I := I.map (algebraMap R A))
    (J := idealOfDefinition R I A B) (K := L) (φ := (inl R I A B).toRingHom) (ψ := lift L hIL f g)
    (hIJ := inl_isAdicHom.le_comap) (hJK := lift_le_comap hIL f g hI) (hIK := hik)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ (RingHom.ext fun a => lift_inl L hIL f g a)

set_option linter.style.setOption false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 800000 in
-- The `lift` term unfolds into the completion's continuous-extension machinery, which is slow for
-- the kernel when comparing the composite structure-sheaf maps against `Spf g`.
/-- The mediating morphism recovers `g` after the second projection. -/
theorem fibreLift_comp_pr₂ (hI : I.FG) :
    fibreLift hIL f g hI ≫ fibrePr₂ =
      locallyRingedSpaceMap (I.map (algebraMap R B)) L g.toRingHom (algHom_le_comap g hIL) := by
  have hik : I.map (algebraMap R B) ≤
      L.comap ((lift L hIL f g).comp (inr R I A B).toRingHom) := by
    rw [← Ideal.comap_comap, ← Ideal.map_le_iff_le_comap,
      show Ideal.map (inr R I A B).toRingHom (I.map (algebraMap R B)) =
        idealOfDefinition R I A B from inr_isAdicHom]
    exact lift_le_comap hIL f g hI
  change locallyRingedSpaceMap (idealOfDefinition R I A B) L (lift L hIL f g)
        (lift_le_comap hIL f g hI) ≫
      locallyRingedSpaceMap (I.map (algebraMap R B)) (idealOfDefinition R I A B)
        (inr R I A B).toRingHom inr_isAdicHom.le_comap =
      locallyRingedSpaceMap (I.map (algebraMap R B)) L g.toRingHom (algHom_le_comap g hIL)
  rw [← locallyRingedSpaceMap_comp (I := I.map (algebraMap R B))
    (J := idealOfDefinition R I A B) (K := L) (φ := (inr R I A B).toRingHom) (ψ := lift L hIL f g)
    (hIJ := inr_isAdicHom.le_comap) (hJK := lift_le_comap hIL f g hI) (hIK := hik)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ (RingHom.ext fun b => lift_inr L hIL f g b)

end Lift

end Geometric

end CompletedTensorProduct
