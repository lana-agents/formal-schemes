import FormalSchemes.FormalScheme

set_option linter.style.header false

/-!
# Functoriality of the formal spectrum on locally ringed spaces

A ring homomorphism `φ : R →+* S` between adic rings mapping the ideal of definition `I` of `R`
into the ideal of definition `J` of `S` (equivalently, a continuous ring homomorphism) induces a
morphism of locally ringed spaces `Spf S ⟶ Spf R` (EGA I, 10.2.2). This file constructs the
underlying morphism of sheafed spaces: the continuous map is `FormalSpectrum.map`, and the map
of structure sheaves is assembled level-by-level from the maps
`StructureSheaf.comap (φ mod J ^ (n + 1))` between the structure sheaves of the thickenings,
using that the pushforward of sheaves along a continuous map preserves limits (it is a right
adjoint).

## Main definitions

* `FormalSpectrum.levelRingHom I J φ hφ n : R ⧸ I ^ (n + 1) →+* S ⧸ J ^ (n + 1)`: the induced
  map of thickenings.
* `FormalSpectrum.mapTop I J φ hφ`: the underlying continuous map `Spf S ⟶ Spf R` in `TopCat`.
* `FormalSpectrum.levelSheafHom I J φ hφ n`: the level-`n` map of thickening sheaves
  `thickeningSheaf I n ⟶ (mapTop _)_* thickeningSheaf J n`.
* `FormalSpectrum.mapSheafHom I J φ hφ`: the induced map of structure sheaves
  `O_{Spf R} ⟶ (mapTop _)_* O_{Spf S}`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hφ : I ≤ J.comap φ)

/-!
### The induced maps of thickenings
-/

section LevelMaps

include hφ in
theorem pow_le_comap (n : ℕ) : I ^ n ≤ (J ^ n).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hφ) n

/-- The map of `n`-th infinitesimal thickenings `R ⧸ I ^ (n + 1) →+* S ⧸ J ^ (n + 1)` induced
by a ring homomorphism `φ` with `φ(I) ⊆ J`. -/
def levelRingHom (n : ℕ) : R ⧸ I ^ (n + 1) →+* S ⧸ J ^ (n + 1) :=
  Ideal.quotientMap (J ^ (n + 1)) φ (pow_le_comap I J φ hφ (n + 1))

@[simp]
theorem levelRingHom_mk (n : ℕ) (x : R) :
    levelRingHom I J φ hφ n (Ideal.Quotient.mk (I ^ (n + 1)) x) =
      Ideal.Quotient.mk (J ^ (n + 1)) (φ x) :=
  Ideal.quotientMap_mk

/-- The maps of thickenings intertwine the transition maps of the two towers. -/
theorem levelRingHom_step (n : ℕ) :
    (levelRingHom I J φ hφ n).comp (stepRingHom I n).hom =
      (stepRingHom J n).hom.comp (levelRingHom I J φ hφ (n + 1)) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [show (stepRingHom I n).hom (Ideal.Quotient.mk (I ^ (n + 1 + 1)) x) =
      Ideal.Quotient.mk (I ^ (n + 1)) x from
    Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x,
    levelRingHom_mk, levelRingHom_mk,
    show (stepRingHom J n).hom (Ideal.Quotient.mk (J ^ (n + 1 + 1)) (φ x)) =
      Ideal.Quotient.mk (J ^ (n + 1)) (φ x) from
    Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (φ x)]

/-- The map of level-`1` thickenings `R ⧸ I →+* S ⧸ J`. -/
def residueRingHom : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J φ hφ

/-- The two paths `R ⧸ I ^ (n + 1) → S ⧸ J` around the square formed by the maps of
thickenings and the projections to the residue level agree. -/
theorem residueRingHom_comp_factor (n : ℕ) :
    (residueRingHom I J φ hφ).comp
        (Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero :
          (I ^ (n + 1) : Ideal R) ≤ I)) =
      (Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero :
          (J ^ (n + 1) : Ideal S) ≤ J)).comp (levelRingHom I J φ hφ n) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.factor_mk, levelRingHom_mk,
    residueRingHom]
  rw [Ideal.quotientMap_mk]

end LevelMaps

/-!
### The underlying continuous map, and the corresponding opens
-/

section BaseMap

/-- The underlying continuous map `Spf S ⟶ Spf R`, as a morphism in `TopCat`. -/
def mapTop : TopCat.of (FormalSpectrum J) ⟶ TopCat.of (FormalSpectrum I) :=
  TopCat.ofHom ⟨map I J φ hφ, continuous_map I J φ hφ⟩

/-- The square relating the map of formal spectra, the maps to the thickenings, and the induced
maps of thickenings: `Spec (φ mod J^(n+1))` restricted along the thickening homeomorphisms is
the map of formal spectra. -/
theorem comap_levelRingHom_toThickening (n : ℕ) (y : PrimeSpectrum (S ⧸ J ^ (n + 1))) :
    (thickeningTopIso I n).inv (PrimeSpectrum.comap (levelRingHom I J φ hφ n) y) =
      mapTop I J φ hφ ((thickeningTopIso J n).inv y) := by
  -- both sides are determined by their image under the homeomorphism `toThickening`
  apply (thickeningHomeomorph I (n + 1) n.succ_ne_zero).injective
  have h1 : (thickeningHomeomorph I (n + 1) n.succ_ne_zero)
      ((thickeningTopIso I n).inv (PrimeSpectrum.comap (levelRingHom I J φ hφ n) y)) =
      PrimeSpectrum.comap (levelRingHom I J φ hφ n) y :=
    (thickeningHomeomorph I (n + 1) n.succ_ne_zero).apply_symm_apply _
  rw [h1]
  -- the ring-level square
  have hring : ((residueRingHom I J φ hφ).comp
      (Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero))).comp
        (Ideal.Quotient.mk (I ^ (n + 1))) =
      ((Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero)).comp
        (levelRingHom I J φ hφ n)).comp (Ideal.Quotient.mk (I ^ (n + 1))) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact congrArg (fun ψ => ψ.comp (Ideal.Quotient.mk (I ^ (n + 1))))
      (residueRingHom_comp_factor I J φ hφ n)
  have hring' : (residueRingHom I J φ hφ).comp
      (Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero)) =
      (Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero)).comp
        (levelRingHom I J φ hφ n) :=
    residueRingHom_comp_factor I J φ hφ n
  -- compute both sides as `PrimeSpectrum.comap` of the two equal ring homomorphisms
  have lhs : (thickeningHomeomorph I (n + 1) n.succ_ne_zero)
      (mapTop I J φ hφ ((thickeningTopIso J n).inv y)) =
      PrimeSpectrum.comap ((residueRingHom I J φ hφ).comp
        (Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero)))
        ((thickeningHomeomorph J (n + 1) n.succ_ne_zero).symm y) := by
    rw [PrimeSpectrum.comap_comp]
    rfl
  rw [lhs, hring', PrimeSpectrum.comap_comp]
  simp only [Function.comp_apply]
  congr 1
  exact ((thickeningHomeomorph J (n + 1) n.succ_ne_zero).apply_symm_apply y).symm

/-- The opens of the thickenings corresponding to `U ⊆ Spf R` and its preimage in `Spf S` are
compatible with `Spec` of the induced maps of thickenings. -/
theorem thickeningOpen_map_le (n : ℕ) (U : Opens (FormalSpectrum I)) :
    (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj U) :
      Set (PrimeSpectrum (S ⧸ J ^ (n + 1)))) ⊆
      PrimeSpectrum.comap (levelRingHom I J φ hφ n) ⁻¹'
        (thickeningOpen I n U : Set (PrimeSpectrum (R ⧸ I ^ (n + 1)))) := by
  intro y hy
  change (thickeningTopIso I n).inv (PrimeSpectrum.comap (levelRingHom I J φ hφ n) y) ∈ U
  rw [comap_levelRingHom_toThickening]
  exact hy

end BaseMap

/-!
### The induced map of structure sheaves
-/

section SheafMap

/-- The level-`n` map of thickening sheaves `thickeningSheaf I n ⟶ (mapTop)_* thickeningSheaf
J n`, given over each open `U ⊆ Spf R` by `StructureSheaf.comap` of the induced map of
thickenings. -/
def levelSheafHom (n : ℕ) :
    thickeningSheaf I n ⟶
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj (thickeningSheaf J n) :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        (StructureSheaf.comap (levelRingHom I J φ hφ n)
          (thickeningOpen I n U.unop)
          (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj U.unop))
          (thickeningOpen_map_le I J φ hφ n U.unop))
      naturality := fun U V i => by
        apply CommRingCat.hom_ext
        rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
        exact comap_comp_map (levelRingHom I J φ hφ n)
          ((Opens.map (thickeningTopIso I n).inv).map i.unop)
          ((Opens.map (thickeningTopIso J n).inv).map ((Opens.map (mapTop I J φ hφ)).map i.unop))
          (thickeningOpen_map_le I J φ hφ n U.unop)
          (thickeningOpen_map_le I J φ hφ n V.unop) }

theorem levelSheafHom_hom_app (n : ℕ) (U : Opens (FormalSpectrum I)) :
    (levelSheafHom I J φ hφ n).hom.app (op U) =
      CommRingCat.ofHom (StructureSheaf.comap (levelRingHom I J φ hφ n)
        (thickeningOpen I n U) (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj U))
        (thickeningOpen_map_le I J φ hφ n U)) :=
  rfl

theorem comp_hom_app_left (n : ℕ) (U : (Opens (FormalSpectrum I))ᵒᵖ) :
    (stepSheafHom I n ≫ levelSheafHom I J φ hφ n).hom.app U =
      (stepSheafHom I n).hom.app U ≫ (levelSheafHom I J φ hφ n).hom.app U :=
  rfl

theorem comp_hom_app_right (n : ℕ) (U : (Opens (FormalSpectrum I))ᵒᵖ) :
    (levelSheafHom I J φ hφ (n + 1) ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map (stepSheafHom J n)).hom.app
        U =
      (levelSheafHom I J φ hφ (n + 1)).hom.app U ≫
        (stepSheafHom J n).hom.app (op ((Opens.map (mapTop I J φ hφ)).obj U.unop)) :=
  rfl

set_option linter.style.setOption false in
set_option maxHeartbeats 4000000 in
-- Verifying the composite of `StructureSheaf.comap`s against `comap` of the composite ring
-- homomorphism unfolds the section rings of the structure sheaves, which is slow.
theorem comap_levelRingHom_square (n : ℕ) (V : Opens (FormalSpectrum I)) :
    (StructureSheaf.comap (levelRingHom I J φ hφ n)
        (thickeningOpen I n V) (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen_map_le I J φ hφ n V)).comp
      (StructureSheaf.comap (stepRingHom I n).hom
        (thickeningOpen I (n + 1) V) (thickeningOpen I n V)
        (thickeningOpen_le_comap I n V)) =
      (StructureSheaf.comap (stepRingHom J n).hom
        (thickeningOpen J (n + 1) ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen_le_comap J n ((Opens.map (mapTop I J φ hφ)).obj V))).comp
      (StructureSheaf.comap (levelRingHom I J φ hφ (n + 1))
        (thickeningOpen I (n + 1) V)
        (thickeningOpen J (n + 1) ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen_map_le I J φ hφ (n + 1) V)) :=
  (StructureSheaf.comap_comp (stepRingHom I n).hom (levelRingHom I J φ hφ n)
      (thickeningOpen I (n + 1) V) (thickeningOpen I n V)
      (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V))
      (thickeningOpen_le_comap I n V)
      (thickeningOpen_map_le I J φ hφ n V)).symm.trans
    ((comap_congr (levelRingHom_step I J φ hφ n) _ _ _ _).trans
      (StructureSheaf.comap_comp (levelRingHom I J φ hφ (n + 1)) (stepRingHom J n).hom
        (thickeningOpen I (n + 1) V)
        (thickeningOpen J (n + 1) ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen_map_le I J φ hφ (n + 1) V)
        (thickeningOpen_le_comap J n ((Opens.map (mapTop I J φ hφ)).obj V))))

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
-- Bundling the previous square into `CommRingCat` is still slow for the kernel.
theorem ofHom_comap_levelRingHom_square (n : ℕ) (V : Opens (FormalSpectrum I)) :
    CommRingCat.ofHom (StructureSheaf.comap (stepRingHom I n).hom
        (thickeningOpen I (n + 1) V) (thickeningOpen I n V)
        (thickeningOpen_le_comap I n V)) ≫
      CommRingCat.ofHom (StructureSheaf.comap (levelRingHom I J φ hφ n)
        (thickeningOpen I n V) (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen_map_le I J φ hφ n V)) =
      CommRingCat.ofHom (StructureSheaf.comap (levelRingHom I J φ hφ (n + 1))
        (thickeningOpen I (n + 1) V)
        (thickeningOpen J (n + 1) ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen_map_le I J φ hφ (n + 1) V)) ≫
      CommRingCat.ofHom (StructureSheaf.comap (stepRingHom J n).hom
        (thickeningOpen J (n + 1) ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V))
        (thickeningOpen_le_comap J n ((Opens.map (mapTop I J φ hφ)).obj V))) :=
  (CommRingCat.ofHom_comp _ _).symm.trans
    ((congrArg CommRingCat.ofHom (comap_levelRingHom_square I J φ hφ n V)).trans
      (CommRingCat.ofHom_comp _ _))

/-- The level sheaf maps intertwine the transition maps of the two towers of thickening
sheaves. -/
theorem levelSheafHom_step (n : ℕ) :
    stepSheafHom I n ≫ levelSheafHom I J φ hφ n =
      levelSheafHom I J φ hφ (n + 1) ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map (stepSheafHom J n) := by
  refine InducedCategory.Hom.ext (NatTrans.ext (funext fun U => ?_))
  induction U using Opposite.rec with
  | op V =>
    rw [comp_hom_app_left I J φ hφ n (op V), comp_hom_app_right I J φ hφ n (op V)]
    have e1 := congrArg₂ (· ≫ ·) (stepSheafHom_hom_app I n V)
      (levelSheafHom_hom_app I J φ hφ n V)
    have e2 := congrArg₂ (· ≫ ·) (levelSheafHom_hom_app I J φ hφ (n + 1) V)
      (stepSheafHom_hom_app J n ((Opens.map (mapTop I J φ hφ)).obj V))
    exact e1.trans ((ofHom_comap_levelRingHom_square I J φ hφ n V).trans e2.symm)

/-- The natural transformation between the two towers of thickening sheaves induced by `φ`. -/
def levelNatTrans : structureSheafFunctor I ⟶
    structureSheafFunctor J ⋙ TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ) :=
  NatTrans.ofOpSequence (fun n => levelSheafHom I J φ hφ n) (fun n => by
    rw [structureSheafFunctor_map_succ]
    have h : (structureSheafFunctor J ⋙
          TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map
        (homOfLE (Nat.le_add_right n 1)).op =
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map (stepSheafHom J n) := by
      change (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map
        ((structureSheafFunctor J).map (homOfLE (Nat.le_add_right n 1)).op) = _
      rw [structureSheafFunctor_map_succ]
      rfl
    rw [h]
    exact levelSheafHom_step I J φ hφ n)

@[simp]
theorem levelNatTrans_app (n : ℕ) :
    (levelNatTrans I J φ hφ).app ⟨n⟩ = levelSheafHom I J φ hφ n :=
  rfl

/-- The induced morphism of structure sheaves `O_{Spf R} ⟶ (mapTop)_* O_{Spf S}`: since the
pushforward of sheaves is a right adjoint, it preserves the limit defining `O_{Spf S}`, and the
level maps induce a morphism of the limits. -/
def mapSheafHom : structureSheaf I ⟶
    (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj (structureSheaf J) :=
  limMap (levelNatTrans I J φ hφ) ≫
    (preservesLimitIso (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ))
      (structureSheafFunctor J)).inv

/-- The induced morphism of structure sheaves is compatible with the limit projections to the
levels of the towers. -/
theorem mapSheafHom_π (n : ℕ) :
    mapSheafHom I J φ hφ ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map
          (limit.π (structureSheafFunctor J) ⟨n⟩) =
      limit.π (structureSheafFunctor I) ⟨n⟩ ≫ levelSheafHom I J φ hφ n := by
  have h2 : (preservesLimitIso (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ))
      (structureSheafFunctor J)).inv ≫
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map
        (limit.π (structureSheafFunctor J) ⟨n⟩) =
      limit.π (structureSheafFunctor J ⋙
        TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)) ⟨n⟩ :=
    preservesLimitIso_inv_π _ _ _
  have h1 : mapSheafHom I J φ hφ ≫
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map
        (limit.π (structureSheafFunctor J) ⟨n⟩) =
      (limMap (levelNatTrans I J φ hφ) ≫
        ((preservesLimitIso (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ))
          (structureSheafFunctor J)).inv ≫
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map
            (limit.π (structureSheafFunctor J) ⟨n⟩)) :
        structureSheaf I ⟶
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj
            (thickeningSheaf J n)) := by
    simp only [mapSheafHom, Category.assoc]
    rfl
  have h2' : (limMap (levelNatTrans I J φ hφ) ≫
        ((preservesLimitIso (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ))
          (structureSheafFunctor J)).inv ≫
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).map
            (limit.π (structureSheafFunctor J) ⟨n⟩)) :
        structureSheaf I ⟶
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj
            (thickeningSheaf J n)) =
      (limMap (levelNatTrans I J φ hφ) ≫
        limit.π (structureSheafFunctor J ⋙
          TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)) ⟨n⟩ :
        structureSheaf I ⟶
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj
            (thickeningSheaf J n)) :=
    congrArg (fun t => limMap (levelNatTrans I J φ hφ) ≫ t) h2
  have h3 : (limMap (levelNatTrans I J φ hφ) ≫
        limit.π (structureSheafFunctor J ⋙
          TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)) ⟨n⟩ :
        structureSheaf I ⟶
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj
            (thickeningSheaf J n)) =
      limit.π (structureSheafFunctor I) ⟨n⟩ ≫ levelSheafHom I J φ hφ n :=
    (limMap_π (levelNatTrans I J φ hφ) ⟨n⟩).trans (by rw [levelNatTrans_app]; rfl)
  exact h1.trans (h2'.trans h3)

end SheafMap

/-!
### The morphism of locally ringed spaces
-/

section LocallyRingedSpaceMap

/-- The preimage of a basic open under the map of formal spectra is a basic open. -/
theorem map_preimage_basicOpen (f₀ : R) :
    (Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀) = basicOpen J (φ f₀) := by
  apply Opens.ext
  ext y
  change Ideal.Quotient.mk I f₀ ∉ (map I J φ hφ y).asIdeal ↔
    Ideal.Quotient.mk J (φ f₀) ∉ y.asIdeal
  change Ideal.Quotient.mk I f₀ ∉
    (PrimeSpectrum.comap (Ideal.quotientMap J φ hφ) y).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.quotientMap_mk]

/-- The maps of thickenings match up the distinguished points: the image under
`Spec (levelRingHom)` of the point of the thickening of `Spf S` corresponding to `y` is the
point corresponding to `mapTop y`. -/
theorem comap_levelRingHom_hom (n : ℕ) (y : FormalSpectrum J) :
    PrimeSpectrum.comap (levelRingHom I J φ hφ n) ((thickeningTopIso J n).hom y) =
      (thickeningTopIso I n).hom (mapTop I J φ hφ y) := by
  apply (thickeningHomeomorph I (n + 1) n.succ_ne_zero).symm.injective
  have h1 := comap_levelRingHom_toThickening I J φ hφ n ((thickeningTopIso J n).hom y)
  have h2 : (thickeningTopIso J n).inv ((thickeningTopIso J n).hom y) = y :=
    inv_hom_apply J n y
  rw [h2] at h1
  refine h1.trans ?_
  exact (inv_hom_apply I n (mapTop I J φ hφ y)).symm

/-- The underlying morphism of presheafed spaces `Spf S ⟶ Spf R`. -/
def presheafedSpaceMap :
    (sheafedSpaceObj J).toPresheafedSpace ⟶ (sheafedSpaceObj I).toPresheafedSpace where
  base := mapTop I J φ hφ
  c := (mapSheafHom I J φ hφ).hom

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
-- The proof chases a germ through the level-0 projections of both structure sheaves and
-- evaluates it, which unfolds the section rings of the structure sheaves; this is slow.
/-- The stalk maps of the induced morphism of formal spectra are local ring homomorphisms:
a germ of `O_{Spf R}` whose image is invertible is invertible, because invertibility is
detected by the value of the level-`0` component, and on values the morphism acts by the
local homomorphism `Localization.localRingHom`. -/
theorem isLocalHom_stalkMap (y : FormalSpectrum J) :
    IsLocalHom ((presheafedSpaceMap I J φ hφ).stalkMap y).hom := by
  constructor
  intro a ha
  -- represent the germ by a section over a basic open around `x = mapTop y`
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ a
  obtain ⟨w, hw, hxw, hwU⟩ := (isTopologicalBasis_basicOpen I).exists_subset_of_mem_open
    hxU U.2
  obtain ⟨f₀, rfl⟩ := hw
  have hDU : basicOpen I f₀ ≤ U := hwU
  set s' := (structureSheaf I).presheaf.map (homOfLE hDU).op s with hs'
  have hgerm : ((structureSheaf I).presheaf.germ (basicOpen I f₀)
        (mapTop I J φ hφ y) hxw).hom s' =
      ((structureSheaf I).presheaf.germ U (mapTop I J φ hφ y) hxU).hom s :=
    (structureSheaf I).presheaf.germ_res_apply (homOfLE hDU) (mapTop I J φ hφ y) hxw s
  -- normalize the hypothesis and the goal to the restricted section
  have ha' : IsUnit (((presheafedSpaceMap I J φ hφ).stalkMap y).hom
      (((structureSheaf I).presheaf.germ (basicOpen I f₀)
        (mapTop I J φ hφ y) hxw).hom s')) := by
    have h0 : IsUnit (((presheafedSpaceMap I J φ hφ).stalkMap y).hom
        (((structureSheaf I).presheaf.germ U (mapTop I J φ hφ y) hxU).hom s)) := ha
    rwa [← hgerm] at h0
  suffices h : IsUnit (((structureSheaf I).presheaf.germ (basicOpen I f₀)
      (mapTop I J φ hφ y) hxw).hom s') by
    have hgoal : IsUnit (((structureSheaf I).presheaf.germ U
        (mapTop I J φ hφ y) hxU).hom s) := by rwa [hgerm] at h
    exact hgoal
  -- it suffices that the level-0 component of `s'` has invertible germ
  apply isUnit_stalk_of_isUnit_zero I (mapTop I J φ hφ y)
  rw [show ((stalkProj I (mapTop I J φ hφ y) 0).hom
      (((structureSheaf I).presheaf.germ (basicOpen I f₀) (mapTop I J φ hφ y) hxw).hom s')) =
      ((thickeningSheaf I 0).presheaf.germ (basicOpen I f₀) (mapTop I J φ hφ y) hxw).hom
        (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op (basicOpen I f₀))).hom s') from
    TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
      (limit.π (structureSheafFunctor I) ⟨0⟩).hom s']
  -- switch to values via the criterion on `D(f₀)`
  haveI : IsLocalization.Away (Ideal.Quotient.mk (I ^ (0 + 1)) f₀)
      (((Spec.structureSheaf (R ⧸ I ^ (0 + 1))).presheaf.obj
        (op (thickeningOpen I 0 (basicOpen I f₀))) : Type u)) :=
    isLocalization_away_basicOpen_sections I 0 f₀
  rw [isUnit_thickeningGerm_iff_isUnit_value I 0 (mapTop I J φ hφ y) (basicOpen I f₀) hxw
    (Ideal.Quotient.mk (I ^ (0 + 1)) f₀)]
  -- the image germ is invertible, so the level-0 germ of the image section is invertible
  have hb : IsUnit (((thickeningSheaf J 0).presheaf.germ
      ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)) y hxw).hom
      (((limit.π (structureSheafFunctor J) ⟨0⟩).hom.app
        (op ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)))).hom
        (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom s'))) := by
    have hst : ((presheafedSpaceMap I J φ hφ).stalkMap y).hom
        (((structureSheaf I).presheaf.germ (basicOpen I f₀) (mapTop I J φ hφ y) hxw).hom s') =
        ((structureSheaf J).presheaf.germ
          ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)) y hxw).hom
          (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom s') :=
      AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply
        (presheafedSpaceMap I J φ hφ) (basicOpen I f₀) y hxw s'
    have h1 := ha'
    rw [hst] at h1
    have h2 := h1.map (stalkProj J y 0).hom
    have hkey : ((stalkProj J y 0).hom
        (((structureSheaf J).presheaf.germ
          ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)) y hxw).hom
          (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom s'))) =
        ((thickeningSheaf J 0).presheaf.germ
          ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)) y hxw).hom
          (((limit.π (structureSheafFunctor J) ⟨0⟩).hom.app
            (op ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)))).hom
            (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom s')) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
        (limit.π (structureSheafFunctor J) ⟨0⟩).hom _
    exact hkey ▸ h2
  -- transfer the invertibility of the level-0 germ on the S-side to values
  haveI hSloc : IsLocalization.Away (Ideal.Quotient.mk (J ^ (0 + 1)) (φ f₀))
      (((Spec.structureSheaf (S ⧸ J ^ (0 + 1))).presheaf.obj
        (op (thickeningOpen J 0 ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)))) :
          Type u)) :=
    (map_preimage_basicOpen I J φ hφ f₀).symm ▸
      isLocalization_away_basicOpen_sections J 0 (φ f₀)
  have hbv := (isUnit_thickeningGerm_iff_isUnit_value J 0 y
    ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)) hxw
    (Ideal.Quotient.mk (J ^ (0 + 1)) (φ f₀)) _).mp hb
  -- rewrite the section through the compatibility of `mapSheafHom` with the projections
  have hsec : (((limit.π (structureSheafFunctor J) ⟨0⟩).hom.app
      (op ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)))).hom
      (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom s')) =
      ((levelSheafHom I J φ hφ 0).hom.app (op (basicOpen I f₀))).hom
        (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op (basicOpen I f₀))).hom s') :=
    DFunLike.congr_fun (congrArg (fun (α : structureSheaf I ⟶
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj (thickeningSheaf J 0)) =>
        (α.hom.app (op (basicOpen I f₀))).hom) (mapSheafHom_π I J φ hφ 0)) s'
  replace hbv := hsec ▸ hbv
  -- on values, the level map acts by the local homomorphism `Localization.localRingHom`
  have hval : StructureSheaf.sectionValue
      (thickeningOpen J 0 ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)))
      ((thickeningTopIso J 0).hom y) (hom_mem_thickeningOpen J 0 y hxw)
      (((levelSheafHom I J φ hφ 0).hom.app (op (basicOpen I f₀))).hom
        (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op (basicOpen I f₀))).hom s')) =
      Localization.localRingHom
        (PrimeSpectrum.comap (levelRingHom I J φ hφ 0)
          ((thickeningTopIso J 0).hom y)).asIdeal
        ((thickeningTopIso J 0).hom y).asIdeal (levelRingHom I J φ hφ 0) rfl
        ((((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op (basicOpen I f₀))).hom s').1
          ⟨PrimeSpectrum.comap (levelRingHom I J φ hφ 0) ((thickeningTopIso J 0).hom y),
            thickeningOpen_map_le I J φ hφ 0 (basicOpen I f₀)
              (hom_mem_thickeningOpen J 0 y hxw)⟩) :=
    StructureSheaf.comap_apply (levelRingHom I J φ hφ 0)
      (thickeningOpen I 0 (basicOpen I f₀))
      (thickeningOpen J 0 ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀)))
      (thickeningOpen_map_le I J φ hφ 0 (basicOpen I f₀))
      (((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app (op (basicOpen I f₀))).hom s')
      ⟨(thickeningTopIso J 0).hom y, hom_mem_thickeningOpen J 0 y hxw⟩
  replace hbv := hval ▸ hbv
  -- `localRingHom` is a local ring homomorphism, so the value on the R-side is a unit
  haveI hloc := Localization.isLocalHom_localRingHom
    (PrimeSpectrum.comap (levelRingHom I J φ hφ 0) ((thickeningTopIso J 0).hom y)).asIdeal
    ((thickeningTopIso J 0).hom y).asIdeal (levelRingHom I J φ hφ 0) rfl
  have hu := hloc.map_nonunit _ hbv
  -- finally transport the evaluation point to the point corresponding to `mapTop y`
  have hpt : (⟨PrimeSpectrum.comap (levelRingHom I J φ hφ 0) ((thickeningTopIso J 0).hom y),
      thickeningOpen_map_le I J φ hφ 0 (basicOpen I f₀)
        (hom_mem_thickeningOpen J 0 y hxw)⟩ :
      (thickeningOpen I 0 (basicOpen I f₀) : Set (PrimeSpectrum (R ⧸ I ^ (0 + 1))))) =
      ⟨(thickeningTopIso I 0).hom (mapTop I J φ hφ y),
        hom_mem_thickeningOpen I 0 (mapTop I J φ hφ y) hxw⟩ :=
    Subtype.ext (comap_levelRingHom_hom I J φ hφ 0 y)
  change IsUnit ((((limit.π (structureSheafFunctor I) ⟨0⟩).hom.app
    (op (basicOpen I f₀))).hom s').1
    ⟨(thickeningTopIso I 0).hom (mapTop I J φ hφ y),
      hom_mem_thickeningOpen I 0 (mapTop I J φ hφ y) hxw⟩)
  exact hpt ▸ hu

/-- **Functoriality of the formal spectrum** (EGA I, 10.2.2): a ring homomorphism `φ : R →+* S`
between adic rings carrying the ideal of definition of `R` into that of `S` (equivalently, a
continuous ring homomorphism) induces a morphism of locally ringed spaces `Spf S ⟶ Spf R`. -/
def locallyRingedSpaceMap : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I where
  toHom := presheafedSpaceMap I J φ hφ
  prop y := isLocalHom_stalkMap I J φ hφ y

/-- The induced morphism of affine formal schemes `Spf S ⟶ Spf R`. -/
def spfMap [TopologicalSpace R] [TopologicalSpace S] [IsAdicRing I] [IsAdicRing J] :
    FormalScheme.Spf J ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk (locallyRingedSpaceMap I J φ hφ)

end LocallyRingedSpaceMap





end FormalSpectrum
