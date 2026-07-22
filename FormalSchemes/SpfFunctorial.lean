import FormalSchemes.SpfMap

set_option linter.style.header false

/-!
# Functoriality of the formal spectrum: identity and composition laws

`FormalSchemes/SpfMap.lean` constructs, for a continuous ring homomorphism `φ : R →+* S`
between adic rings (`I ≤ J.comap φ`), the induced morphism of locally ringed spaces
`FormalSpectrum.locallyRingedSpaceMap I J φ hφ : Spf S ⟶ Spf R` and the affine-formal-scheme
morphism `FormalSpectrum.spfMap`. This file develops the functoriality of `Spf` (EGA I, 10.2),
towards exhibiting it as a (contravariant) functor on adic rings and continuous ring homs.

## Main results

* `levelRingHom_id`/`levelRingHom_comp`: the induced maps of thickenings `R ⧸ Iⁿ⁺¹ → S ⧸ Jⁿ⁺¹`
  respect identity and composition.
* `mapTop_id`/`mapTop_comp`: the underlying continuous maps `Spf S → Spf R` respect identity and
  composition (contravariantly).
* `locallyRingedSpaceMap_congr`: the induced morphism of locally ringed spaces depends only on the
  ring homomorphism, not on the chosen continuity proof.
* `levelSheafHom_id`: the level-`n` map of thickening sheaves induced by the identity is the
  canonical transport `eqToHom` (the identity up to the propositional equality `mapTop_id`).
* `mapSheafHom_id`: the induced map of structure sheaves `O_{Spf R} ⟶ (mapTop id)_* O_{Spf R}` of
  the identity is the canonical transport `eqToHom`.
* `presheafedSpaceMap_id`, `locallyRingedSpaceMap_id`: **the formal spectrum respects the
  identity** — `Spf (id R) = 𝟙 (Spf R)` as a morphism of presheafed / locally ringed spaces.
* `levelSheafHom_comp`, `mapSheafHom_comp`: the level-`n` / structure-sheaf maps respect
  composition, up to the transport along `mapTop_comp`.
* `presheafedSpaceMap_comp`, `locallyRingedSpaceMap_comp`: **the formal spectrum respects
  composition** — `Spf (g ∘ f) = Spf g ≫ Spf f` (contravariantly) as a morphism of presheafed /
  locally ringed spaces.

The equalities `locallyRingedSpaceMap_id`/`_comp` are subtle because the underlying base maps
`mapTop (id)` / `mapTop (g ∘ f)` are only *propositionally* equal to `𝟙` / `mapTop g ≫ mapTop f`
(`mapTop_id`/`mapTop_comp`), so the equalities of the sheaf components carry an
`eqToHom`/`whiskerRight` conjugation — the same conjugation that `FormalSchemes/Thickenings.lean`
(lines 161-186) deliberately sidesteps for the thickening cocone. The load-bearing steps are
`eqToHom_pushforward_limit_square` / `eqToHom_pushforward_comp_limit_square`, which discharge the
`eqToHom`-naturality square between `mapSheafHom_π` and the transport by reducing (via `subst`) to
the case where the base map is literally the identity / a strict composite.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

/-- Whiskering an `eqToHom` natural transformation on the right by a functor is again the
corresponding `eqToHom`. -/
theorem CategoryTheory.Functor.whiskerRight_eqToHom_aux {C D E : Type*} [Category C] [Category D]
    [Category E] {F G : C ⥤ D} (h : F = G) (P : D ⥤ E) :
    Functor.whiskerRight (eqToHom h) P = eqToHom (by rw [h]) := by
  subst h
  simp

/-- Absorbing an `eqToHom` transport of the target open into a `StructureSheaf.comap`. -/
theorem StructureSheaf.comap_ofHom_target_eq {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (U : TopologicalSpace.Opens (PrimeSpectrum.Top A))
    {W₁ W₂ : TopologicalSpace.Opens (PrimeSpectrum.Top B)} (hW : W₁ = W₂)
    (h₁ : W₁.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (e : ((Spec.structureSheaf B).presheaf.obj (op W₁) : CommRingCat) =
        (Spec.structureSheaf B).presheaf.obj (op W₂)) :
    CommRingCat.ofHom (StructureSheaf.comap f U W₁ h₁) ≫ eqToHom e =
      CommRingCat.ofHom (StructureSheaf.comap f U W₂ (hW ▸ h₁)) := by
  subst hW
  exact Category.comp_id _

/-- Composition of two `StructureSheaf.comap`s at the `CommRingCat.ofHom` level. -/
theorem StructureSheaf.ofHom_comap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (U : TopologicalSpace.Opens (PrimeSpectrum.Top A))
    (V : TopologicalSpace.Opens (PrimeSpectrum.Top B))
    (W : TopologicalSpace.Opens (PrimeSpectrum.Top C))
    (hUV : ∀ p ∈ V, PrimeSpectrum.comap f p ∈ U) (hVW : ∀ p ∈ W, PrimeSpectrum.comap g p ∈ V) :
    CommRingCat.ofHom (StructureSheaf.comap f U V hUV) ≫
        CommRingCat.ofHom (StructureSheaf.comap g V W hVW) =
      CommRingCat.ofHom
        (StructureSheaf.comap (g.comp f) U W
          fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) :=
  (CommRingCat.ofHom_comp _ _).symm.trans
    (congrArg CommRingCat.ofHom (StructureSheaf.comap_comp f g U V W hUV hVW).symm)

namespace FormalSpectrum

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable (I : Ideal R) (J : Ideal S) (K : Ideal T)

/-!
### Functoriality of the induced maps of thickenings
-/

section LevelMaps

/-- The map of thickenings induced by the identity is the identity. -/
theorem levelRingHom_id (n : ℕ) :
    levelRingHom I I (RingHom.id R) (Ideal.comap_id I).ge n = RingHom.id (R ⧸ I ^ (n + 1)) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp [levelRingHom_mk]

/-- The map of thickenings induced by a composite is the composite of the induced maps. -/
theorem levelRingHom_comp (φ : R →+* S) (ψ : S →+* T) (hIJ : I ≤ J.comap φ)
    (hJK : J ≤ K.comap ψ) (hIK : I ≤ K.comap (ψ.comp φ)) (n : ℕ) :
    levelRingHom I K (ψ.comp φ) hIK n =
      (levelRingHom J K ψ hJK n).comp (levelRingHom I J φ hIJ n) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp [levelRingHom_mk]

end LevelMaps

/-!
### Functoriality of the underlying continuous maps
-/

section BaseMap

/-- The underlying continuous map induced by the identity is the identity. -/
theorem mapTop_id :
    mapTop I I (RingHom.id R) (Ideal.comap_id I).ge = 𝟙 (TopCat.of (FormalSpectrum I)) := by
  refine TopCat.ext fun x => ?_
  exact congrFun (map_id I) x

/-- The underlying continuous map induced by a composite is the composite (contravariantly) of
the induced maps. -/
theorem mapTop_comp (φ : R →+* S) (ψ : S →+* T) (hIJ : I ≤ J.comap φ) (hJK : J ≤ K.comap ψ)
    (hIK : I ≤ K.comap (ψ.comp φ)) :
    mapTop I K (ψ.comp φ) hIK = mapTop J K ψ hJK ≫ mapTop I J φ hIJ := by
  refine TopCat.ext fun x => ?_
  change map I K (ψ.comp φ) hIK x = map I J φ hIJ (map J K ψ hJK x)
  rw [map_comp I J K φ ψ hIJ hJK hIK]
  rfl

end BaseMap

/-!
### Congruence in the ring homomorphism
-/

section Congr

variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- The induced morphism of locally ringed spaces depends only on the ring homomorphism, not on
the proof of continuity. -/
theorem locallyRingedSpaceMap_congr (φ₁ φ₂ : R →+* S) (h₁ : I ≤ J.comap φ₁)
    (h₂ : I ≤ J.comap φ₂) (hφ : φ₁ = φ₂) :
    locallyRingedSpaceMap I J φ₁ h₁ = locallyRingedSpaceMap I J φ₂ h₂ := by
  subst hφ
  rfl

end Congr

/-!
### Transport lemmas for the identity, towards `locallyRingedSpaceMap_id`

Since `mapTop I I (id) = 𝟙` only *propositionally* (`mapTop_id`), pushing a thickening / structure
sheaf forward along the identity map recovers it, but only up to a transport `eqToHom`. These
lemmas record those transports and identify the level-`n` sheaf map of the identity with the
transport. The one outstanding step for the full `locallyRingedSpaceMap_id : Spf (id) = 𝟙` is the
`eqToHom`-naturality square matching `mapSheafHom_π` at each level against
`structureSheaf_pushforward_mapTop_id` — the same `eqToHom`/`whiskerRight` conjugation flagged in
`FormalSchemes/Thickenings.lean` (lines 161-186).
-/

section IdentityTransport

/-- Pushing forward the `n`-th thickening sheaf along the identity map recovers it. -/
theorem thickeningSheaf_pushforward_mapTop_id (n : ℕ) :
    thickeningSheaf I n =
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).obj
        (thickeningSheaf I n) := by
  rw [mapTop_id]
  rfl

/-- Pushing forward the structure sheaf along the identity map recovers it. -/
theorem structureSheaf_pushforward_mapTop_id :
    structureSheaf I =
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).obj
        (structureSheaf I) := by
  rw [mapTop_id]
  rfl

/-- The level-`n` sheaf map induced by the identity is the canonical transport isomorphism. -/
theorem levelSheafHom_id (n : ℕ) :
    levelSheafHom I I (RingHom.id R) (Ideal.comap_id I).ge n =
      eqToHom (thickeningSheaf_pushforward_mapTop_id I n) := by
  refine InducedCategory.Hom.ext (NatTrans.ext (funext fun U => ?_))
  induction U using Opposite.rec with
  | op V =>
    rw [levelSheafHom_hom_app]
    simp only [levelRingHom_id]
    rw [StructureSheaf.comap_id (show thickeningOpen I n V =
      thickeningOpen I n ((Opens.map (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).obj V)
        by rw [mapTop_id, Opens.map_id_obj])]
    rw [show (eqToHom (thickeningSheaf_pushforward_mapTop_id I n)
          : thickeningSheaf I n ⟶ _).hom =
        eqToHom (congrArg ObjectProperty.FullSubcategory.obj
          (thickeningSheaf_pushforward_mapTop_id I n)) from by
      rw [← ObjectProperty.ι_map]
      exact eqToHom_map _ _]
    rw [eqToHom_app, CommRingCat.ofHom_hom]
    rfl

end IdentityTransport

/-!
### The identity law `Spf (id) = 𝟙`

Assembling the transport lemmas above into the equality of morphisms of locally ringed spaces
`locallyRingedSpaceMap I I (id) = 𝟙 (Spf R)`.
-/

section IdentityLaw

/-- General `eqToHom`/pushforward–limit naturality square, for a self-map `m` of the base equal
to the identity. Reducing to `m = 𝟙` by `subst` makes both transports and the pushforward-map
definitionally trivial. -/
theorem eqToHom_pushforward_limit_square {X : TopCat.{u}}
    (F : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat.{u} X) (m : X ⟶ X) (e : m = 𝟙 X) (n : ℕ)
    (pS : limit F = (TopCat.Sheaf.pushforward CommRingCat.{u} m).obj (limit F))
    (pIn : F.obj ⟨n⟩ = (TopCat.Sheaf.pushforward CommRingCat.{u} m).obj (F.obj ⟨n⟩)) :
    limit.π F ⟨n⟩ ≫ eqToHom pIn =
      eqToHom pS ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} m).map (limit.π F ⟨n⟩) := by
  subst e
  rfl

/-- The map of structure sheaves induced by the identity is the canonical transport `eqToHom`. -/
theorem mapSheafHom_id :
    mapSheafHom I I (RingHom.id R) (Ideal.comap_id I).ge =
      eqToHom (structureSheaf_pushforward_mapTop_id I) := by
  refine (isLimitOfPreserves (TopCat.Sheaf.pushforward CommRingCat
      (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge))
      (limit.isLimit (structureSheafFunctor I))).hom_ext ?_
  intro j
  induction j using Opposite.rec with
  | op n =>
    change mapSheafHom I I (RingHom.id R) (Ideal.comap_id I).ge ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).map
          (limit.π (structureSheafFunctor I) ⟨n⟩) =
      eqToHom (structureSheaf_pushforward_mapTop_id I) ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).map
          (limit.π (structureSheafFunctor I) ⟨n⟩)
    rw [mapSheafHom_π I I (RingHom.id R) (Ideal.comap_id I).ge n, levelSheafHom_id]
    exact eqToHom_pushforward_limit_square (structureSheafFunctor I)
      (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge) (mapTop_id I) n _ _

/-- The presheaf-level component of the identity's structure-sheaf map is the transport
`eqToHom`. -/
theorem mapSheafHom_id_hom :
    (mapSheafHom I I (RingHom.id R) (Ideal.comap_id I).ge).hom =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj
        (structureSheaf_pushforward_mapTop_id I)) := by
  rw [mapSheafHom_id, ← ObjectProperty.ι_map]
  exact eqToHom_map _ _

/-- The underlying morphism of presheafed spaces induced by the identity is the identity. -/
theorem presheafedSpaceMap_id :
    presheafedSpaceMap I I (RingHom.id R) (Ideal.comap_id I).ge =
      𝟙 ((sheafedSpaceObj I).toPresheafedSpace) := by
  refine PresheafedSpace.ext _ _ (mapTop_id I) ?_
  change (mapSheafHom I I (RingHom.id R) (Ideal.comap_id I).ge).hom ≫ _ = 𝟙 _
  rw [mapSheafHom_id_hom, CategoryTheory.Functor.whiskerRight_eqToHom_aux]
  exact eqToHom_trans _ _

/-- **The formal spectrum respects the identity** (EGA I, 10.2): the morphism of locally ringed
spaces induced by the identity ring homomorphism is the identity. -/
theorem locallyRingedSpaceMap_id :
    locallyRingedSpaceMap I I (RingHom.id R) (Ideal.comap_id I).ge =
      𝟙 (locallyRingedSpaceObj I) := by
  apply LocallyRingedSpace.Hom.ext'
  rw [LocallyRingedSpace.id_toHom]
  exact presheafedSpaceMap_id I

end IdentityLaw

/-!
### The composition law `Spf (g ∘ f) = Spf g ≫ Spf f`

Assembling the level-, sheaf-, and presheafed-space maps into the equality of morphisms of locally
ringed spaces `locallyRingedSpaceMap I K (ψ ∘ φ) = locallyRingedSpaceMap J K ψ ≫
locallyRingedSpaceMap I J φ`, the contravariant composition law. The transports arise because
`mapTop I K (ψ ∘ φ) = mapTop J K ψ ≫ mapTop I J φ` only *propositionally* (`mapTop_comp`).
-/

section CompositionLaw

variable (φ : R →+* S) (ψ : S →+* T)
variable (hIJ : I ≤ J.comap φ) (hJK : J ≤ K.comap ψ) (hIK : I ≤ K.comap (ψ.comp φ))

/-- Transport: pushing a thickening sheaf forward along the composite base map. -/
theorem thickeningSheaf_pushforward_mapTop_comp (n : ℕ) :
    (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hIJ)).obj
        ((TopCat.Sheaf.pushforward CommRingCat (mapTop J K ψ hJK)).obj (thickeningSheaf K n)) =
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I K (ψ.comp φ) hIK)).obj
        (thickeningSheaf K n) := by
  rw [mapTop_comp I J K φ ψ hIJ hJK hIK]; rfl

/-- Transport: pushing the structure sheaf forward along the composite base map. -/
theorem structureSheaf_pushforward_mapTop_comp :
    (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hIJ)).obj
        ((TopCat.Sheaf.pushforward CommRingCat (mapTop J K ψ hJK)).obj (structureSheaf K)) =
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I K (ψ.comp φ) hIK)).obj
        (structureSheaf K) := by
  rw [mapTop_comp I J K φ ψ hIJ hJK hIK]; rfl

set_option linter.style.setOption false in
set_option maxHeartbeats 4000000 in
-- Comparing the composite of two `StructureSheaf.comap`s against `comap` of the composite ring
-- homomorphism unfolds the section rings of the structure sheaves, which is slow for the kernel.
theorem levelSheafHom_comp (n : ℕ) :
    levelSheafHom I K (ψ.comp φ) hIK n =
      levelSheafHom I J φ hIJ n ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hIJ)).map
          (levelSheafHom J K ψ hJK n) ≫
        eqToHom (thickeningSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK n) := by
  refine InducedCategory.Hom.ext (NatTrans.ext (funext fun U => ?_))
  induction U using Opposite.rec with
  | op V =>
    have hdist : (levelSheafHom I J φ hIJ n ≫
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hIJ)).map
            (levelSheafHom J K ψ hJK n) ≫
          eqToHom (thickeningSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK n)).hom.app
          (op V) =
        (levelSheafHom I J φ hIJ n).hom.app (op V) ≫
          (levelSheafHom J K ψ hJK n).hom.app (op ((Opens.map (mapTop I J φ hIJ)).obj V)) ≫
          (eqToHom (thickeningSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK n)).hom.app
            (op V) := rfl
    rw [hdist, levelSheafHom_hom_app, levelSheafHom_hom_app, levelSheafHom_hom_app]
    rw [show (eqToHom (thickeningSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK n)).hom =
          eqToHom (congrArg ObjectProperty.FullSubcategory.obj
            (thickeningSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK n)) from by
        rw [← ObjectProperty.ι_map]; exact eqToHom_map _ _]
    rw [eqToHom_app]
    -- the two opens over `Spf T` agree
    have hP : (Opens.map (mapTop J K ψ hJK)).obj ((Opens.map (mapTop I J φ hIJ)).obj V) =
        (Opens.map (mapTop I K (ψ.comp φ) hIK)).obj V := by
      rw [mapTop_comp I J K φ ψ hIJ hJK hIK]; rfl
    -- absorb the transport `eqToHom` into the middle comap, moving its target open to `P3`
    erw [StructureSheaf.comap_ofHom_target_eq (levelRingHom J K ψ hJK n)
      (thickeningOpen J n ((Opens.map (mapTop I J φ hIJ)).obj V))
      (congrArg (thickeningOpen K n) hP)]
    -- combine the two comaps into `comap` of the composite ring hom
    erw [StructureSheaf.ofHom_comap_comp]
    rw [comap_congr (levelRingHom_comp I J K φ ψ hIJ hJK hIK n).symm]

/-- General `eqToHom`/pushforward–limit naturality square for a base map factoring as `g ≫ f`. -/
theorem eqToHom_pushforward_comp_limit_square {X Y Z : TopCat.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (F : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat.{u} X) (m : X ⟶ Z) (e : m = g ≫ f) (n : ℕ)
    (pS : (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} g).obj (limit F)) =
        (TopCat.Sheaf.pushforward CommRingCat.{u} m).obj (limit F))
    (pIn : (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} g).obj (F.obj ⟨n⟩)) =
        (TopCat.Sheaf.pushforward CommRingCat.{u} m).obj (F.obj ⟨n⟩)) :
    (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
        ((TopCat.Sheaf.pushforward CommRingCat.{u} g).map (limit.π F ⟨n⟩)) ≫ eqToHom pIn =
      eqToHom pS ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} m).map (limit.π F ⟨n⟩) := by
  subst e
  rfl

/-- **The map of structure sheaves respects composition** (transported along `mapTop_comp`). -/
theorem mapSheafHom_comp :
    mapSheafHom I K (ψ.comp φ) hIK =
      mapSheafHom I J φ hIJ ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hIJ)).map (mapSheafHom J K ψ hJK) ≫
        eqToHom (structureSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK) := by
  refine (isLimitOfPreserves (TopCat.Sheaf.pushforward CommRingCat (mapTop I K (ψ.comp φ) hIK))
      (limit.isLimit (structureSheafFunctor K))).hom_ext ?_
  intro j
  induction j using Opposite.rec with
  | op n =>
    change mapSheafHom I K (ψ.comp φ) hIK ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I K (ψ.comp φ) hIK)).map
          (limit.π (structureSheafFunctor K) ⟨n⟩) =
      (mapSheafHom I J φ hIJ ≫
          (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hIJ)).map (mapSheafHom J K ψ hJK) ≫
          eqToHom (structureSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK)) ≫
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I K (ψ.comp φ) hIK)).map
          (limit.π (structureSheafFunctor K) ⟨n⟩)
    rw [mapSheafHom_π I K (ψ.comp φ) hIK n, levelSheafHom_comp I J K φ ψ hIJ hJK hIK n,
      Category.assoc, Category.assoc]
    erw [← eqToHom_pushforward_comp_limit_square (mapTop J K ψ hJK) (mapTop I J φ hIJ)
        (structureSheafFunctor K) (mapTop I K (ψ.comp φ) hIK) (mapTop_comp I J K φ ψ hIJ hJK hIK) n
        (structureSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK)
        (thickeningSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK n)]
    erw [← Functor.map_comp_assoc, mapSheafHom_π J K ψ hJK n, Functor.map_comp_assoc]
    rw [reassoc_of% (mapSheafHom_π I J φ hIJ n)]
    exact (Category.assoc _ _ _).symm

/-- The presheaf-level component of the composite's structure-sheaf map. -/
theorem mapSheafHom_comp_hom :
    (mapSheafHom I K (ψ.comp φ) hIK).hom =
      (mapSheafHom I J φ hIJ).hom ≫
        (TopCat.Presheaf.pushforward CommRingCat (mapTop I J φ hIJ)).map
          (mapSheafHom J K ψ hJK).hom ≫
        eqToHom (congrArg ObjectProperty.FullSubcategory.obj
          (structureSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK)) := by
  have hC : (eqToHom (structureSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK)).hom =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj
        (structureSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK)) := by
    rw [← ObjectProperty.ι_map]; exact eqToHom_map _ _
  rw [mapSheafHom_comp]
  show (mapSheafHom I J φ hIJ).hom ≫
      ((TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hIJ)).map (mapSheafHom J K ψ hJK)).hom ≫
      (eqToHom (structureSheaf_pushforward_mapTop_comp I J K φ ψ hIJ hJK hIK)).hom = _
  rw [hC]
  rfl

set_option linter.style.setOption false in
set_option maxHeartbeats 2000000 in
-- Collapsing the `eqToHom`/`whiskerRight` transport across the propositional base-map equality
-- `mapTop_comp` unfolds the section rings of the structure sheaves, which is slow for the kernel.
theorem presheafedSpaceMap_comp :
    presheafedSpaceMap I K (ψ.comp φ) hIK =
      presheafedSpaceMap J K ψ hJK ≫ presheafedSpaceMap I J φ hIJ := by
  refine PresheafedSpace.ext _ _ (mapTop_comp I J K φ ψ hIJ hJK hIK) ?_
  change (mapSheafHom I K (ψ.comp φ) hIK).hom ≫ _ =
    (mapSheafHom I J φ hIJ).hom ≫
      (TopCat.Presheaf.pushforward CommRingCat (mapTop I J φ hIJ)).map (mapSheafHom J K ψ hJK).hom
  rw [mapSheafHom_comp_hom I J K φ ψ hIJ hJK hIK,
    CategoryTheory.Functor.whiskerRight_eqToHom_aux, Category.assoc, Category.assoc]
  erw [eqToHom_trans]
  rw [← Category.assoc]
  exact Category.comp_id _

/-- **The formal spectrum respects composition** (EGA I, 10.2): the morphism of locally ringed
spaces induced by a composite ring homomorphism is the composite (contravariantly) of the induced
morphisms. -/
theorem locallyRingedSpaceMap_comp :
    locallyRingedSpaceMap I K (ψ.comp φ) hIK =
      locallyRingedSpaceMap J K ψ hJK ≫ locallyRingedSpaceMap I J φ hIJ := by
  apply LocallyRingedSpace.Hom.ext'
  rw [LocallyRingedSpace.comp_toHom]
  exact presheafedSpaceMap_comp I J K φ ψ hIJ hJK hIK

end CompositionLaw

end FormalSpectrum
