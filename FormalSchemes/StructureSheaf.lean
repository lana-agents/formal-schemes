import FormalSchemes.FormalSpectrum
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Functor.OfSequence

set_option linter.style.header false

/-!
# The structure sheaf of the formal spectrum

Given an adic ring `R` with ideal of definition `I` (see `IsAdicRing`), the **structure sheaf**
`O_{Spf R}` of its formal spectrum `Spf R = FormalSpectrum I` (see
`FormalSchemes/FormalSpectrum.lean`) is defined as the inverse limit, over `n ≥ 1`, of the
structure sheaves of the infinitesimal thickenings `Spec (R ⧸ I ^ n)`, transported to `Spf R`
along the homeomorphisms `FormalSpectrum.thickeningHomeomorph`. This file constructs `O_{Spf R}`
as such a limit of sheaves of commutative rings on `TopCat.of (FormalSpectrum I)`.

We reindex by `n : ℕ` standing for the exponent `n + 1`, so that the `n ≠ 0` side condition of
`thickeningHomeomorph` disappears, and work throughout with `R ⧸ I ^ (n + 1)`.

## Main definitions

* `FormalSpectrum.thickeningTopIso I n`: the isomorphism, in `TopCat`, between `TopCat.of
  (FormalSpectrum I)` and the topological space `Spec.topObj (R ⧸ I ^ (n + 1))` underlying the
  `n`-th infinitesimal thickening, induced by `FormalSpectrum.thickeningHomeomorph`.
* `FormalSpectrum.thickeningSheaf I n`: the structure sheaf of the `n`-th thickening
  `Spec (R ⧸ I ^ (n + 1))`, transported to `TopCat.of (FormalSpectrum I)` along
  `thickeningTopIso`, as a sheaf of `CommRingCat`.
* `FormalSpectrum.structureSheafFunctor I : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat (TopCat.of
  (FormalSpectrum I))`: the inverse system of the `thickeningSheaf`, with transition maps induced
  by the ring surjections `Ideal.Quotient.factor : R ⧸ I ^ (n + 1) →+* R ⧸ I ^ m` classifying the
  closed immersions of the thickenings into one another.
* `FormalSpectrum.structureSheaf I`: the structure sheaf `O_{Spf R}` of `Spf R`, defined as the
  limit of `structureSheafFunctor`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §10.5.
* [The Stacks Project, Tag 0AI5](https://stacks.math.columbia.edu/tag/0AI5)
* [The Stacks Project, Tag 0AI6](https://stacks.math.columbia.edu/tag/0AI6)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

variable {R : Type*} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

namespace FormalSpectrum

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `Spf R` is homeomorphic, as an object of `TopCat`, to the topological space underlying the
`n`-th infinitesimal thickening `Spec (R ⧸ I ^ (n + 1))`. -/
def thickeningTopIso (n : ℕ) :
    TopCat.of (FormalSpectrum I) ≅ Spec.topObj (CommRingCat.of (R ⧸ I ^ (n + 1))) :=
  TopCat.isoOfHomeo (thickeningHomeomorph I (n + 1) n.succ_ne_zero)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The structure sheaf of the `n`-th infinitesimal thickening `Spec (R ⧸ I ^ (n + 1))`,
transported to `Spf R` along `thickeningTopIso`. -/
def thickeningSheaf (n : ℕ) : TopCat.Sheaf CommRingCat (TopCat.of (FormalSpectrum I)) :=
  (TopCat.Sheaf.pushforward CommRingCat (thickeningTopIso I n).inv).obj
    (Spec.sheafedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).sheaf

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The ring surjection `R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)` classifying the closed immersion of
the `n`-th thickening into the `(n + 1)`-th one. -/
def stepRingHom (n : ℕ) :
    CommRingCat.of (R ⧸ I ^ (n + 1 + 1)) ⟶ CommRingCat.of (R ⧸ I ^ (n + 1)) :=
  CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The triangle of maps out of `Spf R` into the thickenings `Spec (R ⧸ I ^ (n + 1))` and
`Spec (R ⧸ I ^ (n + 2))` commutes with the transition map `Spec.topMap (stepRingHom I n)` of the
tower of thickenings. -/
theorem thickeningTopIso_hom_comp_topMap_stepRingHom (n : ℕ) :
    (thickeningTopIso I n).hom ≫ Spec.topMap (stepRingHom I n) =
      (thickeningTopIso I (n + 1)).hom := by
  ext x
  exact congrFun (comap_factor_comp_toThickening I (Nat.succ_ne_zero n)
    (Nat.succ_ne_zero (n + 1)) (Nat.le_succ (n + 1))) x

omit [TopologicalSpace R] [IsAdicRing I] in
theorem topMap_stepRingHom_comp_inv (n : ℕ) :
    Spec.topMap (stepRingHom I n) ≫ (thickeningTopIso I (n + 1)).inv =
      (thickeningTopIso I n).inv := by
  rw [Iso.comp_inv_eq, ← thickeningTopIso_hom_comp_topMap_stepRingHom I n,
    Iso.inv_hom_id_assoc]

/-!
### Sections of the thickening sheaves, and the transition maps of the tower

The `n`-th thickening sheaf on `Spf R` is the pushforward of the structure sheaf of
`Spec (R ⧸ I ^ (n + 1))` along a homeomorphism, so its ring of sections over an open `U ⊆ Spf R`
is *definitionally* the ring of sections of `O_{Spec (R ⧸ I ^ (n + 1))}` over the corresponding
open `thickeningOpen I n U` (`thickeningSheaf_obj`). This lets us define the transition map
`stepSheafHom` of the tower open-by-open as the map `StructureSheaf.comap` on sections induced
by the surjection `R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)` (so the computation rule
`stepSheafHom_hom_app` holds by definition). These identifications drive all section- and
stalk-level computations on `Spf R`.
-/

section Sections

omit [TopologicalSpace R] [IsAdicRing I]

variable (n : ℕ) (U : TopologicalSpace.Opens (FormalSpectrum I))

open TopologicalSpace in
/-- The open subset of the `n`-th infinitesimal thickening `Spec (R ⧸ I ^ (n + 1))`
corresponding to an open subset `U ⊆ Spf R` under the thickening homeomorphism. -/
def thickeningOpen : Opens (PrimeSpectrum (R ⧸ I ^ (n + 1))) :=
  (Opens.map (thickeningTopIso I n).inv).obj U

@[simp]
theorem thickeningOpen_top : thickeningOpen I n ⊤ = ⊤ :=
  rfl

/-- The sections of the `n`-th thickening sheaf over `U ⊆ Spf R` are, definitionally, the
sections of the structure sheaf of the `n`-th thickening over `thickeningOpen I n U`. -/
theorem thickeningSheaf_obj :
    (thickeningSheaf I n).presheaf.obj (op U) =
      (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf.obj (op (thickeningOpen I n U)) :=
  rfl

/-- The transition maps `Spec (R ⧸ I ^ (n + 1)) → Spec (R ⧸ I ^ (n + 2))` of the tower of
thickenings match up the opens `thickeningOpen` corresponding to a fixed open of `Spf R`. -/
theorem map_topMap_thickeningOpen :
    (TopologicalSpace.Opens.map (Spec.topMap (stepRingHom I n))).obj
        (thickeningOpen I (n + 1) U) =
      thickeningOpen I n U := by
  have h : (TopologicalSpace.Opens.map
        (Spec.topMap (stepRingHom I n) ≫ (thickeningTopIso I (n + 1)).inv)).obj U =
      thickeningOpen I n U := by
    rw [topMap_stepRingHom_comp_inv]
    rfl
  exact h

theorem thickeningOpen_le_comap :
    (thickeningOpen I n U : Set (PrimeSpectrum (R ⧸ I ^ (n + 1)))) ⊆
      PrimeSpectrum.comap (stepRingHom I n).hom ⁻¹'
        (thickeningOpen I (n + 1) U : Set (PrimeSpectrum (R ⧸ I ^ (n + 2)))) := by
  rw [← map_topMap_thickeningOpen I n U]
  exact fun x hx => hx

/-- Under the thickening homeomorphism, the basic open `D(f) ⊆ Spf R` corresponds to the basic
open `D(f mod I ^ (n + 1))` of the `n`-th thickening `Spec (R ⧸ I ^ (n + 1))`. -/
theorem thickeningOpen_basicOpen (f : R) :
    thickeningOpen I n (basicOpen I f) =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) f) := by
  apply TopologicalSpace.Opens.ext
  change ⇑(thickeningTopIso I n).inv ⁻¹' (basicOpen I f : Set (FormalSpectrum I)) = _
  rw [← toThickening_preimage_basicOpen I (n + 1) n.succ_ne_zero f, ← Set.preimage_comp]
  have h : toThickening I (n + 1) n.succ_ne_zero ∘ ⇑(thickeningTopIso I n).inv = id := by
    funext y
    exact (thickeningHomeomorph I (n + 1) n.succ_ne_zero).apply_symm_apply y
  rw [h]
  rfl

/-- The ring of sections of the `n`-th thickening sheaf over an open of `Spf R` is an algebra
over the ring `R ⧸ I ^ (n + 1)` of the thickening. -/
instance thickeningSectionsAlgebra :
    Algebra (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U)) :=
  inferInstanceAs (Algebra (R ⧸ I ^ (n + 1))
    ((Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf.obj (op (thickeningOpen I n U))))

/-- The sections of the `n`-th thickening sheaf over the basic open `D(f) ⊆ Spf R` are the
localization of `R ⧸ I ^ (n + 1)` away from `f mod I ^ (n + 1)` (EGA I, 10.1.4). -/
instance isLocalization_away_basicOpen_sections (f : R) :
    IsLocalization.Away (Ideal.Quotient.mk (I ^ (n + 1)) f)
      ((thickeningSheaf I n).presheaf.obj (op (basicOpen I f))) := by
  change IsLocalization.Away (Ideal.Quotient.mk (I ^ (n + 1)) f)
    ((Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf.obj
      (op (thickeningOpen I n (basicOpen I f))))
  rw [thickeningOpen_basicOpen]
  exact StructureSheaf.IsLocalization.to_basicOpen _ _

/-- The identification of the sections of the `n`-th thickening sheaf over `D(f) ⊆ Spf R` with
the localization `(R ⧸ I ^ (n + 1))_f`, as a ring isomorphism. -/
noncomputable def basicOpenSectionsEquiv (f : R) :
    ((thickeningSheaf I n).presheaf.obj (op (basicOpen I f))) ≃+*
      Localization.Away (Ideal.Quotient.mk (I ^ (n + 1)) f) :=
  (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (I ^ (n + 1)) f)) _ _).toRingEquiv

/-- `StructureSheaf.comap` is compatible with the restriction maps of the structure sheaves:
the square

```
Γ(U₁, O_Spec A) → Γ(U₂, O_Spec B)
      ↓                  ↓
Γ(V₁, O_Spec A) → Γ(V₂, O_Spec B)
```

of comaps and restrictions commutes. -/
theorem comap_comp_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {U₁ V₁ : TopologicalSpace.Opens (PrimeSpectrum.Top A)} (i₁ : V₁ ⟶ U₁)
    {U₂ V₂ : TopologicalSpace.Opens (PrimeSpectrum.Top B)} (i₂ : V₂ ⟶ U₂)
    (hU : U₂.1 ⊆ PrimeSpectrum.comap φ ⁻¹' U₁.1)
    (hV : V₂.1 ⊆ PrimeSpectrum.comap φ ⁻¹' V₁.1) :
    (StructureSheaf.comap φ V₁ V₂ hV).comp
        ((Spec.structureSheaf A).presheaf.map i₁.op).hom =
      ((Spec.structureSheaf B).presheaf.map i₂.op).hom.comp
        (StructureSheaf.comap φ U₁ U₂ hU) := by
  refine RingHom.ext fun s => Subtype.ext (funext fun p => ?_)
  change (StructureSheaf.comap φ V₁ V₂ hV
        (((Spec.structureSheaf A).presheaf.map i₁.op).hom s)).1 p =
      (StructureSheaf.comap φ U₁ U₂ hU s).1 (i₂ p)
  rw [StructureSheaf.comap_apply, StructureSheaf.comap_apply]
  rfl

/-- The transition map `thickeningSheaf I (n + 1) ⟶ thickeningSheaf I n` of the inverse system,
induced by the closed immersion of thickenings classified by `stepRingHom`. Over each open
`U ⊆ Spf R` it is the map on sections `StructureSheaf.comap` induced by the surjection
`R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)`. -/
def stepSheafHom : thickeningSheaf I (n + 1) ⟶ thickeningSheaf I n :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        (StructureSheaf.comap (stepRingHom I n).hom
          (thickeningOpen I (n + 1) U.unop) (thickeningOpen I n U.unop)
          (thickeningOpen_le_comap I n U.unop))
      naturality := fun U V i => by
        apply CommRingCat.hom_ext
        rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
        exact comap_comp_map (stepRingHom I n).hom
          ((TopologicalSpace.Opens.map (thickeningTopIso I (n + 1)).inv).map i.unop)
          ((TopologicalSpace.Opens.map (thickeningTopIso I n).inv).map i.unop)
          (thickeningOpen_le_comap I n U.unop) (thickeningOpen_le_comap I n V.unop) }

/-- Computation rule for `stepSheafHom`: over an open `U ⊆ Spf R` it is the map on sections
`StructureSheaf.comap` induced by the surjection `R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)` between
the structure sheaves of the thickenings. True by definition. -/
theorem stepSheafHom_hom_app :
    (stepSheafHom I n).hom.app (op U) =
      CommRingCat.ofHom (StructureSheaf.comap (stepRingHom I n).hom
        (thickeningOpen I (n + 1) U) (thickeningOpen I n U)
        (thickeningOpen_le_comap I n U)) :=
  rfl

end Sections

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The inverse system of structure sheaves of the thickenings of `Spf R`, whose limit defines
`O_{Spf R}`. -/
def structureSheafFunctor : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat (TopCat.of (FormalSpectrum I)) :=
  Functor.ofOpSequence (stepSheafHom I)

/-- The **structure sheaf** `O_{Spf R}` of the formal spectrum `Spf R` of an adic ring `R` with
ideal of definition `I`, defined as the inverse limit of the structure sheaves of the
infinitesimal thickenings `Spec (R ⧸ I ^ n)`. -/
def structureSheaf : TopCat.Sheaf CommRingCat (TopCat.of (FormalSpectrum I)) :=
  CategoryTheory.Limits.limit (structureSheafFunctor I)

end FormalSpectrum
