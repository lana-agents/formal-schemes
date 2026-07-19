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

open CategoryTheory AlgebraicGeometry

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

omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000 in
-- Checking that `hom` has the stated type requires unfolding `SheafedSpace.sheaf` and the
-- `TopCat.Sheaf`/`TopCat.Presheaf` pushforward functors against each other, which is slow.
/-- The transition map `thickeningSheaf I (n + 1) ⟶ thickeningSheaf I n` of the inverse system,
induced by the closed immersion of thickenings classified by `stepRingHom`. -/
def stepSheafHom (n : ℕ) : thickeningSheaf I (n + 1) ⟶ thickeningSheaf I n :=
  have hom :
      (Spec.sheafedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))).sheaf.obj ⟶
        ((TopCat.Sheaf.pushforward CommRingCat (Spec.topMap (stepRingHom I n))).obj
          (Spec.sheafedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).sheaf).obj :=
    (Spec.sheafedSpaceMap (stepRingHom I n)).hom.c
  (TopCat.Sheaf.pushforward CommRingCat (thickeningTopIso I (n + 1)).inv).map
      (ObjectProperty.homMk hom) ≫
    eqToHom (congrArg
      (fun f => (TopCat.Sheaf.pushforward CommRingCat f).obj
        (Spec.sheafedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).sheaf)
      (topMap_stepRingHom_comp_inv I n))

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
