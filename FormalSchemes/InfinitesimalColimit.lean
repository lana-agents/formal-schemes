import FormalSchemes.Spf

set_option linter.style.header false

/-!
# The formal spectrum as the colimit of its infinitesimal thickenings (EGA I, 10.6.3)

Let `R` be a commutative ring with an ideal of definition `I` for its adic topology. The `n`-th
**infinitesimal thickening** of the formal spectrum `Spf R` is the affine scheme
`Spec (R ⧸ I ^ (n + 1))`. The transition maps of the tower are the closed immersions
`Spec (R ⧸ I ^ (n + 1)) ↪ Spec (R ⧸ I ^ (n + 2))` classified, under `Spec`, by the ring
surjections `R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)` (`FormalSpectrum.stepRingHom`). These assemble
into a diagram

```
Spec (R ⧸ I) ↪ Spec (R ⧸ I ^ 2) ↪ Spec (R ⧸ I ^ 3) ↪ ⋯
```

indexed by the poset `ℕ`, and EGA I, 10.6.3 identifies `Spf R` with its colimit (in the category
of locally ringed spaces, or of formal schemes).

This file constructs the diagram as a functor `ℕ ⥤ LocallyRingedSpace` and records the
**topological content** of 10.6.3: the tower is constant on underlying spaces, all of the
thickenings `Spec (R ⧸ I ^ (n + 1))` being homeomorphic to `Spf R`
(`FormalSpectrum.thickeningHomeomorph`). What varies along the tower is the structure sheaf, and
`Spf R` recovers the inverse limit of the structure sheaves of the thickenings (see
`FormalSchemes/StructureSheaf.lean`).

## Main definitions

* `FormalSpectrum.infThickening I : ℕ ⥤ LocallyRingedSpace`: the tower of infinitesimal
  thickenings of `Spf R`, sending `n` to `Spec (R ⧸ I ^ (n + 1))` and each successor step to the
  closed immersion `Spec.locallyRingedSpaceMap (stepRingHom I n)`.
* `FormalSpectrum.infThickeningHomeomorph I n`: the homeomorphism `Spf R ≃ₜ Spec (R ⧸ I ^ (n + 1))`
  exhibiting the tower as topologically constant.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.3.
* [The Stacks Project, Tag 0AI5](https://stacks.math.columbia.edu/tag/0AI5)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

namespace FormalSpectrum

/-!
### The tower of infinitesimal thickenings
-/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The `n`-th successor step of the tower of infinitesimal thickenings: the closed immersion
`Spec (R ⧸ I ^ (n + 1)) ⟶ Spec (R ⧸ I ^ (n + 2))` obtained by applying `Spec` to the surjection
`R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)` (`stepRingHom I n`). -/
def infThickeningStep (n : ℕ) :
    Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))) :=
  Spec.locallyRingedSpaceMap (stepRingHom I n)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The **tower of infinitesimal thickenings** of `Spf R`, as a functor `ℕ ⥤ LocallyRingedSpace`:
`n` is sent to the affine scheme `Spec (R ⧸ I ^ (n + 1))`, and the successor steps are the closed
immersions `infThickeningStep`. Functoriality (`map_id`, `map_comp`) is automatic, being inherited
from `Spec` and the composition of the quotient factor maps. -/
def infThickening : ℕ ⥤ LocallyRingedSpace :=
  Functor.ofSequence (infThickeningStep I)

omit [TopologicalSpace R] [IsAdicRing I] in
@[simp]
theorem infThickening_obj (n : ℕ) :
    (infThickening I).obj n = Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The map assigned by the tower to a successor step `n ⟶ n + 1` is the closed immersion
`infThickeningStep I n`. -/
@[simp]
theorem infThickening_map_succ (n : ℕ) :
    (infThickening I).map (homOfLE (Nat.le_add_right n 1)) = infThickeningStep I n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-!
### The tower is topologically constant (EGA I, 10.6.3)
-/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Each infinitesimal thickening `Spec (R ⧸ I ^ (n + 1))` is homeomorphic to `Spf R`: nilpotents
do not affect the underlying space, so the tower `infThickening I` is constant on spaces. This is
the topological content of EGA I, 10.6.3. -/
def infThickeningHomeomorph (n : ℕ) : FormalSpectrum I ≃ₜ PrimeSpectrum (R ⧸ I ^ (n + 1)) :=
  thickeningHomeomorph I (n + 1) n.succ_ne_zero

omit [TopologicalSpace R] [IsAdicRing I] in
@[simp]
theorem infThickeningHomeomorph_apply (n : ℕ) (x : FormalSpectrum I) :
    infThickeningHomeomorph I n x = toThickening I (n + 1) n.succ_ne_zero x :=
  rfl

end FormalSpectrum
