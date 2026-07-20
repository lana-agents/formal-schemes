import FormalSchemes.StructureSheaf
import Mathlib.AlgebraicGeometry.StructureSheaf

set_option linter.style.header false

/-!
# Basic opens of the formal spectrum and their level-`n` sections

For an element `f : R` of an adic ring with ideal of definition `I`, the **basic open** `D(f)` of
the formal spectrum `Spf R = FormalSpectrum I` is the basic open `PrimeSpectrum.basicOpen` of the
image of `f` in `R ⧸ I`. Since `Spf R` is homeomorphic, via `FormalSpectrum.thickeningTopIso`, to
each infinitesimal thickening `Spec (R ⧸ I ^ (n + 1))`, the open `D(f)` corresponds to the basic
open `D(mk (I ^ (n + 1)) f)` of that thickening (`FormalSpectrum.map_inv_basicOpen`). Consequently
the sections of the `n`-th thickening sheaf over `D(f)` are, by
`AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`, a localization of `R ⧸ I ^ (n + 1)`
away from `mk (I ^ (n + 1)) f`, hence canonically isomorphic to
`Localization.Away (mk (I ^ (n + 1)) f)` (`FormalSpectrum.thickeningSectionBasicOpenEquiv`).

This is the level-`n` input to the identification of `Γ(D(f), O_{Spf R})` with the `I`-adic
completion of the localization `R_f` (EGA I 10.5.6ff / Stacks Tag 0AI7).

## Main definitions

* `FormalSpectrum.basicOpen I f`: the basic open `D(f)` of `Spf R`, an `Opens (FormalSpectrum I)`.
* `FormalSpectrum.thickeningSectionBasicOpenEquiv I f n`: the ring isomorphism
  `Γ(D(f), thickeningSheaf I n) ≃+* Localization.Away (mk (I ^ (n + 1)) f)`.

## Main results

* `FormalSpectrum.map_thickeningTopIso_hom_basicOpen`: `D(mk (I ^ (n + 1)) f)` pulls back along
  `(thickeningTopIso I n).hom` to `D(f)`.
* `FormalSpectrum.map_inv_basicOpen`: `D(f)` pulls back along `(thickeningTopIso I n).inv` to
  `D(mk (I ^ (n + 1)) f)`, so `Γ(D(f), thickeningSheaf I n)` unfolds to
  `Γ(D(mk (I ^ (n + 1)) f), structureSheaf (R ⧸ I ^ (n + 1)))`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §10.5.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

variable {R : Type*} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I] (f : R)

namespace FormalSpectrum

/-- The **basic open** `D(f)` of the formal spectrum `Spf R = FormalSpectrum I`, i.e. the basic
open of the image of `f` in `R ⧸ I`. Recall `FormalSpectrum I := PrimeSpectrum (R ⧸ I)`. -/
def basicOpen : Opens (FormalSpectrum I) :=
  PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f)

omit [TopologicalSpace R] [IsAdicRing I] in
@[simp]
theorem mem_basicOpen (x : FormalSpectrum I) :
    x ∈ basicOpen I f ↔ Ideal.Quotient.mk I f ∉ x.asIdeal :=
  PrimeSpectrum.mem_basicOpen _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Under the homeomorphism `(thickeningTopIso I n).hom` identifying `Spf R` with its `n`-th
thickening `Spec (R ⧸ I ^ (n + 1))`, the basic open `D(mk (I ^ (n + 1)) f)` of the thickening
pulls back to the basic open `D(f)` of `Spf R`. -/
theorem map_thickeningTopIso_hom_basicOpen (n : ℕ) :
    (Opens.map (thickeningTopIso I n).hom).obj
        (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) f))
      = basicOpen I f := by
  rw [basicOpen,
    ← Ideal.Quotient.factor_mk (Ideal.pow_le_self n.succ_ne_zero : I ^ (n + 1) ≤ I) f]
  exact PrimeSpectrum.comap_basicOpen _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Under the homeomorphism `(thickeningTopIso I n).inv`, the basic open `D(f)` of `Spf R` pulls
back to the basic open `D(mk (I ^ (n + 1)) f)` of the `n`-th thickening
`Spec (R ⧸ I ^ (n + 1))`. Equivalently, the sections of `thickeningSheaf I n` over `D(f)` are the
sections of the structure sheaf of `Spec (R ⧸ I ^ (n + 1))` over `D(mk (I ^ (n + 1)) f)`. -/
theorem map_inv_basicOpen (n : ℕ) :
    (Opens.map (thickeningTopIso I n).inv).obj (basicOpen I f)
      = PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) f) := by
  rw [← map_thickeningTopIso_hom_basicOpen I f n, ← Opens.map_comp_obj,
    Iso.inv_hom_id, Opens.map_id_obj]

/-- The ring of sections of the `n`-th thickening sheaf over the basic open `D(f)` is canonically
isomorphic to `Localization.Away (mk (I ^ (n + 1)) f)`, the localization of `R ⧸ I ^ (n + 1)` away
from the image of `f`.

Indeed, transporting along `map_inv_basicOpen` identifies these sections with the sections of the
structure sheaf of `Spec (R ⧸ I ^ (n + 1))` over `D(mk (I ^ (n + 1)) f)`, which is a localization
away from `mk (I ^ (n + 1)) f` by
`AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`; uniqueness of localizations
(`IsLocalization.algEquiv`) then gives the isomorphism to `Localization.Away`. -/
def thickeningSectionBasicOpenEquiv (n : ℕ) :
    (thickeningSheaf I n).presheaf.obj (op (basicOpen I f)) ≃+*
      Localization.Away (Ideal.Quotient.mk (I ^ (n + 1)) f) :=
  (((Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf.mapIso
        (eqToIso (congrArg op (map_inv_basicOpen I f n)))).commRingCatIsoToRingEquiv).trans
    (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (I ^ (n + 1)) f))
      ((Spec.structureSheaf (R ⧸ I ^ (n + 1))).obj.obj
        (op (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) f))))
      (Localization.Away (Ideal.Quotient.mk (I ^ (n + 1)) f))).toRingEquiv

end FormalSpectrum
