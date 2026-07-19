import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

set_option linter.style.header false

/-!
# Localization away from `f` commutes with quotient by an ideal

For a commutative ring `R`, an element `f : R`, and an ideal `K : Ideal R`, localizing the quotient
`R ⧸ K` away from the image of `f` is the same as quotienting the localization `Localization.Away f`
by the extension of `K`. Concretely, writing `A = Localization.Away f`, the natural map
`R ⧸ K → A ⧸ K·A` exhibits `A ⧸ K·A` as a localization of `R ⧸ K` away from `Ideal.Quotient.mk K f`.

This is a purely commutative-algebra statement (localization commutes with quotients). It is the
crux of identifying the sections of the structure sheaf of a formal spectrum on a basic open
`D(f)` with an adic completion of a localization: applied level by level with `K = I ^ (n + 1)`
(and `Ideal.map_pow`), it turns the tower `n ↦ Localization.Away (Ideal.Quotient.mk (I ^ (n+1)) f)`
into the tower `n ↦ A ⧸ (I·A) ^ (n + 1)` defining `AdicCompletion (I·A) A`.

## Main results

* `IsLocalization.away_quotient`: `A ⧸ K.map (algebraMap R A)` is a localization of `R ⧸ K` away
  from `Ideal.Quotient.mk K f`, where `A = Localization.Away f`.
* `Localization.awayQuotientEquiv`: the resulting ring isomorphism
  `Localization.Away (Ideal.Quotient.mk K f) ≃+* A ⧸ K.map (algebraMap R A)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §10.5.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

namespace IsLocalization

variable {R : Type*} [CommRing R] (f : R) (K : Ideal R)

/-- Localizing `R` away from `f` and then quotienting by the extension of `K` yields a localization
of `R ⧸ K` away from the image `Ideal.Quotient.mk K f`: localization commutes with quotients.

This specializes the general fact that, for `IsLocalization M S`, the quotient
`S ⧸ K.map (algebraMap R S)` is a localization of `R ⧸ K` at the image of `M`
(`IsLocalization.of_surjective`), to the
case `M = Submonoid.powers f`, using that the image of `Submonoid.powers f` in `R ⧸ K` is
`Submonoid.powers (Ideal.Quotient.mk K f)`. -/
instance away_quotient :
    IsLocalization.Away (Ideal.Quotient.mk K f)
      (Localization.Away f ⧸ K.map (algebraMap R (Localization.Away f))) := by
  have h : Algebra.algebraMapSubmonoid (R ⧸ K) (Submonoid.powers f)
      = Submonoid.powers (Ideal.Quotient.mk K f) := by
    change (Submonoid.powers f).map (algebraMap R (R ⧸ K))
      = Submonoid.powers (Ideal.Quotient.mk K f)
    rw [Submonoid.map_powers, Ideal.Quotient.algebraMap_eq]
  change IsLocalization (Submonoid.powers (Ideal.Quotient.mk K f)) _
  rw [← h]
  infer_instance

end IsLocalization

namespace Localization

variable {R : Type*} [CommRing R] (f : R) (K : Ideal R)

/-- **Localization commutes with quotient (away version).** The localization of `R ⧸ K` away from
`Ideal.Quotient.mk K f` is isomorphic, as a ring, to the quotient of `Localization.Away f` by the
extension of `K`. Both are localizations of `R ⧸ K` at `Submonoid.powers (Ideal.Quotient.mk K f)`
(see `IsLocalization.away_quotient`), so they are canonically isomorphic by uniqueness of
localizations. -/
noncomputable def awayQuotientEquiv :
    Localization.Away (Ideal.Quotient.mk K f) ≃+*
      Localization.Away f ⧸ K.map (algebraMap R (Localization.Away f)) :=
  (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk K f))
    (Localization.Away (Ideal.Quotient.mk K f))
    (Localization.Away f ⧸ K.map (algebraMap R (Localization.Away f)))).toRingEquiv

/-- `Localization.awayQuotientEquiv` is an `R ⧸ K`-algebra map: it sends the image of `x : R ⧸ K`
in `Localization.Away (Ideal.Quotient.mk K f)` to its image in `Localization.Away f ⧸ K·A`. This is
the naturality input needed downstream (e.g. to identify the tower of quotients level by level). -/
@[simp]
theorem awayQuotientEquiv_algebraMap (x : R ⧸ K) :
    awayQuotientEquiv f K (algebraMap (R ⧸ K) (Localization.Away (Ideal.Quotient.mk K f)) x)
      = algebraMap (R ⧸ K) (Localization.Away f ⧸ K.map (algebraMap R (Localization.Away f))) x :=
  (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk K f)) _ _).commutes x

end Localization
