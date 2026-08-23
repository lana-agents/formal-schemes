import FormalSchemes.AwayCompletionCongrEquiv

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The comparison maps of completed away localizations fix the base

`FormalSchemes/AwayCompletionCongrEquiv.lean` builds, for two elements `x y : A` that invert each
other's basic opens, the comparison map `awayCongrHom : A{1/x}^ →ₐ[R] A{1/y}^` and — when both
directions are available — the isomorphism `awayCongrEquiv`. This file records the one fact about
them that every consumer needs and that was missing: **they fix the image of `A`**.

That is immediate, because `awayCongrHom` is by definition the completion of
`IsLocalization.Away.lift`, an `A`-compatible localization map, so it is one line from
`furtherLocAlgHom_algebraMap` (`FormalSchemes/CompletedTensorAwayInterchangePullbackLegs.lean`).
It is stated in a new file rather than added to `AwayCompletionCongrEquiv.lean` itself because the
completed-tensor and Tate self-product towers sit above that file, and rebuilding them is the
memory hazard issues 636 and 737 document; the two lemmas are wanted by leaves, which can import
this instead.

Why it matters: a datum whose chart transition fixes the image of `A` has *inert* transitions, and
that is exactly what lets an inverse supplied by one chart be paired against an element read in
another. `FormalSchemes/ThreeChartCoverSeparated.lean` (issue 779) turns on it; a datum whose
transition is a genuine automorphism, like the Tate model's, does not have it.

## Main results

* `CompletedTensorAwayInterchange.awayCongrHom_algebraMap`
* `CompletedTensorAwayInterchange.awayCongrEquiv_algebraMap`

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.15.
-/

noncomputable section

open FormalSpectrum

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The comparison map `A{1/x} →ₐ[R] A{1/y}` fixes the image of `A`** — it is the completion of
an `A`-compatible localization map. -/
theorem awayCongrHom_algebraMap (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x)) (a : A) :
    awayCongrHom I x y hI hxy (algebraMap A (awayCompletion (I.map (algebraMap R A)) x) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) y) a :=
  furtherLocAlgHom_algebraMap I x y hI _ _ a

/-- **The comparison isomorphism fixes the image of `A`.** -/
theorem awayCongrEquiv_algebraMap (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyx : IsUnit (algebraMap A (Localization.Away x) y)) (a : A) :
    awayCongrEquiv I x y hI hxy hyx
        (algebraMap A (awayCompletion (I.map (algebraMap R A)) x) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) y) a :=
  awayCongrHom_algebraMap I x y hI hxy a

end CompletedTensorAwayInterchange

end
