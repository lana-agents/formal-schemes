import FormalSchemes.GlueDataCompact
import FormalSchemes.TateGlueTwoPatch

set_option linter.style.header false

/-!
# The glued formal Tate annulus is quasi-compact

`FormalSchemes/TateGlueTwoPatch.lean` glues two copies of the formal Tate annulus `Spf A` along the
overlap `{x invertible} ≅ {y invertible}` into `tateTwoPatch`, the `J = Bool` slice of the Tate
chain. Both patches are affine formal schemes, hence quasi-compact, and there are two of them, so
`FormalScheme.GlueData.compactSpace` (`FormalSchemes/GlueDataCompact.lean`) applies.

## Why this file exists

The lemma it consumes is general, and a general lemma with a single consumer inside its own subtree
is indistinguishable from one that should have stayed private to that subtree. `tateTwoPatch` and
the glued formal completion of `FormalSchemes/CompletionCompact.lean` sit on branches of this
development that do not import one another, so between them they are the reason
`FormalScheme.GlueData.compactSpace` lives directly above `FormalSchemes/Gluing.lean` rather than
inside either consumer.

The result is also wanted on its own account: quasi-compactness of the Tate formal model is a
hypothesis the finiteness and separation theory of EGA I §10.12–10.15 takes for granted.

## Main results

* `AlgebraicGeometry.tateTwoPatch_compactSpace`: the glued two-patch formal Tate annulus is
  quasi-compact.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The glued two-patch formal Tate annulus is quasi-compact.** Both patches are the affine
formal scheme `Spf A` — `tateTwoPatchFormalGlueData` presents them by the same object — so a single
`rintro _` discharges the per-patch hypothesis with no case split. -/
instance tateTwoPatch_compactSpace (hI : I.FG) [IsNoetherianRing R] :
    CompactSpace (tateTwoPatch R I q hI).toLocallyRingedSpace :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : Finite (tateTwoPatchFormalGlueData R I q hI).toLocallyRingedSpaceGlueData.J :=
    inferInstanceAs (Finite (ULift.{u} Bool))
  FormalScheme.GlueData.compactSpace _ (by
    rintro _
    exact inferInstanceAs (CompactSpace (FormalSpectrum (annulusIdealOfDefinition R I q))))

end AlgebraicGeometry
