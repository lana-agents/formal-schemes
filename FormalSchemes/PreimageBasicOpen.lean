import FormalSchemes.GlobalSectionsHom
import FormalSchemes.TwoChartBasicOpen

set_option linter.style.header false

/-!
# The preimage of a basic open along a morphism into a formal spectrum

Let `f : X ⟶ Spf (R, I)` be a morphism from an **arbitrary** locally ringed space. Then for every
`g : R`

> `f⁻¹ D(g)` is the locus where the germ of the global section `FormalSpectrum.globalSectionsHom`
> sends `g` to is invertible

(`FormalSpectrum.preimage_basicOpen_eq`, as an equality of opens, and
`FormalSpectrum.mem_preimage_basicOpen_iff`, pointwise). Neither side mentions a chart, an affine
cover or a choice: the right-hand side is `AlgebraicGeometry.RingedSpace.basicOpen` of a global
section of `X`, and the section is the image of `g` under the ring homomorphism
`R →+* Γ(X, 𝒪_X)` that `f` induces.

## Why this file exists, and why it is this low

Both halves were on the tree already and had never been put together.

* `FormalSpectrum.ringedSpaceBasicOpen_symm_eq` (`FormalSchemes.TwoChartBasicOpen`) identifies
  `FormalSpectrum.basicOpen I g`, defined combinatorially, with the `RingedSpace` basic open of
  the corresponding global section. That file's own docstring says the identification exists to
  reach "the form Mathlib's `AlgebraicGeometry.LocallyRingedSpace.preimage_basicOpen` speaks
  about" — and that Mathlib lemma is the other half.
* `FormalSpectrum.globalSectionsHom` (`FormalSchemes.GlobalSectionsHom`) is the induced
  `R →+* Γ(X, 𝒪_X)` **for an arbitrary source**.

The affine-source form is `FormalSpectrum.base_preimage_basicOpen`
(`FormalSchemes.SpfGammaSheafComponentArb`): for `f : Spf S ⟶ Spf R` it says `f⁻¹ D(g) = D(φ g)`,
with `φ` the map on rings. That is a different statement — its source is a formal spectrum and its
right-hand side is another `FormalSpectrum.basicOpen`, and neither is available here — so this is
not a duplicate of it and it is not re-derived from this one: `FormalSchemes.TwoChartBasicOpen` and
`FormalSchemes.SpfGammaSheafComponentArb` are **mutually unreachable** (neither is in the other's
import closure, checked both ways), so a dedup would cost an import in one direction or the other.

`FormalSchemes.TwoChartBasicOpen` (fwd 31) and `FormalSchemes.GlobalSectionsHom` (fwd 41) are
likewise mutually unreachable, so neither can host a statement mentioning both without gaining an
import; this file over the two has forward closure **44**, and reverse closure **5**, all five of
them in the Tate node-chart cluster.

## Main results

* `FormalSpectrum.preimage_basicOpen_eq`: `f⁻¹ D(g) = X.basicOpen (globalSectionsHom I X f g)`.
* `FormalSpectrum.mem_preimage_basicOpen_iff`: the same, read at a point, as invertibility of a
  germ.

## What the membership form costs

`AlgebraicGeometry.RingedSpace.basicOpen` is a `TopologicalSpace.Opens`, so the equality composes
with `TopologicalSpace.Opens.map` and can be substituted for the preimage wherever one appears.
But membership in it is *invertibility of a germ*
(`AlgebraicGeometry.RingedSpace.mem_basicOpen`), not a combinatorial condition on a prime: a
consumer that wants to decide whether a given point lies in `f⁻¹ D(g)` still has to decide a
germ. That is why both forms are stated.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.4.
* `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean` —
  `AlgebraicGeometry.LocallyRingedSpace.preimage_basicOpen`, the scheme-theoretic template.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- **The preimage of a basic open is the non-vanishing locus of a global section.** For a
morphism `f : X ⟶ Spf (R, I)` out of an arbitrary locally ringed space and `g : R`, the open
`f⁻¹ D(g)` is `AlgebraicGeometry.RingedSpace.basicOpen` of the global section of `X` that
`FormalSpectrum.globalSectionsHom` attaches to `g`.

`FormalSpectrum.ringedSpaceBasicOpen_symm_eq` rewrites `D(g)` as a `RingedSpace` basic open, and
`AlgebraicGeometry.LocallyRingedSpace.preimage_basicOpen` pulls it back; the closing `rfl`
identifies the pulled-back section with `globalSectionsHom I X f g`, which is what that
homomorphism is defined to be. -/
theorem preimage_basicOpen_eq (X : LocallyRingedSpace.{u})
    (f : X ⟶ locallyRingedSpaceObj I) (g : R) :
    (Opens.map f.base).obj (basicOpen I g) =
      X.toRingedSpace.basicOpen (globalSectionsHom I X f g) := by
  rw [← ringedSpaceBasicOpen_symm_eq I g, LocallyRingedSpace.preimage_basicOpen]
  rfl

/-- **The pointwise form.** `f x` lies in `D(g)` exactly when the germ at `x` of the global section
attached to `g` is a unit. `FormalSpectrum.preimage_basicOpen_eq` and
`AlgebraicGeometry.RingedSpace.mem_basicOpen` at `U = ⊤`. -/
theorem mem_preimage_basicOpen_iff (X : LocallyRingedSpace.{u})
    (f : X ⟶ locallyRingedSpaceObj I) (g : R) (x : X) :
    f.base x ∈ basicOpen I g ↔
      IsUnit (X.presheaf.germ ⊤ x trivial (globalSectionsHom I X f g)) := by
  have h : x ∈ (Opens.map f.base).obj (basicOpen I g) ↔
      x ∈ X.toRingedSpace.basicOpen (globalSectionsHom I X f g) := by
    rw [preimage_basicOpen_eq]
  exact h.trans (RingedSpace.mem_basicOpen X.toRingedSpace (U := ⊤) _ x trivial)

end FormalSpectrum

end
