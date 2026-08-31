import FormalSchemes.Spf

set_option linter.style.header false

/-!
# Sections of `O_{Spf R}` over an inhabited open are a nonzero ring

Every statement of the form "`Γ(Spf R, U)` is complete", "`Γ(Spf R, U)` is a complete adic ring",
"this subring of `Γ(Spf R, U)` is Hausdorff" is **vacuously true when that ring is `0`**, and this
tree proves several of them without anywhere recording that the ring is not `0`. This file supplies
the missing input, in the only generality it needs: sections over an open with a point in it.

The argument is one line and uses nothing about `Spf` beyond what `FormalSchemes.Spf` already
proves. `FormalSpectrum.isLocalRing_structureSheaf_stalk` (EGA I, 10.1.6) makes every stalk of the
structure sheaf a local ring, hence nontrivial; the germ at a point `x ∈ U` is a ring homomorphism
out of `Γ(Spf R, U)` into that stalk; and a ring homomorphism into a nontrivial ring has a
nontrivial domain (`RingHom.domain_nontrivial`), since `1 = 0` upstairs would force `1 = 0`
downstairs.

## Main results

* `FormalSpectrum.nontrivial_sections_of_mem`: `Γ(Spf R, U)` is nontrivial as soon as some `x`
  lies in `U`.
* `FormalSpectrum.nontrivial_sections_of_nonempty`: the same with the hypothesis phrased as
  `(U : Set _).Nonempty`, which is the shape the tree's nonemptiness lemmas produce.

## What is *not* proved here

Nothing about which opens are inhabited — that is a question about the ring `R` and its ideal of
definition, and the tree answers it separately in each case — for the Tate annulus by
`annulus_formalSpectrum_nonempty`, which is in the **root** namespace. Nothing about `U = ⊥`,
where the sections ring genuinely is `0` and the hypothesis of both results below fails.

No converse: these say an inhabited open has nonzero sections, not that an empty open is the only
way to get zero sections.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, 10.1.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Sections over an open containing a point are a nonzero ring.** The germ at `x` is a ring
homomorphism into the stalk, which is a local ring — hence nontrivial — by
`FormalSpectrum.isLocalRing_structureSheaf_stalk`, and `RingHom.domain_nontrivial` transports that
back to the source. -/
theorem nontrivial_sections_of_mem {U : Opens (FormalSpectrum I)} {x : FormalSpectrum I}
    (hx : x ∈ U) :
    Nontrivial ((locallyRingedSpaceObj I).presheaf.obj (op U)) :=
  ((locallyRingedSpaceObj I).presheaf.germ U x hx).hom.domain_nontrivial

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Sections over an inhabited open are a nonzero ring**, with the hypothesis in the form the
tree's nonemptiness lemmas produce. -/
theorem nontrivial_sections_of_nonempty {U : Opens (FormalSpectrum I)}
    (hU : (U : Set (FormalSpectrum I)).Nonempty) :
    Nontrivial ((locallyRingedSpaceObj I).presheaf.obj (op U)) :=
  nontrivial_sections_of_mem I hU.choose_spec

end FormalSpectrum
