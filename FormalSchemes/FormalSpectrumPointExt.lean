import FormalSchemes.FormalSpectrum

set_option linter.style.header false

/-!
# Points of a formal spectrum are separated by its basic opens

Two points of `Spf (R, I)` that lie in exactly the same basic opens `D(f)`, `f : R`, are equal
(`FormalSpectrum.eq_of_forall_mem_basicOpen_iff`). This is the extensionality principle that turns
a description of the *preimages* of the basic opens along a morphism into a description of that
morphism's fibres.

## Why this file exists, and why it is this low

`FormalSpectrum.mem_basicOpen` reads membership of a point in `D(f)` as non-membership of
`Ideal.Quotient.mk I f` in that point's prime ideal, and `Ideal.Quotient.mk I` is surjective,
so the family of memberships determines the prime and `PrimeSpectrum.ext` finishes. Nothing else
is used: no topology on `R`, no adic hypothesis, no sheaf.

`FormalSchemes/FormalSpectrum.lean`, where the statement belongs on subject matter, has a reverse
closure of **515** — nearly the whole tree — so this is a new module over it rather than an edit
to it.

## Main results

* `FormalSpectrum.eq_of_forall_mem_basicOpen_iff`: a point of `Spf (R, I)` is determined by the
  set of `f : R` whose basic open contains it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.
-/

universe u

open TopologicalSpace

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **A point of `Spf (R, I)` is determined by the basic opens containing it.** Membership in
`FormalSpectrum.basicOpen I f` is non-membership of the residue of `f` in the prime
(`FormalSpectrum.mem_basicOpen`), and every element of `R ⧸ I` is such a residue, so the family of
memberships pins the prime down. -/
theorem eq_of_forall_mem_basicOpen_iff {x y : FormalSpectrum I}
    (h : ∀ f : R, x ∈ basicOpen I f ↔ y ∈ basicOpen I f) : x = y := by
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  simpa only [mem_basicOpen, not_iff_not] using (h f).not

end FormalSpectrum
