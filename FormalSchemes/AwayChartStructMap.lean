import FormalSchemes.AwayBaseChangeTopFiniteType
import FormalSchemes.BasicOpenImmersion

set_option linter.style.header false

/-!
# Basic-open charts commute with structural morphisms

One square, an instance of `FormalSpectrum.locallyRingedSpaceMap_comp`, needed to run EGA I
10.13's composition law at a non-affine target.

`AlgebraicGeometry.basicOpenChart_comp_structMap` (`FormalSchemes.RelativeTopFiniteTypeBasis`)
already shrinks the *source* of a structural morphism: a basic-open chart `Spf A{1/g}^ ⟶ Spf A`
composed with `Spf A ⟶ Spf R` is the structural morphism of `A{1/g}^` over the same base. The
square here shrinks the **base** as well. Over the basic open `D(c) ⊆ Spf R` the chart of the
source is taken at the image `c · A`, and

```
Spf A{1/(c·A)}^ --chart--> Spf A
      |                      |
      | struct               | struct
      v                      v
   Spf R{1/c}^  --chart--> Spf R
```

commutes. This is the geometric counterpart of
`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange_of_algebraMap_eq`, whose
algebra structure it is stated relative to: the vertical map on the left is `Spf` of
`FormalSpectrum.awayBaseHom`.

The proof does not unfold a structure sheaf. `FormalSpectrum.basicOpenChart` and
`IsTopologicallyFiniteType.structMap` are both `FormalSpectrum.locallyRingedSpaceMap`, so the
square is the two readings of one composite ring homomorphism, identified by
`FormalSpectrum.awayCompletionHom_comp_algebraMap` against
`FormalSpectrum.awayBaseHom_comp_algebraMap`.

## Main results

* `FormalSpectrum.basicOpenChart_comp_structMap_baseChange`: the square.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory

universe u

namespace FormalSpectrum

variable {R A : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
variable [CommRing A] [Algebra R A] [TopologicalSpace A] {L : Ideal A} [IsAdicRing L]

/-- **The away base-change square.** Shrinking the base to `D(c)` and the source to `D(c · A)`
commutes with the structural morphisms, the left-hand vertical being `Spf` of
`FormalSpectrum.awayBaseHom`.

Stated relative to a supplied `Algebra (R{1/c}^) (A{1/(c·A)}^)` and the identification `halg` of
its structure map with `awayBaseHom`, exactly as
`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange_of_algebraMap_eq` is: there
is no canonical such instance, the two rings being completions of localisations of two different
rings at two different elements.

The two readings of the composite `R → R{1/c}^ → A{1/(c·A)}^ = R → A → A{1/(c·A)}^` are identified
by `FormalSpectrum.awayBaseHom_comp_algebraMap` against
`FormalSpectrum.awayCompletionHom_comp_algebraMap`. -/
theorem basicOpenChart_comp_structMap_baseChange (hI : I.FG)
    (hL : I.map (algebraMap R A) = L) (c : R)
    [IsAdicRing (awayCompletionIdeal I c)]
    [IsAdicRing (awayCompletionIdeal L (algebraMap R A c))]
    [Algebra (awayCompletion I c) (awayCompletion L (algebraMap R A c))]
    (halg : algebraMap (awayCompletion I c) (awayCompletion L (algebraMap R A c)) =
      awayBaseHom c hI hL)
    (hbc : (awayCompletionIdeal I c).map
        (algebraMap (awayCompletion I c) (awayCompletion L (algebraMap R A c))) =
      awayCompletionIdeal L (algebraMap R A c)) :
    basicOpenChart L (algebraMap R A c) ≫ IsTopologicallyFiniteType.structMap hL =
      IsTopologicallyFiniteType.structMap hbc ≫ basicOpenChart I c := by
  have hring : (awayCompletionHom L (algebraMap R A c)).comp (algebraMap R A) =
      (awayBaseHom c hI hL).comp (awayCompletionHom I c) := by
    rw [awayCompletionHom_comp_algebraMap,
      show awayCompletionHom I c = algebraMap R (awayCompletion I c) from rfl,
      awayBaseHom_comp_algebraMap]
  have hIle : I ≤ (awayCompletionIdeal L (algebraMap R A c)).comap
      ((awayCompletionHom L (algebraMap R A c)).comp (algebraMap R A)) := by
    rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_map, hL, map_awayCompletionHom]
  have h1 := locallyRingedSpaceMap_comp I L (awayCompletionIdeal L (algebraMap R A c))
    (algebraMap R A) (awayCompletionHom L (algebraMap R A c))
    (Ideal.map_le_iff_le_comap.mp hL.le)
    (le_comap_awayCompletionHom L (algebraMap R A c)) hIle
  have h2 := locallyRingedSpaceMap_comp I (awayCompletionIdeal I c)
    (awayCompletionIdeal L (algebraMap R A c))
    (awayCompletionHom I c) (awayBaseHom c hI hL)
    (le_comap_awayCompletionHom I c)
    (Ideal.map_le_iff_le_comap.mp (by rw [← halg]; exact hbc.le))
    (by rw [← hring]; exact hIle)
  have h3 : locallyRingedSpaceMap I (awayCompletionIdeal L (algebraMap R A c))
        ((awayCompletionHom L (algebraMap R A c)).comp (algebraMap R A)) hIle =
      locallyRingedSpaceMap I (awayCompletionIdeal L (algebraMap R A c))
        ((awayBaseHom c hI hL).comp (awayCompletionHom I c)) (by rw [← hring]; exact hIle) :=
    locallyRingedSpaceMap_congr _ _ _ _ _ _ hring
  have h4 : IsTopologicallyFiniteType.structMap hbc =
      locallyRingedSpaceMap (awayCompletionIdeal I c)
        (awayCompletionIdeal L (algebraMap R A c)) (awayBaseHom c hI hL)
        (Ideal.map_le_iff_le_comap.mp (by rw [← halg]; exact hbc.le)) :=
    locallyRingedSpaceMap_congr _ _ _ _ _ _ halg
  rw [h4]
  exact h1.symm.trans (h3.trans h2)

end FormalSpectrum
