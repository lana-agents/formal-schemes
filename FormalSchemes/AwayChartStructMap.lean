import FormalSchemes.AwayBaseChangeTopFiniteType
import FormalSchemes.BasicOpenImmersion

set_option linter.style.header false

/-!
# Basic-open charts commute with structural morphisms

Two squares, both instances of `FormalSpectrum.locallyRingedSpaceMap_comp`, and both needed to
run EGA I 10.13's composition law at a non-affine target.

The first shrinks only the source. A basic-open chart `Spf A{1/g}^ ⟶ Spf A` of a formal spectrum
over a base `(R, I)` composes with the structural morphism to give the structural morphism of
`A{1/g}^` over the *same* base:

```
Spf A{1/g}^ --chart--> Spf A --struct--> Spf R    =    Spf A{1/g}^ --struct--> Spf R
```

The second shrinks the base as well. Over the basic open `D(c) ⊆ Spf R` the chart of the source
is taken at the image `c · A`, and the square

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

Neither proof unfolds a structure sheaf. `FormalSpectrum.basicOpenChart` and
`AlgebraicGeometry.IsTopologicallyFiniteType.structMap` are both
`FormalSpectrum.locallyRingedSpaceMap`, so each square is the two readings of one composite ring
homomorphism, identified by `FormalSpectrum.awayCompletionHom_comp_algebraMap` and
`FormalSpectrum.awayBaseHom_comp_algebraMap` respectively.

## Main results

* `FormalSpectrum.basicOpenChart_comp_structMap_base`: the first square.
* `FormalSpectrum.basicOpenChart_comp_structMap`: the second square, the away base change.

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

/-- **A basic-open chart of the source composes into the structural morphism.** Both sides are
`locallyRingedSpaceMap I (awayCompletionIdeal L g)` of the composite `R → A → A{1/g}^`, which is
`algebraMap R (A{1/g}^)` by `FormalSpectrum.awayCompletionHom_comp_algebraMap`.

The hypothesis `hbc` is the ideal identity the target structural morphism is taken at; for a
tf-type algebra it is `AlgebraicGeometry.IsTopologicallyFiniteType.map_eq` of
`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion`. It is a hypothesis rather than a
consequence so that this file needs nothing about finite type. -/
theorem basicOpenChart_comp_structMap_base (hL : I.map (algebraMap R A) = L) (g : A)
    [IsAdicRing (awayCompletionIdeal L g)]
    (hbc : I.map (algebraMap R (awayCompletion L g)) = awayCompletionIdeal L g) :
    basicOpenChart L g ≫ IsTopologicallyFiniteType.structMap hL =
      IsTopologicallyFiniteType.structMap hbc := by
  have hIle : I ≤ (awayCompletionIdeal L g).comap
      ((awayCompletionHom L g).comp (algebraMap R A)) := by
    rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_map, hL, map_awayCompletionHom]
  have h1 := locallyRingedSpaceMap_comp I L (awayCompletionIdeal L g)
    (algebraMap R A) (awayCompletionHom L g)
    (Ideal.map_le_iff_le_comap.mp hL.le) (le_comap_awayCompletionHom L g) hIle
  have h2 : locallyRingedSpaceMap I (awayCompletionIdeal L g)
        ((awayCompletionHom L g).comp (algebraMap R A)) hIle =
      IsTopologicallyFiniteType.structMap hbc :=
    locallyRingedSpaceMap_congr _ _ _ _ _ _ (awayCompletionHom_comp_algebraMap g)
  exact h1.symm.trans h2

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
theorem basicOpenChart_comp_structMap (hI : I.FG) (hL : I.map (algebraMap R A) = L) (c : R)
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
