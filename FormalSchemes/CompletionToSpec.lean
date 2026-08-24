import FormalSchemes.Completion
import FormalSchemes.IndSchemeForward
import FormalSchemes.SpfGammaBase

set_option linter.style.header false

/-!
# The canonical morphism from a formal completion to the ambient affine scheme

`FormalSchemes/Completion.lean` constructs the **formal completion of `Spec R` along `V(I)`**
(EGA I, 10.8) as the object `formalCompletion R I hI = Spf (R^)`, the formal spectrum of the
`I`-adic completion, and identifies its underlying space with `Spec (R ⧸ I)`. What it does not
construct is the **morphism** `i : X_{/Y} ⟶ X`; yet every statement about the completion *as a
completion of something* is a statement about `i`. This file supplies it.

The construction costs nothing, because the affine-target mapping-out property of the formal
spectrum is already available: `FormalSpectrum.specHomEquiv` (`FormalSchemes/IndScheme.lean`)
identifies `Hom_{LRS}(Spf R', Spec B)` with `B →+* R'`, so the completion morphism is simply the
morphism corresponding to the completion map `R →+* R^`,

```
formalCompletion.toSpec = specHomEquiv.symm (algebraMap R (AdicCompletion I R)).
```

Its base map is then `Spec` of that ring map, restricted along the inclusion `Spf R^ ↪ Spec R^`,
and it is a **closed embedding onto `V(I)`** — which upgrades `formalCompletion.range_comap_mk`
from a statement about a set obtained from a homeomorphism to a statement about the canonical
morphism.

## The base map of a morphism into an affine scheme

Deriving the base map uses a general fact of independent interest, proved here for lack of a
better home: for a morphism `g : Spf R' ⟶ Spec B` the base map is `Spec` of `specHomEquiv g`
composed with the inclusion `Spf R' ↪ Spec R'` (`FormalSpectrum.base_eq_comap_specHomEquiv`).
This is the affine-target analogue of `FormalSpectrum.base_toPrimeSpectrum_eq`
(`FormalSchemes/SpfGammaBase.lean`), and like it the proof goes through
`FormalSpectrum.isUnit_germ_top_iff` — germs of global sections detect the prime — matched
against Mathlib's `LocallyRingedSpace.notMem_prime_iff_unit_in_stalk`, which says the same thing
about the unit `X ⟶ Spec Γ(X)` of the `Γ ⊣ Spec` adjunction. The two halves were already written
down next to each other and had simply never been composed.

## Main definitions and results

* `FormalSpectrum.toPrimeSpectrum_eq_comap_toΓSpecFun`: the inclusion `Spf R ↪ Spec R` is the
  adjunction unit's base map, transported along `globalSectionsEquiv`.
* `FormalSpectrum.base_eq_comap_specHomEquiv`: the base map of `g : Spf R ⟶ Spec B` is
  `Spec (specHomEquiv g)` composed with `Spf R ↪ Spec R`.
* `FormalSpectrum.specHomEquiv_naturality_left` / `_right`: naturality of `specHomEquiv` in the
  source (through `globalSectionsMap`) and in the affine target.
* `formalCompletion.toSpec`: the **canonical morphism** `X_{/Y} ⟶ X` (EGA I, 10.8).
* `formalCompletion.specHomEquiv_toSpec`: its global-sections map is the completion map `R →+* R^`.
* `formalCompletion.toSpec_base`, `range_toSpec_base`, `isClosedEmbedding_toSpec_base`: its base
  map, computed; its image is `V(I)`; and it is a closed embedding.
* `formalCompletion.residueMap`: the ring map `R →+* R^ ⧸ I·R^` whose `Spec` that base map is,
  with `surjective_residueMap` and `ker_residueMap` the two facts the last two rest on.
* `formalCompletion.map_comp_toSpec`: naturality in the pair `(Spec R, V(I))` — together with
  `formalCompletion.map_id` and `map_comp` this makes the completion a functor **over** `Spec`,
  which is what EGA I 10.8's functoriality statement asserts.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

section BaseMap

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- The inclusion `Spf R ↪ Spec R` is the base map of the unit `Spf R ⟶ Spec Γ(Spf R)` of the
`Γ ⊣ Spec` adjunction, read through `globalSectionsEquiv I : Γ(Spf R) ≃+* R`.

Both sides describe a point of `Spf R` by the same recipe — the primes at which a global section
has non-invertible germ — the left through `FormalSpectrum.isUnit_germ_top_iff` and the right
through `LocallyRingedSpace.notMem_prime_iff_unit_in_stalk`. -/
theorem toPrimeSpectrum_eq_comap_toΓSpecFun (x : FormalSpectrum I) :
    toPrimeSpectrum I x =
      PrimeSpectrum.comap (globalSectionsEquiv I).symm.toRingHom
        ((locallyRingedSpaceObj I).toΓSpecFun x) := by
  apply PrimeSpectrum.ext
  ext r
  rw [← not_iff_not]
  have h1 := (locallyRingedSpaceObj I).notMem_prime_iff_unit_in_stalk
    ((globalSectionsEquiv I).symm r) x
  have h2 := isUnit_germ_top_iff I x r
  exact (h1.trans h2).symm

/-- **The base map of a morphism into an affine scheme, in terms of `specHomEquiv`**, for a
morphism presented through the inverse of the equivalence: the morphism `Spf R ⟶ Spec B`
attached to `φ : B →+* R` acts on points as `Spec φ`, precomposed with the inclusion
`Spf R ↪ Spec R`. -/
theorem base_specHomEquiv_symm (B : Type u) [CommRing B] (φ : B →+* R) (x : FormalSpectrum I) :
    ((specHomEquiv I B).symm φ).base x = PrimeSpectrum.comap φ (toPrimeSpectrum I x) := by
  rw [specHomEquiv_symm_apply, toPrimeSpectrum_eq_comap_toΓSpecFun]
  rfl

/-- **The base map of a morphism into an affine scheme is `Spec` of its global-sections map**:
for `g : Spf R ⟶ Spec B` the point `g.base x` is the preimage under `specHomEquiv I B g` of the
prime of `R` at `x`. This is the affine-target analogue of `base_toPrimeSpectrum_eq`. -/
theorem base_eq_comap_specHomEquiv (B : Type u) [CommRing B]
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (x : FormalSpectrum I) :
    g.base x = PrimeSpectrum.comap (specHomEquiv I B g) (toPrimeSpectrum I x) := by
  conv_lhs => rw [← (specHomEquiv I B).symm_apply_apply g]
  exact base_specHomEquiv_symm I B _ x

end BaseMap

section Naturality

variable {R S : Type u} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
variable (I : Ideal R) (J : Ideal S) [IsAdicRing I] [IsAdicRing J]

/-- **Naturality of `specHomEquiv` in the source**: precomposing `v : Spf R ⟶ Spec B` with a
morphism `u : Spf S ⟶ Spf R` postcomposes the associated ring homomorphism with
`globalSectionsMap I J u : R →+* S`. -/
theorem specHomEquiv_naturality_left (B : Type u) [CommRing B]
    (u : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (v : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) :
    specHomEquiv J B (u ≫ v) = (globalSectionsMap I J u).comp (specHomEquiv I B v) := by
  refine RingHom.ext fun b => ?_
  exact (congrArg (globalSectionsEquiv J)
    (congrArg (u.c.app (op ⊤)).hom
      ((globalSectionsEquiv I).symm_apply_apply
        ((v.c.app (op ⊤)).hom
          (@algebraMap B
            ((Spec.locallyRingedSpaceObj (CommRingCat.of B)).presheaf.obj (op ⊤)) _ _
            (StructureSheaf.openAlgebra (R := B) (op ⊤)) b))))).symm

/-- **Naturality of `specHomEquiv` in the affine target**, in the direction of the inverse:
the morphism attached to `φ.comp f` is the morphism attached to `φ`, followed by `Spec f`. -/
theorem specHomEquiv_symm_naturality_right (B C : Type u) [CommRing B] [CommRing C]
    (f : B →+* C) (φ : C →+* R) :
    (specHomEquiv I B).symm (φ.comp f) =
      (specHomEquiv I C).symm φ ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom f) := by
  rw [specHomEquiv_symm_apply, specHomEquiv_symm_apply]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  congr 1
  have h : CommRingCat.ofHom ((globalSectionsEquiv I).symm.toRingHom.comp (φ.comp f)) =
      CommRingCat.ofHom f ≫
        CommRingCat.ofHom ((globalSectionsEquiv I).symm.toRingHom.comp φ) := rfl
  exact (congrArg Spec.locallyRingedSpaceMap h).trans (Spec.locallyRingedSpaceMap_comp _ _)

/-- **Naturality of `specHomEquiv` in the affine target**: postcomposing `v : Spf R ⟶ Spec C`
with `Spec f` for `f : B →+* C` precomposes the associated ring homomorphism with `f`. -/
theorem specHomEquiv_naturality_right (B C : Type u) [CommRing B] [CommRing C]
    (f : B →+* C) (v : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of C)) :
    specHomEquiv I B (v ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom f)) =
      (specHomEquiv I C v).comp f := by
  have h := specHomEquiv_symm_naturality_right I B C f (specHomEquiv I C v)
  rw [Equiv.symm_apply_apply] at h
  exact ((specHomEquiv I B).symm_apply_eq.mp h).symm

end Naturality

end FormalSpectrum

namespace formalCompletion

section ToSpec

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The **canonical morphism from the formal completion to the ambient affine scheme**
(EGA I, 10.8): `Spec R` completed along `V(I)` maps to `Spec R` by the morphism corresponding,
under the affine-target universal property `FormalSpectrum.specHomEquiv`, to the completion map
`R →+* R^`. -/
def toSpec (hI : I.FG) :
    (formalCompletion R I hI).toLocallyRingedSpace ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of R) :=
  haveI := AdicCompletion.isAdicRing_map I hI
  (FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition I) R).symm
    (algebraMap R (AdicCompletion I R))

/-- The global-sections map of `formalCompletion.toSpec` is the completion map `R →+* R^`. This
is a formality, but it is the statement everything below is proved from. -/
theorem specHomEquiv_toSpec (hI : I.FG) :
    haveI := AdicCompletion.isAdicRing_map I hI
    FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition I) R (toSpec R I hI) =
      algebraMap R (AdicCompletion I R) :=
  haveI := AdicCompletion.isAdicRing_map I hI
  (FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition I) R).apply_symm_apply _

/-- The base map of `formalCompletion.toSpec`: a point of the completion, viewed as a prime of
`R^` containing `I·R^`, maps to its preimage in `R`. -/
theorem toSpec_base (hI : I.FG) (x : FormalSpectrum (AdicCompletion.idealOfDefinition I)) :
    (toSpec R I hI).base x =
      PrimeSpectrum.comap (algebraMap R (AdicCompletion I R))
        (FormalSpectrum.toPrimeSpectrum (AdicCompletion.idealOfDefinition I) x) :=
  haveI := AdicCompletion.isAdicRing_map I hI
  FormalSpectrum.base_specHomEquiv_symm (AdicCompletion.idealOfDefinition I) R _ x

/-- The residue map `R →+* R^ ⧸ I·R^` of the completion. Composing the completion map with the
projection to the residue ring, this is the ring map whose `Spec` is the base map of
`formalCompletion.toSpec`. -/
def residueMap : R →+* AdicCompletion I R ⧸ AdicCompletion.idealOfDefinition I :=
  (Ideal.Quotient.mk (AdicCompletion.idealOfDefinition I)).comp
    (algebraMap R (AdicCompletion I R))

/-- The residue map of the completion is the residue map of `R` itself, read through the
identification `R^ ⧸ I·R^ ≃+* R ⧸ I` of `AdicCompletion.quotientEquiv`. -/
theorem quotientEquiv_residueMap (hI : I.FG) (r : R) :
    AdicCompletion.quotientEquiv I hI (residueMap R I r) = Ideal.Quotient.mk I r :=
  rfl

/-- The residue map of the completion is surjective: it is the residue map `R ↠ R ⧸ I`
composed with an isomorphism. -/
theorem surjective_residueMap (hI : I.FG) : Function.Surjective (residueMap R I) := fun z => by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.quotientEquiv I hI z)
  exact ⟨r, (AdicCompletion.quotientEquiv I hI).injective
    ((quotientEquiv_residueMap R I hI r).trans hr)⟩

/-- The kernel of the residue map of the completion is `I` itself: completion does not change
the residue ring, so `algebraMap R R^` pulls `I·R^` back to `I`. -/
theorem ker_residueMap (hI : I.FG) : RingHom.ker (residueMap R I) = I := by
  ext r
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    rw [← quotientEquiv_residueMap R I hI r, h, _root_.map_zero]
  · intro h
    refine (AdicCompletion.quotientEquiv I hI).injective ?_
    rw [quotientEquiv_residueMap R I hI r, h, _root_.map_zero]

/-- `formalCompletion.toSpec_base`, packaged through `residueMap`: the base map is `Spec` of
the residue map `R →+* R^ ⧸ I·R^`. -/
theorem toSpec_base_eq_comap (hI : I.FG) (x : FormalSpectrum (AdicCompletion.idealOfDefinition I)) :
    (toSpec R I hI).base x = PrimeSpectrum.comap (residueMap R I) x :=
  toSpec_base R I hI x

/-- The base map of the canonical morphism, as a function: it is `Spec` of the residue map. -/
theorem coe_toSpec_base (hI : I.FG) :
    ⇑(toSpec R I hI).base =
      fun x : FormalSpectrum (AdicCompletion.idealOfDefinition I) =>
        PrimeSpectrum.comap (residueMap R I) x :=
  funext (toSpec_base_eq_comap R I hI)

/-- **The formal completion sits inside `Spec R` as the closed subset `V(I)`** (EGA I, 10.8),
now as a statement about the canonical morphism rather than about the underlying space: the
image of `formalCompletion.toSpec` is the zero locus of `I`. -/
theorem range_toSpec_base (hI : I.FG) :
    Set.range ⇑(toSpec R I hI).base = PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [coe_toSpec_base R I hI]
  have h := range_comap_of_surjective _ (residueMap R I) (surjective_residueMap R I hI)
  rw [ker_residueMap R I hI] at h
  exact h

/-- The canonical morphism of EGA I 10.8 is a **closed embedding on underlying spaces**: the
formal completion is supported on the closed subscheme one completes along. -/
theorem isClosedEmbedding_toSpec_base (hI : I.FG) :
    Topology.IsClosedEmbedding ⇑(toSpec R I hI).base := by
  rw [coe_toSpec_base R I hI]
  exact PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (residueMap R I)
    (surjective_residueMap R I hI)

end ToSpec

/-- **Naturality of the canonical morphism in the pair `(Spec R, V(I))`** (EGA I, 10.8): the
square

```
formalCompletion S J ──→ formalCompletion R I
        │                          │
        ↓                          ↓
     Spec S       ──────→        Spec R
```

commutes. Together with `formalCompletion.map_id` and `formalCompletion.map_comp` this exhibits
the formal completion as a functor **over** `Spec`. -/
theorem map_comp_toSpec {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}
    (hI : I.FG) (hJ : J.FG) (f : R →+* S) (hf : I.map f ≤ J) :
    (formalCompletion.map hI hJ f hf).toLRSHom ≫ toSpec R I hI =
      toSpec S J hJ ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom f) := by
  haveI := AdicCompletion.isAdicRing_map I hI
  haveI := AdicCompletion.isAdicRing_map J hJ
  have h1 := FormalSpectrum.specHomEquiv_naturality_left
    (AdicCompletion.idealOfDefinition I) (AdicCompletion.idealOfDefinition J) R
    (formalCompletion.map hI hJ f hf).toLRSHom (toSpec R I hI)
  have h2 := FormalSpectrum.specHomEquiv_naturality_right
    (AdicCompletion.idealOfDefinition J) R S f (toSpec S J hJ)
  refine (FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition J) R).injective ?_
  have h3 : FormalSpectrum.globalSectionsMap (AdicCompletion.idealOfDefinition I)
      (AdicCompletion.idealOfDefinition J) (formalCompletion.map hI hJ f hf).toLRSHom =
      AdicCompletion.mapCompletion f hf hJ :=
    FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap ..
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [h3,
    show FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition I) R (toSpec R I hI) =
        algebraMap R (AdicCompletion I R) from
      (FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition I) R).apply_symm_apply _,
    show FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition J) S (toSpec S J hJ) =
        algebraMap S (AdicCompletion J S) from
      (FormalSpectrum.specHomEquiv (AdicCompletion.idealOfDefinition J) S).apply_symm_apply _]
  exact AdicCompletion.mapCompletion_comp_algebraMap f hf hJ

end formalCompletion
