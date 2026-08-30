import FormalSchemes.CofinalSheafComparisonGeneral
import FormalSchemes.SpfFunctorial
import FormalSchemes.SpfGammaFunctorial
import FormalSchemes.TopFiniteType

set_option linter.style.header false

/-!
# The ideal-independence isomorphism commutes with structural morphisms

`FormalSpectrum.generalCofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonGeneral`) identifies
the formal spectra of any two ideals of definition of one adic ring: `Spf` sees only the
topological ring. `IsTopologicallyFiniteType.ofCofinal` (`FormalSchemes.CofinalTopFiniteType`)
moves a tf-type structure from one base ideal to a cofinal one, and in doing so replaces the ideal
of the top ring `L = I · A` by `J · A`. This file says that the two operations agree: the square

```
Spf (J · A) --structMap--> Spf J
    |                        |
    | cofinal iso            | cofinal iso
    v                        v
Spf (I · A) --structMap--> Spf I
```

commutes.

That is the statement EGA I 10.13's composition law at a non-affine target needs, and it is the
half of `FormalSchemes.CofinalTopFiniteType` that is geometric rather than algebraic: the middle
chart of a tower arrives with two ideals of definition, one from each factor, and the two are
cofinal but never equal — `L` against `L ^ 2` is the standing counterexample. Aligning them by
`IsTopologicallyFiniteType.ofCofinal` moves the *charts* as well as the *rings*, and without the
square below the two factorisations cannot be composed.

## Why it is two lines of functoriality and not a sheaf computation

`FormalSpectrum.cofinalSpfIso`'s inverse is, by construction,
`FormalSpectrum.locallyRingedSpaceMap` of the **identity** ring homomorphism, and
`IsTopologicallyFiniteType.structMap` is `locallyRingedSpaceMap` of `algebraMap`. In the nested
case the square is therefore two instances of `FormalSpectrum.locallyRingedSpaceMap_comp`, both
computing `locallyRingedSpaceMap` of `algebraMap R A` read as a composite in the two possible ways
— nothing about the structure sheaves is unfolded. The general case follows by running the nested
one at the ideal `I * J`, which is where `FormalSpectrum.isAdicRing_mul` is needed.

## Main results

* `FormalSpectrum.isAdicRing_mul`: the product of two ideals of definition is an ideal of
  definition — the nested ideal `FormalSpectrum.generalCofinalSpfIso` factors through, extracted
  from its proof so that the factorisation can be stated.
* `FormalSpectrum.generalCofinalSpfIso_eq`: that factorisation, as an equation.
* `FormalSpectrum.structMap_comp_cofinalSpfIso_inv`: **the square, nested case.**
* `FormalSpectrum.structMap_comp_generalCofinalSpfIso_inv`: **the square, general case.**
* `FormalSpectrum.globalSectionsMap_generalCofinalSpfIso_hom`: the comparison is the identity on
  global sections — the form in which an *abstract* isomorphism of two charts is compared with it.
* `FormalSpectrum.globalSectionsMap_structMap`: global sections of a structural morphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.3, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
variable [IsAdicRing I] [IsAdicRing J]

/-- **The product of two ideals of definition is an ideal of definition.** It is nested below both,
and cofinal with both because some power of each lies in the other
(`IsAdic.exists_pow_le`), so the adic topology it defines is the given one; completeness is
`IsHausdorff.of_le` and `IsPrecomplete.of_cofinal` at the containment `I * J ≤ I`.

The proof is the opening of `FormalSpectrum.generalCofinalSpfIso`, extracted so that the
factorisation of that isomorphism through `Spf (I * J)` can be *stated*
(`FormalSpectrum.generalCofinalSpfIso_eq`) rather than only used inside its own construction.

Not an instance: `I * J` is not a pattern instance search can key on without looping. -/
theorem isAdicRing_mul : IsAdicRing (I * J) := by
  have hIadic : IsAdic I := IsAdicRing.isAdic
  have hJadic : IsAdic J := IsAdicRing.isAdic
  haveI : IsTopologicalRing R := hIadic.isTopologicalRing
  have hKI : (I * J : Ideal R) ≤ I := by rw [mul_comm]; exact Ideal.mul_le_left
  have hIcK : ∃ c : ℕ, I ^ (c + 1) ≤ I * J := by
    obtain ⟨m, hm⟩ := IsAdic.exists_pow_le hJadic hIadic
    refine ⟨m, ?_⟩
    rw [pow_succ]
    calc I ^ m * I ≤ J * I := Ideal.mul_mono hm le_rfl
      _ = I * J := mul_comm J I
  have hK_adic : IsAdic (I * J) := by
    obtain ⟨c, hc⟩ := hIcK
    exact IsAdic.of_le_of_pow_le (is_ideal_adic_pow hIadic (Nat.succ_pos c)) hc
      (Ideal.pow_right_mono hKI (c + 1))
  haveI : IsAdicComplete (I * J) R := by
    obtain ⟨c, hc⟩ := hIcK
    exact { toIsHausdorff := IsHausdorff.of_le hKI
            toIsPrecomplete := IsPrecomplete.of_cofinal hKI hc }
  exact { isAdic := hK_adic }

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing J] in
/-- `I * J ≤ I`, the containment `Ideal.mul_le_left` does not give directly. -/
theorem mul_le_self_left : (I * J : Ideal R) ≤ I := by rw [mul_comm]; exact Ideal.mul_le_left

/-- **The ideal-independence isomorphism factors through the product ideal.** True by `rfl`: the
`have`s inside `FormalSpectrum.generalCofinalSpfIso`'s construction are all proofs of `Prop`s —
including the `IsAdicRing (I * J)` instance, since `IsAdicRing` is a `Prop` class — so proof
irrelevance identifies them with the ones supplied here. -/
theorem generalCofinalSpfIso_eq (hI : I.FG) (hJ : J.FG) :
    haveI := isAdicRing_mul I J
    generalCofinalSpfIso I J hI hJ =
      (cofinalSpfIso (I * J) I (mul_le_self_left I J) (hI.mul hJ) hI).symm ≪≫
        cofinalSpfIso (I * J) J Ideal.mul_le_left (hI.mul hJ) hJ := rfl

variable {I J}
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable {L M : Ideal A} [IsAdicRing L] [IsAdicRing M]

/-- **The square, for nested ideals of definition.** With `I ≤ J` on the base and the induced
`L = I · A ≤ M = J · A` on the top ring, the two structural morphisms are intertwined by the two
comparison morphisms.

Both sides are `locallyRingedSpaceMap I M (algebraMap R A)`, read as a composite in the two
possible ways: through `(J, M)` with the identity of `R` first, and through `(I, L)` with the
identity of `A` last. `FormalSpectrum.locallyRingedSpaceMap_comp` computes each, and
`FormalSpectrum.locallyRingedSpaceMap_congr` identifies the two composite ring homomorphisms,
which differ only by `RingHom.comp_id` against `RingHom.id_comp`. -/
theorem structMap_comp_cofinalSpfIso_inv (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG)
    (hIL : I.map (algebraMap R A) = L) (hJM : J.map (algebraMap R A) = M)
    (hLM : L ≤ M) (hL : L.FG) (hM : M.FG) :
    IsTopologicallyFiniteType.structMap hJM ≫ (cofinalSpfIso I J hIJ hI hJ).inv =
      (cofinalSpfIso L M hLM hL hM).inv ≫ IsTopologicallyFiniteType.structMap hIL := by
  have hIM : I ≤ M.comap (algebraMap R A) :=
    Ideal.map_le_iff_le_comap.mp (le_trans (Ideal.map_mono hIJ) hJM.le)
  have h1 := locallyRingedSpaceMap_comp I J M (RingHom.id R) (algebraMap R A)
    (le_comap_id_of_le I J hIJ) (Ideal.map_le_iff_le_comap.mp hJM.le)
    (show I ≤ M.comap ((algebraMap R A).comp (RingHom.id R)) by simpa using hIM)
  have h2 := locallyRingedSpaceMap_comp I L M (algebraMap R A) (RingHom.id A)
    (Ideal.map_le_iff_le_comap.mp hIL.le) (le_comap_id_of_le L M hLM)
    (show I ≤ M.comap ((RingHom.id A).comp (algebraMap R A)) by simpa using hIM)
  have h3 : locallyRingedSpaceMap I M ((algebraMap R A).comp (RingHom.id R))
        (show I ≤ M.comap ((algebraMap R A).comp (RingHom.id R)) by simpa using hIM) =
      locallyRingedSpaceMap I M ((RingHom.id A).comp (algebraMap R A))
        (show I ≤ M.comap ((RingHom.id A).comp (algebraMap R A)) by simpa using hIM) :=
    locallyRingedSpaceMap_congr I M _ _ _ _ (by simp)
  exact h1.symm.trans (h3.trans h2)

/-- **The square, for arbitrary cofinal ideals of definition.** No containment between `I` and `J`
is assumed; the nested case is run twice, at the product ideal `I * J` on the base and at
`(I * J) · A = L * M` on the top ring, which is where `Ideal.map_mul` enters.

This is the form the composition law consumes: the two ideals of definition of a middle chart
arrive from independent witnesses, and nothing nests them. -/
theorem structMap_comp_generalCofinalSpfIso_inv (hI : I.FG) (hJ : J.FG)
    (hIL : I.map (algebraMap R A) = L) (hJM : J.map (algebraMap R A) = M)
    (hL : L.FG) (hM : M.FG) :
    IsTopologicallyFiniteType.structMap hJM ≫ (generalCofinalSpfIso I J hI hJ).inv =
      (generalCofinalSpfIso L M hL hM).inv ≫ IsTopologicallyFiniteType.structMap hIL := by
  haveI := isAdicRing_mul I J
  haveI := isAdicRing_mul L M
  have hKA : (I * J).map (algebraMap R A) = L * M := by
    rw [Ideal.map_mul, hIL, hJM]
  have hJside := structMap_comp_cofinalSpfIso_inv (I := I * J) (J := J) (L := L * M) (M := M)
    Ideal.mul_le_left (hI.mul hJ) hJ hKA hJM Ideal.mul_le_left (hL.mul hM) hM
  have hIside := structMap_comp_cofinalSpfIso_inv (I := I * J) (J := I) (L := L * M) (M := L)
    (mul_le_self_left I J) (hI.mul hJ) hI hKA hIL (mul_le_self_left L M) (hL.mul hM) hL
  set kI := cofinalSpfIso (I * J) I (mul_le_self_left I J) (hI.mul hJ) hI with hkI
  set kL := cofinalSpfIso (L * M) L (mul_le_self_left L M) (hL.mul hM) hL with hkL
  have key : IsTopologicallyFiniteType.structMap hKA ≫ kI.hom =
      kL.hom ≫ IsTopologicallyFiniteType.structMap hIL := by
    calc IsTopologicallyFiniteType.structMap hKA ≫ kI.hom
        = (kL.hom ≫ kL.inv) ≫ IsTopologicallyFiniteType.structMap hKA ≫ kI.hom := by
          rw [Iso.hom_inv_id, Category.id_comp]
      _ = kL.hom ≫ (kL.inv ≫ IsTopologicallyFiniteType.structMap hKA) ≫ kI.hom := by
          rw [Category.assoc, Category.assoc]
      _ = kL.hom ≫ (IsTopologicallyFiniteType.structMap hIL ≫ kI.inv) ≫ kI.hom := by
          rw [hIside]
      _ = kL.hom ≫ IsTopologicallyFiniteType.structMap hIL := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [generalCofinalSpfIso_eq I J hI hJ, generalCofinalSpfIso_eq L M hL hM]
  simp only [Iso.trans_inv, Iso.symm_inv, ← hkI, ← hkL]
  rw [← Category.assoc, hJside, Category.assoc, key, Category.assoc]

/-! ### Global sections of the comparison isomorphism -/

variable (I J)

/-- **The global-sections map of a structural morphism is the structure map of the algebra.**
`AlgebraicGeometry.IsTopologicallyFiniteType.structMap` is `locallyRingedSpaceMap` of
`algebraMap`, so this is `FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`; it earns a name
because `rw` is syntactic and no rewrite fires on the `structMap` spelling. -/
theorem globalSectionsMap_structMap {A : Type u} [CommRing A] [TopologicalSpace A] [Algebra R A]
    {L : Ideal A} [IsAdicRing L] (h : I.map (algebraMap R A) = L) :
    globalSectionsMap I L (IsTopologicallyFiniteType.structMap h) = algebraMap R A :=
  globalSectionsMap_locallyRingedSpaceMap I L (algebraMap R A) _

/-- **The comparison morphism is `Spf` of the identity, so its global-sections map is the
identity.** Immediate from `FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`, since
`FormalSpectrum.cofinalSpfIso`'s inverse *is* `locallyRingedSpaceMap` of `RingHom.id`. -/
theorem globalSectionsMap_cofinalSpfIso_inv (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) :
    globalSectionsMap I J (cofinalSpfIso I J hIJ hI hJ).inv = RingHom.id R :=
  globalSectionsMap_locallyRingedSpaceMap I J (RingHom.id R) (le_comap_id_of_le I J hIJ)

/-- The same for the forward direction, by functoriality of global sections: the two composites
are the identity morphism, whose global-sections map is `RingHom.id`. -/
theorem globalSectionsMap_cofinalSpfIso_hom (hIJ : I ≤ J) (hI : I.FG) (hJ : J.FG) :
    globalSectionsMap J I (cofinalSpfIso I J hIJ hI hJ).hom = RingHom.id R := by
  have h := globalSectionsMap_comp I J I (cofinalSpfIso I J hIJ hI hJ).hom
    (cofinalSpfIso I J hIJ hI hJ).inv
  rw [(cofinalSpfIso I J hIJ hI hJ).hom_inv_id, globalSectionsMap_id,
    globalSectionsMap_cofinalSpfIso_inv] at h
  simpa using h.symm

/-- **The ideal-independence isomorphism is invisible on global sections.** Both formal spectra
have the same ring of global sections, and the comparison induces the identity on it.

This is what identifies an *abstract* isomorphism of formal spectra with the comparison up to
`Spf` of a ring isomorphism: by `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`, a
morphism of formal spectra with continuous global-sections map is `Spf` of that map, so composing
with the comparison changes nothing but the ideal. -/
theorem globalSectionsMap_generalCofinalSpfIso_hom (hI : I.FG) (hJ : J.FG) :
    globalSectionsMap J I (generalCofinalSpfIso I J hI hJ).hom = RingHom.id R := by
  haveI := isAdicRing_mul I J
  rw [generalCofinalSpfIso_eq I J hI hJ]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [globalSectionsMap_comp, globalSectionsMap_cofinalSpfIso_inv,
    globalSectionsMap_cofinalSpfIso_hom]
  simp

end FormalSpectrum
