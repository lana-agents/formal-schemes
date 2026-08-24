import FormalSchemes.IndSchemeForward
import FormalSchemes.Completion

set_option linter.style.header false

/-!
# The ind-scheme universal property is restriction to the thickenings

`FormalSchemes/IndScheme.lean` establishes the affine-target mapping-out property of the formal
spectrum, `FormalSpectrum.specHomEquiv : Hom_{LRS}(Spf R, Spec B) ≃ (B →+* R)`, and
`FormalSchemes/IndSchemeLimit.lean` repackages its right-hand side as a limit
`lim_n Hom(Spec (R ⧸ Iⁿ), Spec B)`. Both are built from the `Γ ⊣ Spec` adjunction, so neither
says anything about the *thickening morphisms* `FormalSpectrum.thickeningMap I n :
Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R` of `FormalSchemes/Thickenings.lean` — the cocone that makes
`Spf R = colim_n Spec (R ⧸ I ^ (n + 1))` (EGA I, 10.6.3) a geometric statement rather than an
abstract bijection of hom-sets.

This file closes that gap. The main result is

```
thickeningMap I n ≫ g = Spec (mod I ^ (n + 1) ∘ specHomEquiv I B g)
```

(`FormalSpectrum.thickeningMap_comp_specHom`): **restricting a morphism `g : Spf R ⟶ Spec B` to
the `n`-th infinitesimal thickening is `Spec` of the reduction of its ring homomorphism modulo
`I ^ (n + 1)`.** Together with completeness of `R` this gives the uniqueness half of the colimit
property, `FormalSpectrum.hom_ext_thickeningMap`: a morphism out of `Spf R` into an affine scheme
is determined by its restrictions to the thickenings.

## Main results

* `FormalSpectrum.homEquiv_symm_unop_apply`: for an arbitrary locally ringed space `X`, the ring
  homomorphism `B →+* Γ(X, ⊤)` corresponding under `Γ ⊣ Spec` to a morphism `X ⟶ Spec B` is
  computed by the global-sections component `h.c.app (op ⊤)`. This is the source-generic form of
  `FormalSpectrum.specHomEquiv_apply` (`FormalSchemes/IndSchemeForward.lean`), which is the case
  `X = Spf R`.
* `FormalSpectrum.hom_ext_toSpec`: two morphisms of locally ringed spaces `X ⟶ Spec B` agree as
  soon as their global-sections components agree on `B` (the locally-ringed-space analogue of
  Mathlib's `AlgebraicGeometry.ext_to_Spec`, which is stated for schemes).
* `FormalSpectrum.thickeningMap_c_app_top`: the global-sections component of `thickeningMap I n`
  is reduction modulo `I ^ (n + 1)` through `globalSectionsEquiv`.
* `FormalSpectrum.thickeningMap_comp_specHom`: the compatibility of `specHomEquiv` with the
  thickening cocone, displayed above.
* `FormalSpectrum.thickeningMap_comp_specHomEquiv_symm`: the same statement read in the other
  direction — the morphism `Spf R ⟶ Spec B` attached to `φ : B →+* R` restricts on the `n`-th
  thickening to `Spec` of `φ` followed by reduction.
* `FormalSpectrum.hom_ext_thickeningMap`: a morphism `Spf R ⟶ Spec B` is determined by its
  restrictions to the thickenings.

## Implementation notes

Inside `hom_ext_toSpec`, `homEquiv_symm_unop_apply` must be applied with `Eq.trans`, **not**
`rw`. The goal produced by `Adjunction.homEquiv`'s injectivity mentions
`Spec.toLocallyRingedSpace.obj (op (CommRingCat.of B))` where the statement has the
definitionally equal `Spec.locallyRingedSpaceObj (CommRingCat.of B)`, and `rw`'s keyed matching
does not see through that. A `set_option backward.isDefEq.respectTransparency false` bump does
**not** fix it either — it was tried, and it is the `rw` that has to go; once the rewrites are
replaced by `Eq.trans` the bump is unnecessary and this file needs no `set_option` beyond
`linter.style.header false`. Worth recording, since the reflex on this tree is to reach for the
transparency bump whenever an `instances`-transparency note appears in the error.

The same applies one line later, to Mathlib's `StructureSheaf.toOpen_comp_comap_apply`: it spells
the target open as `Opens.comap ⟨PrimeSpectrum.comap f, _⟩ U` where the goal of
`thickeningMap_comp_specHom` has `(Opens.map base).obj ⊤`, so it too must be supplied by `exact`
rather than `rw`, even though the two are definitionally equal.

Finally, `hl` in `thickeningMap_comp_specHom` is `rfl`: for morphisms of locally ringed spaces the
global-sections component of a composite really is the two components composed, with no
`Opens.map` transport, because `(Opens.map f.base).obj ⊤` reduces to `⊤`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.7).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

/-!
### Morphisms into an affine scheme, from an arbitrary locally ringed space
-/

section Generic

variable {X : LocallyRingedSpace.{u}} (B : Type u) [CommRing B]

/-- The ring homomorphism `B →+* Γ(X, ⊤)` corresponding under the adjunction `Γ ⊣ Spec` to a
morphism of locally ringed spaces `h : X ⟶ Spec B` is computed by the global-sections component
of `h`. This is `FormalSpectrum.specHomEquiv_apply` with an arbitrary source. -/
theorem homEquiv_symm_unop_apply
    (h : X ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) (b : B) :
    ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X
        (op (CommRingCat.of B))).symm h).unop.hom b =
      (h.c.app (op ⊤)).hom
        (@algebraMap B ((Spec.locallyRingedSpaceObj (CommRingCat.of B)).presheaf.obj (op ⊤)) _ _
          (StructureSheaf.openAlgebra (R := B) (op ⊤)) b) := by
  set f := (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (CommRingCat.of B))).symm h with hf
  have hg : (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (CommRingCat.of B))) f = h := by
    rw [hf]
    exact Equiv.apply_symm_apply _ _
  -- The Mathlib crux: `algebraMap ≫ (homEquiv f).c.app U = f.unop ≫ X.presheaf.map …`.
  have hmath := ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app f (op ⊤)
  -- `erw` reduces `(op ⊤).unop` to `⊤` when matching `presheaf_map_top_le_top`.
  erw [presheaf_map_top_le_top, Category.comp_id] at hmath
  have hmath2 := hg ▸ hmath
  rw [← hmath2]
  rfl

/-- **Two morphisms of locally ringed spaces into an affine scheme agree as soon as their
global-sections components do.** This is the locally-ringed-space analogue of Mathlib's
`AlgebraicGeometry.ext_to_Spec`, which is stated for schemes. -/
theorem hom_ext_toSpec (f g : X ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (h : ∀ b : B, (f.c.app (op ⊤)).hom
        (@algebraMap B ((Spec.locallyRingedSpaceObj (CommRingCat.of B)).presheaf.obj (op ⊤)) _ _
          (StructureSheaf.openAlgebra (R := B) (op ⊤)) b) =
      (g.c.app (op ⊤)).hom
        (@algebraMap B ((Spec.locallyRingedSpaceObj (CommRingCat.of B)).presheaf.obj (op ⊤)) _ _
          (StructureSheaf.openAlgebra (R := B) (op ⊤)) b)) :
    f = g := by
  refine (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (CommRingCat.of B))).symm.injective
    (Opposite.unop_injective (CommRingCat.hom_ext (RingHom.ext fun b => ?_)))
  exact (homEquiv_symm_unop_apply B f b).trans
    ((h b).trans (homEquiv_symm_unop_apply B g b).symm)

end Generic

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-!
### The thickening morphisms on global sections
-/

/-- **The global-sections component of the thickening morphism is reduction modulo
`I ^ (n + 1)`**, read through `globalSectionsEquiv I : Γ(⊤, O_{Spf R}) ≃+* R`. -/
theorem thickeningMap_c_app_top (n : ℕ)
    (s : (structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))) :
    ((thickeningMap I n).c.app (op ⊤)).hom s =
      algebraMap (R ⧸ I ^ (n + 1))
        ((thickeningSheaf I n).presheaf.obj (op (⊤ : Opens (FormalSpectrum I))))
        (Ideal.Quotient.mk (I ^ (n + 1)) (globalSectionsEquiv I s)) := by
  rw [mk_globalSectionsEquiv I n s, ← topLevelEquiv_symm_apply]
  exact (RingEquiv.symm_apply_apply _ _).symm

/-!
### The universal property is restriction to the thickenings
-/

variable (B : Type u) [CommRing B]

/-- **The affine-target universal property of `Spf R` is compatible with the thickening cocone**
(EGA I, 10.6.3): restricting a morphism `g : Spf R ⟶ Spec B` along the canonical morphism
`Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R` gives `Spec` of the reduction of `specHomEquiv I B g` modulo
`I ^ (n + 1)`. This is what makes the equivalence `specHomEquiv` — and hence its limit form
`specHomLimitEquiv` — the geometric statement "a morphism out of `Spf R` is a compatible system
of morphisms out of its infinitesimal thickenings", rather than an abstract bijection produced by
the `Γ ⊣ Spec` adjunction. -/
theorem thickeningMap_comp_specHom
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) (n : ℕ) :
    thickeningMap I n ≫ g =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom
        ((Ideal.Quotient.mk (I ^ (n + 1))).comp (specHomEquiv I B g))) := by
  refine hom_ext_toSpec B _ _ fun b => ?_
  have hl : ((thickeningMap I n ≫ g).c.app (op ⊤)).hom
      (@algebraMap B ((Spec.locallyRingedSpaceObj (CommRingCat.of B)).presheaf.obj (op ⊤)) _ _
        (StructureSheaf.openAlgebra (R := B) (op ⊤)) b) =
      ((thickeningMap I n).c.app (op ⊤)).hom ((g.c.app (op ⊤)).hom _) := rfl
  rw [hl, thickeningMap_c_app_top, ← specHomEquiv_apply I B g b]
  exact (StructureSheaf.toOpen_comp_comap_apply
    ((Ideal.Quotient.mk (I ^ (n + 1))).comp (specHomEquiv I B g)) ⊤ b).symm

/-- `thickeningMap_comp_specHom` read from the ring-homomorphism side: the morphism
`Spf R ⟶ Spec B` attached to `φ : B →+* R` restricts on the `n`-th thickening to `Spec` of the
reduction of `φ` modulo `I ^ (n + 1)`. -/
theorem thickeningMap_comp_specHomEquiv_symm (φ : B →+* R) (n : ℕ) :
    thickeningMap I n ≫ (specHomEquiv I B).symm φ =
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1))).comp φ)) := by
  rw [thickeningMap_comp_specHom, Equiv.apply_symm_apply]

/-- **A morphism out of `Spf R` into an affine scheme is determined by its restrictions to the
infinitesimal thickenings** — the uniqueness half of the description of `Spf R` as the colimit of
the `Spec (R ⧸ I ^ (n + 1))` (EGA I, 10.6.3). The proof is `thickeningMap_comp_specHom` plus
faithfulness of `Spec` and Hausdorffness of the `I`-adic topology on `R`. -/
theorem hom_ext_thickeningMap
    (g₁ g₂ : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (h : ∀ n : ℕ, thickeningMap I n ≫ g₁ = thickeningMap I n ≫ g₂) :
    g₁ = g₂ := by
  refine (specHomEquiv I B).injective (RingHom.ext fun b => ?_)
  -- the two ring homomorphisms agree modulo every power of `I`
  have hmod : ∀ n : ℕ, Ideal.Quotient.mk (I ^ (n + 1)) (specHomEquiv I B g₁ b) =
      Ideal.Quotient.mk (I ^ (n + 1)) (specHomEquiv I B g₂ b) := by
    intro n
    have hspec := (h n).symm.trans (thickeningMap_comp_specHom I B g₁ n)
    rw [thickeningMap_comp_specHom I B g₂ n] at hspec
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Quiver.Hom.op_inj (Spec.toLocallyRingedSpace.map_injective hspec.symm))) b
  -- Hausdorffness of the `I`-adic topology on `R` upgrades that to equality
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n => ?_
  rw [SModEq.sub_mem]
  have hmem : ∀ (m : ℕ) (z : R), z ∈ (I ^ m • ⊤ : Submodule R R) ↔ z ∈ I ^ m := by
    intro m z
    rw [Ideal.smul_top_eq_map (I ^ m), Submodule.restrictScalars_mem, Algebra.algebraMap_self,
      Ideal.map_id]
  refine (hmem n _).mpr (Ideal.Quotient.eq.mp ?_)
  cases n with
  | zero =>
    have htop : (I ^ 0 : Ideal R) = ⊤ := by rw [pow_zero]; exact Ideal.one_eq_top
    exact Ideal.Quotient.eq.mpr (by rw [htop]; trivial)
  | succ m => exact hmod m

section Nonvacuity

/-- The `2`-adic integers, with their ideal of definition, form a complete adic ring. -/
private theorem isAdicRing_twoAdicInt :
    IsAdicRing (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) :=
  AdicCompletion.isAdicRing_map _ (Submodule.fg_span (Set.finite_singleton _))

attribute [local instance] isAdicRing_twoAdicInt

/-- **The statements above are not vacuous, and not only for discrete rings.** The `2`-adic
integers `ℤ^` are a complete adic ring whose thickenings `Spec (ℤ^ ⧸ (2)ⁿ⁺¹)` are finite, hence
genuinely smaller than `Spf ℤ^`; restricting the canonical morphism `Spf ℤ^ ⟶ Spec ℤ` attached to
`ℤ → ℤ^` to the `n`-th thickening is `Spec` of the reduction of that map. -/
example (n : ℕ) :
    thickeningMap (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) n ≫
        (specHomEquiv (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})) ℤ).symm
          (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)) =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom
        ((Ideal.Quotient.mk
            (AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)}) ^ (n + 1))).comp
          (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)))) :=
  thickeningMap_comp_specHomEquiv_symm _ ℤ _ n

end Nonvacuity

end FormalSpectrum
