import FormalSchemes.IndScheme

set_option linter.style.header false

/-!
# The forward computation rule for the affine-target universal property

`FormalSchemes/IndScheme.lean` establishes the affine-target mapping-out universal property of the
formal spectrum, `FormalSpectrum.specHomEquiv : Hom_{LRS}(Spf R, Spec B) ≃ (B →+* R)`, together
with a computation rule for its inverse (`specHomEquiv_symm_apply`). This file supplies the
*forward* computation rule, `FormalSpectrum.specHomEquiv_apply`, expressing the value of
`specHomEquiv I B g` on `b : B` through the sheaf component `g.c.app (op ⊤)` of the morphism `g`,

```
specHomEquiv I B g b =
  globalSectionsEquiv I ((g.c.app (op ⊤)).hom (algebraMap B _ b)).
```

This mirrors `FormalSpectrum.globalSectionsMap_apply` (`FormalSchemes/SpfGamma.lean`) and provides a
`simp`-normal form completing the follow-up noted in the `IndScheme.lean` module docstring.

The proof unfolds `specHomEquiv` to the `Γ ⊣ Spec` adjunction `homEquiv` and reduces the sheaf
component using the Mathlib lemma
`AlgebraicGeometry.ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app`, which identifies
`algebraMap B _ ≫ (homEquiv g).c.app U` with `g.unop ≫ (Spf R).presheaf.map (homOfLE le_top).op`.
At `U = op ⊤` the presheaf map is the identity (`presheaf_map_top_le_top`), which yields the stated
formula.

## Main results

* `FormalSpectrum.presheaf_map_top_le_top`: the restriction map of a locally ringed space along
  `⊤ ≤ ⊤` is the identity.
* `FormalSpectrum.specHomEquiv_apply`: the forward computation rule for `specHomEquiv`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- The restriction map of the structure presheaf of a locally ringed space along the (unique)
inclusion `⊤ ≤ ⊤` is the identity: `homOfLE le_top` is the only endomorphism of `⊤` in the
preorder category of opens. -/
theorem presheaf_map_top_le_top (X : LocallyRingedSpace) :
    X.presheaf.map (homOfLE (le_top (a := (⊤ : Opens X)))).op = 𝟙 _ := by
  rw [Subsingleton.elim (homOfLE (le_top (a := (⊤ : Opens X)))) (𝟙 (⊤ : Opens X)), op_id]
  exact CategoryTheory.Functor.map_id _ _

/-- **Forward computation rule for `specHomEquiv`** (mirroring
`FormalSpectrum.globalSectionsMap_apply`): the ring homomorphism `specHomEquiv I B g : B →+* R`
associated to a morphism `g : Spf R ⟶ Spec B` sends `b : B` to `globalSectionsEquiv I` applied to
the image of `algebraMap B _ b` under the global-sections component `g.c.app (op ⊤)`. -/
@[simp]
theorem specHomEquiv_apply (B : Type u) [CommRing B]
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (b : B) :
    specHomEquiv I B g b =
      globalSectionsEquiv I
        ((g.c.app (op ⊤)).hom
          (@algebraMap B
            ((Spec.locallyRingedSpaceObj (CommRingCat.of B)).presheaf.obj (op ⊤)) _ _
            (StructureSheaf.openAlgebra (R := B) (op ⊤)) b)) := by
  set f := (Adjunction.homEquiv ΓSpec.locallyRingedSpaceAdjunction (locallyRingedSpaceObj I)
    (op (CommRingCat.of B))).symm g with hf
  have hg : (Adjunction.homEquiv ΓSpec.locallyRingedSpaceAdjunction (locallyRingedSpaceObj I)
      (op (CommRingCat.of B))) f = g := by
    rw [hf]
    exact Equiv.apply_symm_apply _ _
  -- The Mathlib crux: `algebraMap ≫ (homEquiv f).c.app U = f.unop ≫ (Spf R).presheaf.map …`.
  have hmath := ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app f (op ⊤)
  -- `erw` reduces `(op ⊤).unop` to `⊤` when matching `presheaf_map_top_le_top`.
  erw [presheaf_map_top_le_top, Category.comp_id] at hmath
  -- Rewrite `homEquiv f = g` into the crux equation to phrase it through `g.c.app (op ⊤)`.
  have hmath2 := hg ▸ hmath
  have hspec : specHomEquiv I B g = commRingHomEquiv I B f.unop := rfl
  rw [hspec, commRingHomEquiv_apply, ← hmath2]
  rfl

end FormalSpectrum
