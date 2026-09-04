import FormalSchemes.CofinalSheafComparison
import FormalSchemes.SpfGammaSheafComponentArbComp

set_option linter.style.header false

/-!
# Naturality of the ideal-independence section isos along the `⊤ → D(g)` restriction

For an adic ring `R` with two ideals of definition `I ≤ J` (both `IsAdicRing`, `J` cofinal in `I`
via `J ^ a ≤ I`), `FormalSchemes/CofinalSheafComparison.lean` produces, ideal-by-ideal, the
ring-of-sections comparison isomorphisms `FormalSpectrum.globalSectionsComparison` (on the global
open `⊤`) and `FormalSpectrum.basicOpenSectionsComparison` (on a basic open `D(g)`), both recovering
the same completed localization independently of the chosen ideal of definition.

This file proves the first naturality square those pointwise isomorphisms must satisfy in order to
glue into a single sheaf isomorphism: the square relating the two comparisons with respect to the
**structure-sheaf restriction along the inclusion `D(g) ⊆ ⊤`** commutes, i.e.

```
Γ(⊤, O_I) --globalSectionsComparison--> Γ(⊤, O_J)
   |                                        |
 restrict ⊤→D(g)                         restrict ⊤→D(g)
   v                                        v
Γ(D(g), O_I) --basicOpenSectionsComparison--> Γ(D(g), O_J)
```

This is piece (a) of the deferred goal-1 sheaf-iso roadmap named in the docstring of
`CofinalSheafComparison.lean`. The proof consumes the merged locality-free identity
`FormalSpectrum.awayCompletionHom_eq_restrict` (which reads the `⊤ → D(g)` restriction, through
`globalSectionsEquiv`/`sectionsBasicOpenEquiv`, as the completed-localization structure map
`awayCompletionHom I g : R → R{1/g}`), together with a ring-level crux: the cofinal comparison map
`AdicCompletion.cofinalHom` fixes the structure map `AdicCompletion.of`, hence intertwines the two
`awayCompletionHom`s.

We honestly note that the fully general **basis-restriction** naturality (for an arbitrary basic
inclusion `D(g) ⊆ D(f)`, needed for the complete sheaf gluing over the whole distinguished basis)
remains a follow-up. Only the `f = 1`, i.e. `⊤ → D(g)`, case is settled here, and it is settled by
`awayCompletionHom_eq_restrict`, to which the general case does **not** reduce: there is no
canonical ring map `R_f → R_g` for a general `D(g) ⊆ D(f)`, since the inclusion is a condition on
residues modulo `I` and does not put `g` in the radical of `f`.

**The absence of `R_f → R_g` is not itself the obstruction, and this paragraph used to suggest that
it was.** After completing, the map does exist: `FormalSpectrum.awayCompletionRestrict`
(`FormalSchemes.AwayCompletionRestrict`) is a canonical `R{1/f} →+* R{1/g}` for any
`basicOpen I g ≤ basicOpen I f`, because `f` becomes a unit modulo `I·R_g` and hence in the complete
ring `R{1/g}`. **The identification of the structure-sheaf restriction with it is landed too**, and
an intermediate version of this paragraph called it still open: the restriction is named,
conjugated by `sectionsBasicOpenEquiv`, as `FormalSpectrum.basicOpenRes`
(`FormalSchemes.BasicOpenRestriction`), and
`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`
(`FormalSchemes.BasicOpenRestrictionIdentification`) equates the two for `I` finitely generated. So
the basis-restriction naturality this paragraph opened is no longer blocked on a ring map: what
remains of it is the naturality square itself, not the identification of its right-hand edge.
Note also that `FormalSpectrum.awayCompletionAwayEquiv`, which this paragraph used to name as
the tool the general case requires, assumes `f` is already a unit in `Localization.Away g` — the
strictly stronger *scheme*-theoretic hypothesis — so it does not apply to a general basic inclusion
of `Spf R`.

## Main results

* `FormalSpectrum.cofinalHom_comp_awayCompletionHom`: the ring-level crux — `cofinalHom` intertwines
  the source and target completed-localization structure maps `awayCompletionHom I g`,
  `awayCompletionHom J g`.
* `FormalSpectrum.basicOpenSectionsComparison_comp_restrict_top`: the `⊤ → D(g)` naturality square.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

/-- **Ring-level crux of the `⊤ → D(g)` naturality square.** For two ideals of definition `I ≤ J`,
the cofinal comparison map on the away-completions of `R{1/g}` intertwines the two completed
localization structure maps: `cofinalHom ∘ awayCompletionHom I g = awayCompletionHom J g`. This is
because `awayCompletionHom I g r` is, by definition, `of (I·R_g) R_g (algebraMap R R_g r)`, which
`cofinalHom` carries to `of (J·R_g) R_g (algebraMap R R_g r) = awayCompletionHom J g r`. -/
theorem cofinalHom_comp_awayCompletionHom {R : Type u} [CommRing R]
    [TopologicalSpace R] (I J : Ideal R) [IsAdicRing I] [IsAdicRing J]
    (hIJ : I ≤ J) (g : R) :
    (AdicCompletion.cofinalHom (b := 1)
        (show (I.map (algebraMap R (Localization.Away g))) ^ 1 ≤
              J.map (algebraMap R (Localization.Away g)) by
          rw [pow_one]; exact Ideal.map_mono hIJ)).comp (awayCompletionHom I g) =
      awayCompletionHom J g := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply,
    show awayCompletionHom I g r =
        AdicCompletion.of (I.map (algebraMap R (Localization.Away g))) (Localization.Away g)
          (algebraMap R (Localization.Away g) r) from rfl,
    AdicCompletion.cofinalHom_of,
    show awayCompletionHom J g r =
        AdicCompletion.of (J.map (algebraMap R (Localization.Away g))) (Localization.Away g)
          (algebraMap R (Localization.Away g) r) from rfl]

/-- **The `⊤ → D(g)` naturality square of the ideal-independence section isomorphisms.** For two
ideals of definition `I ≤ J` with `J` cofinal in `I` (`J ^ a ≤ I`), the basic-open comparison on
`D(g)` and the global-sections comparison on `⊤` are compatible with the structure-sheaf restriction
along `D(g) ⊆ ⊤`: restricting first and then applying `basicOpenSectionsComparison` agrees with
applying `globalSectionsComparison` first and then restricting. -/
theorem basicOpenSectionsComparison_comp_restrict_top
    {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
    [IsAdicRing I] [IsAdicRing J] (hIJ : I ≤ J) {a : ℕ} (hcof : J ^ a ≤ I) (g : R) :
    (basicOpenSectionsComparison I J hIJ hcof g).toRingHom.comp
        ((structureSheaf I).presheaf.map (homOfLE (le_top (a := basicOpen I g))).op).hom =
      (((structureSheaf J).presheaf.map (homOfLE (le_top (a := basicOpen J g))).op).hom).comp
        (globalSectionsComparison I J).toRingHom := by
  refine RingHom.ext fun x => ?_
  -- Source-side: the `⊤ → D(g)` restriction of `x`, read through `sectionsBasicOpenEquiv I g`, is
  -- the completed-localization structure map applied to `globalSectionsEquiv I x`.
  have hI : sectionsBasicOpenEquiv I g
        (((structureSheaf I).presheaf.map (homOfLE (le_top (a := basicOpen I g))).op).hom x) =
      awayCompletionHom I g (globalSectionsEquiv I x) := by
    have h := RingHom.congr_fun (awayCompletionHom_eq_restrict I g) (globalSectionsEquiv I x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] at h
    exact h.symm
  -- Target-side: the `⊤ → D(g)` restriction of `(globalSectionsEquiv J).symm (globalSectionsEquiv
  -- I x)` is `(sectionsBasicOpenEquiv J g).symm` of the completed-localization structure map.
  have hJ : ((structureSheaf J).presheaf.map (homOfLE (le_top (a := basicOpen J g))).op).hom
        ((globalSectionsEquiv J).symm (globalSectionsEquiv I x)) =
      (sectionsBasicOpenEquiv J g).symm (awayCompletionHom J g (globalSectionsEquiv I x)) := by
    have h := RingHom.congr_fun (awayCompletionHom_eq_restrict J g) (globalSectionsEquiv I x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
    rw [h, RingEquiv.symm_apply_apply]
  -- Ring-level crux: `cofinalHom` intertwines the two `awayCompletionHom`s at `globalSectionsEquiv
  -- I x`.
  have hcru := RingHom.congr_fun
    (cofinalHom_comp_awayCompletionHom I J hIJ g) (globalSectionsEquiv I x)
  rw [RingHom.comp_apply] at hcru
  -- Pointwise formulas for the two comparison isomorphisms (definitional).
  have hbo (z : (structureSheaf I).presheaf.obj (op (basicOpen I g))) :
      basicOpenSectionsComparison I J hIJ hcof g z =
        (sectionsBasicOpenEquiv J g).symm
          (AdicCompletion.cofinalHom (b := 1)
            (show (I.map (algebraMap R (Localization.Away g))) ^ 1 ≤
                  J.map (algebraMap R (Localization.Away g)) by
              rw [pow_one]; exact Ideal.map_mono hIJ)
            (sectionsBasicOpenEquiv I g z)) :=
    rfl
  have hgo (z : (structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))) :
      globalSectionsComparison I J z =
        (globalSectionsEquiv J).symm (globalSectionsEquiv I z) :=
    rfl
  -- Assemble both composites into nested applications and rewrite.
  rw [RingHom.comp_apply, RingHom.comp_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [hbo, hgo, hI, hcru, hJ]

end FormalSpectrum

end
