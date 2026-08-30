import FormalSchemes.AdicOnSections
import FormalSchemes.SpfGammaSheafComponentArbCont
import FormalSchemes.RestrictedPowerSeries

set_option linter.style.header false

/-!
# The ideal-power spelling of adicity on a basic open

A continuity obligation on this tree is stated as `v ∈ K ^ m → F v ∈ L ^ m` for **ideals** `K`,
`L` — that is the shape `RingHom.mem_eqLocus_of_forall_sub_mem_pow`
(`FormalSchemes.AdicSubringComplete`), `Ideal.map_algebraMap_pow_le_comap`
(`FormalSchemes.AdicExtend`) and `Subring.IsAdicallyClosed` all consume. But the continuity
theorem this tree already has for the basic-open sheaf component,
`FormalSpectrum.arbSheafComponent_mem_pow` (`FormalSchemes.SpfGammaSheafComponentArbCont`), is
stated on the **`Submodule` filtration** `(I·R_g) ^ m • ⊤` over the localization, because that is
what its `Submodule.smul_induction_on` proof needs.

This file supplies the bridge between the two spellings and the corollaries the consumers want.
It proves no new continuity: every adicity statement below is the existing theorem rewritten.

## What was already on the tree

Both halves of the underlying mathematics are already merged, and this file reproves neither:

* `FormalSpectrum.awayCompletionHom_eq_restrict`
  (`FormalSchemes.SpfGammaSheafComponentArbComp`) — the structure-sheaf restriction
  `Γ(⊤) ⟶ Γ(D(g))`, read through `FormalSpectrum.globalSectionsEquiv` on the source and
  `FormalSpectrum.sectionsBasicOpenEquiv` on the target, **is**
  `FormalSpectrum.awayCompletionHom I g`.
* `FormalSpectrum.arbSheafComponent_mem_pow`
  (`FormalSchemes.SpfGammaSheafComponentArbCont`) — an arbitrary morphism's conjugated basic-open
  component is adically continuous once its global-sections map is.

## Main results

* `FormalSpectrum.mem_awayCompletionIdeal_pow_iff`: the spelling bridge — membership in the
  `m`-th power of `FormalSpectrum.awayCompletionIdeal` is membership in the `m`-th
  localization-level filtration step. Two rewrites, but it is the one that lets an ideal-shaped
  consumer meet a module-shaped producer.
* `FormalSpectrum.arbSheafComponent_pow_le_comap_pow` and
  `FormalSpectrum.arbSheafComponent_mem_awayCompletionIdeal_pow`: the ideal-power forms of
  `arbSheafComponent_mem_pow`, as an ideal containment and as a membership implication
  respectively.
* `FormalSpectrum.basicOpenChart_arbSheafComponent_mem_awayCompletionIdeal_pow`: the same for
  `FormalSpectrum.basicOpenChart`, with **no continuity hypothesis** — it is discharged by
  `FormalSpectrum.basicOpenChart_le_comap_globalSectionsMap`.
* `FormalSpectrum.sectionsBasicOpenHom`, `FormalSpectrum.sectionsBasicOpenIdeal` and
  `FormalSpectrum.map_sectionsBasicOpenHom`: the structural map `R → Γ(D(f), O_{Spf R})` and the
  ideal of definition of that section ring, on the **presheaf-section** spelling rather than on
  `FormalSpectrum.awayCompletion`. `map_sectionsBasicOpenHom` is the ideal form of
  `awayCompletionHom_eq_restrict`, and the basic-open analogue of
  `FormalSpectrum.map_awayCompletionHom`.

## What is *not* proved

* **Nothing here says an arbitrary morphism of formal spectra is adic on a basic open.** Every
  statement below carries the global-sections hypothesis `I ≤ J.comap (globalSectionsMap I J w)`
  as an explicit argument, except the `basicOpenChart` specialisation, where it is a theorem.
  Its **global-sections** case is recorded false in `FormalSchemes.AdicOnSections`' module
  docstring (issue 460); the basic-open case is not proved false here, and the hypothesis is
  carried rather than derived. (`FormalSchemes.OpenImmersionReflectsIdeal`'s module docstring
  records a counterexample to a *different* statement — the reflection
  `Ψ t ∈ L → awayCompletionHom J g t ∈ awayCompletionIdeal J g`, issue 480 — not to adicity.)
* **`FormalSpectrum.sectionsBasicOpenEquiv` is not shown to be a map of `R`-algebras.**
  `map_sectionsBasicOpenHom` is the ideal consequence, which is what the consumers need and is
  strictly weaker; no `AlgHom` structure is put on it.
* **Nothing here is applied to the Tate cluster.**
  `AlgebraicGeometry.IsTateInvNodeChartLegContinuous` (`FormalSchemes.TateInvNodeChartComplete`)
  is untouched: a `.c.app` of `annulusOverlapChart` (root namespace, **not** under
  `AlgebraicGeometry` — its file's `namespace FormalSpectrum` block closes before the
  declaration) is not a basic-open restriction, and it is not claimed here that it reduces
  to one.
* No claim is made about `FormalSpectrum.arbSheafComponent` being injective, surjective or
  bijective; that is `FormalSpectrum.bijective_arbSheafComponent`'s business
  (`FormalSchemes.OpenImmersionSheafComponentIso`) and is not used here.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4, §10.4.6, §10.12.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-!
### The spelling bridge
-/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `m`-th power of `awayCompletionIdeal` is the `m`-th localization-level filtration step.**
`FormalSpectrum.awayCompletionIdeal I g` is the extension of `I·R_g` along
`R_g → R{1/g}`, so its powers are the extensions of the powers, and
`Ideal.mem_map_pow_iff_mem_smul_top` (`FormalSchemes.RestrictedPowerSeries`) identifies those with
the `R_g`-module filtration Mathlib's adic API uses.

This is the bridge between the ideal-shaped consumers of continuity on this tree
(`RingHom.mem_eqLocus_of_forall_sub_mem_pow`, `Subring.IsAdicallyClosed`) and the module-shaped
producer `FormalSpectrum.arbSheafComponent_mem_pow`.

**This is the seventh instance of one general fact on this tree**, not a new one: the same
statement and the same two-rewrite proof already appear at six other rings, as
`AdicCompletion.mem_idealOfDefinition_pow_iff` (`FormalSchemes.Completion`),
`RestrictedPowerSeries.mem_idealOfDefinition_pow_iff` (`FormalSchemes.BaseChange`),
`RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff` (`FormalSchemes.FormalGm`),
`FormalGroupAlgebra.mem_idealOfDefinition_pow_iff` (`FormalSchemes.FormalTorus`),
`CompletedTensorProduct.mem_idealOfDefinition_pow_iff` (`FormalSchemes.CompletedTensor`) and
`mem_overlapIdeal_pow_iff` (`FormalSchemes.TateOverlap`, root namespace). The general form —
`x ∈ (K.map (algebraMap B A)) ^ n ↔ x ∈ (K ^ n • ⊤ : Submodule B A)` for any `B`-algebra `A` —
subsumes all seven and belongs beside `Ideal.mem_map_pow_iff_mem_smul_top` in
`FormalSchemes.RestrictedPowerSeries`; it is left to a follow-up because stating it there rebuilds
most of the tree. -/
theorem mem_awayCompletionIdeal_pow_iff (g : R) (m : ℕ) (x : awayCompletion I g) :
    x ∈ (awayCompletionIdeal I g) ^ m ↔
      x ∈ ((I.map (algebraMap R (Localization.Away g))) ^ m • ⊤ :
        Submodule (Localization.Away g) (awayCompletion I g)) := by
  rw [← Ideal.mem_map_pow_iff_mem_smul_top, Ideal.mem_smul_top_self_iff]

/-!
### Adicity on a basic open, in the ideal-power spelling
-/

section ArbSheafComponent

variable (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)

/-- **The ideal-power form of `FormalSpectrum.arbSheafComponent_mem_pow`**, which is the shape
`RingHom.mem_eqLocus_of_forall_sub_mem_pow` (`FormalSchemes.AdicSubringComplete`) consumes: a
continuity hypothesis on this tree is stated as `v ∈ K ^ m → F v ∈ L ^ m` for ideals, not as a
`Continuous`.

No new continuity is proved — this is `arbSheafComponent_mem_pow` after
`mem_awayCompletionIdeal_pow_iff`. The hypothesis is carried, not derived:
`FormalSchemes.AdicOnSections`' module docstring records that the *global-sections* case of the
unhypothesised statement is false (issue 460). -/
theorem arbSheafComponent_mem_awayCompletionIdeal_pow
    (hadic : I ≤ J.comap (globalSectionsMap I J w)) (m : ℕ) {v : awayCompletion I g}
    (hv : v ∈ (awayCompletionIdeal I g) ^ m) :
    arbSheafComponent I J w g v ∈
      (awayCompletionIdeal J (globalSectionsMap I J w g)) ^ m :=
  arbSheafComponent_mem_pow I J w g hadic m v
    ((mem_awayCompletionIdeal_pow_iff I g m v).mp hv)

/-- **The ideal-containment form of the previous theorem**, for callers that want a containment of
ideals rather than a membership implication. -/
theorem arbSheafComponent_pow_le_comap_pow
    (hadic : I ≤ J.comap (globalSectionsMap I J w)) (m : ℕ) :
    (awayCompletionIdeal I g) ^ m ≤
      ((awayCompletionIdeal J (globalSectionsMap I J w g)) ^ m).comap
        (arbSheafComponent I J w g) := fun _ hv =>
  arbSheafComponent_mem_awayCompletionIdeal_pow I J w g hadic m hv

end ArbSheafComponent

/-!
### The unconditional case: the affine basic-open chart
-/

section BasicOpenChart

variable (f : R) [IsAdicRing (awayCompletionIdeal I f)]

/-- **The basic-open chart's sheaf component on a basic open is adic, with no hypothesis beyond
the instances.** The global-sections hypothesis of
`arbSheafComponent_mem_awayCompletionIdeal_pow` is discharged by
`FormalSpectrum.basicOpenChart_le_comap_globalSectionsMap`, which is a theorem precisely because
`FormalSpectrum.basicOpenChart` is `Spf` of `FormalSpectrum.awayCompletionHom` — not because of
any general statement about open immersions, which would be false. -/
theorem basicOpenChart_arbSheafComponent_mem_awayCompletionIdeal_pow (g : R) (m : ℕ)
    {v : awayCompletion I g} (hv : v ∈ (awayCompletionIdeal I g) ^ m) :
    arbSheafComponent I (awayCompletionIdeal I f) (basicOpenChart I f) g v ∈
      (awayCompletionIdeal (awayCompletionIdeal I f)
        (globalSectionsMap I (awayCompletionIdeal I f) (basicOpenChart I f) g)) ^ m :=
  arbSheafComponent_mem_awayCompletionIdeal_pow I (awayCompletionIdeal I f) (basicOpenChart I f) g
    (basicOpenChart_le_comap_globalSectionsMap I f) m hv

end BasicOpenChart

/-!
### The section ring over a basic open, on the presheaf spelling
-/

section BasicOpen

variable (f : R)

/-- **The structural map `R → Γ(D(f), O_{Spf R})`**: restrict the global section attached to
`x : R` by `FormalSpectrum.globalSectionsEquiv` along the inclusion `D(f) ⊆ ⊤`.

The inclusion is spelled `homOfLE (le_top (a := basicOpen I f))`, matching
`FormalSpectrum.awayCompletionHom_eq_restrict`; every consumer has to match that spelling, so it
is fixed here once. -/
def sectionsBasicOpenHom :
    R →+* ((structureSheaf I).presheaf.obj (op (basicOpen I f)) : Type u) :=
  (((structureSheaf I).presheaf.map (homOfLE (le_top (a := basicOpen I f))).op).hom).comp
    (globalSectionsEquiv I).symm.toRingHom

/-- **`sectionsBasicOpenEquiv` carries the structural map to the structural map.** This is
`FormalSpectrum.awayCompletionHom_eq_restrict` restated with the composite named. -/
theorem sectionsBasicOpenEquiv_comp_sectionsBasicOpenHom :
    (sectionsBasicOpenEquiv I f).toRingHom.comp (sectionsBasicOpenHom I f) =
      awayCompletionHom I f :=
  (awayCompletionHom_eq_restrict I f).symm

/-- The ideal of definition of `Γ(D(f), O_{Spf R})`, on the presheaf-section spelling: the
contraction of `FormalSpectrum.awayCompletionIdeal` along
`FormalSpectrum.sectionsBasicOpenEquiv`. -/
def sectionsBasicOpenIdeal :
    Ideal ((structureSheaf I).presheaf.obj (op (basicOpen I f)) : Type u) :=
  (awayCompletionIdeal I f).comap (sectionsBasicOpenEquiv I f).toRingHom

/-- **The ideal form of `awayCompletionHom_eq_restrict`**: the extension of `I` along the
structural map `R → Γ(D(f))` is the ideal of definition of `Γ(D(f))`. The basic-open analogue of
`FormalSpectrum.map_awayCompletionHom`, and the statement a continuity obligation stated on the
presheaf spelling consumes — strictly weaker than "`sectionsBasicOpenEquiv` is an `R`-algebra
map", which is not proved here. -/
theorem map_sectionsBasicOpenHom :
    I.map (sectionsBasicOpenHom I f) = sectionsBasicOpenIdeal I f := by
  have hhom : sectionsBasicOpenHom I f =
      (sectionsBasicOpenEquiv I f).symm.toRingHom.comp (awayCompletionHom I f) := by
    rw [← sectionsBasicOpenEquiv_comp_sectionsBasicOpenHom I f, ← RingHom.comp_assoc]
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
  rw [hhom, ← Ideal.map_map, map_awayCompletionHom, sectionsBasicOpenIdeal]
  exact Ideal.map_symm (sectionsBasicOpenEquiv I f)

/-- **The structural map `R → Γ(D(f))` is adic**, the `Ideal.comap` form of
`map_sectionsBasicOpenHom` and the presheaf-spelling analogue of
`FormalSpectrum.le_comap_awayCompletionHom`. -/
theorem le_comap_sectionsBasicOpenHom :
    I ≤ (sectionsBasicOpenIdeal I f).comap (sectionsBasicOpenHom I f) :=
  Ideal.map_le_iff_le_comap.mp (map_sectionsBasicOpenHom I f).le

end BasicOpen

end FormalSpectrum

end
