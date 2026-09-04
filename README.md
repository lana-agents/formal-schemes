# formal-schemes

A [Lean 4](https://leanprover.github.io/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **formal schemes**, following Grothendieck's *Éléments de géométrie algébrique*
(EGA I, Ch. 0 §7, §10 and Ch. I §10) and the corresponding
[Stacks project](https://stacks.math.columbia.edu/) chapters.

The development builds the affine theory from the ground up: adic rings and their ideals of
definition, the formal spectrum `Spf R` as a topological space, its structure sheaf `O_{Spf R}`
as an inverse limit of the structure sheaves of the infinitesimal thickenings `Spec (R ⧸ Iⁿ)`,
the computation of its sections and stalks, and the packaging of `(Spf R, O_{Spf R})` as a
locally ringed space — from which the notion of a formal scheme is defined. It then leaves the
affine case: formal schemes are glued from affine charts, completed along a closed subset of an
ambient scheme, made topologically of finite type and separated, multiplied over an adic base,
quotiented by group actions, and specialised to a formal model of the Tate curve.

## Building

This project depends on Mathlib (pinned in `lakefile.toml`). To build:

```sh
lake exe cache get   # fetch the Mathlib build cache
lake build           # build the FormalSchemes library
```

## Overview

Fix an *adic ring* `R` with *ideal of definition* `I` — a topological ring whose topology is the
`I`-adic topology and which is complete and Hausdorff for it (`IsAdicRing`). The **formal
spectrum** `Spf R` is the topological space `Spec (R ⧸ I)`, i.e. the closed subset of `Spec R`
cut out by `I`, equipped with the structure sheaf

```
O_{Spf R}  :=  limₙ  O_{Spec (R ⧸ I^(n+1))}
```

the inverse limit, transported to `Spf R`, of the structure sheaves of the *infinitesimal
thickenings* `Spec (R ⧸ I^(n+1))`. Following Mathlib's conventions this is treated as a sheaf of
plain commutative rings; the topological (adic) structure of EGA is recovered through the explicit
limit description of the sections.

### The affine theory

* **Global sections** recover the ring: `Γ(⊤, O_{Spf R}) ≃+* R` (EGA I, 10.1.3) —
  `FormalSpectrum.globalSectionsEquiv`.
* **Sections on a basic open** `D(f)` are the `I`-adic completion of the localization `R_f`:
  `Γ(D(f), O_{Spf R}) ≃+* AdicCompletion (I·R_f) R_f` (EGA I, 10.1.4 / Stacks Tag 0AI7) —
  `FormalSpectrum.sectionsBasicOpenEquiv`.
* **Stalks are local rings** (`FormalSpectrum.isLocalRing_structureSheaf_stalk`), so
  `(Spf R, O_{Spf R})` is a locally ringed space, `FormalSpectrum.locallyRingedSpaceObj`
  (EGA I, 10.1.6).
* **Functoriality**: a ring homomorphism `R → S` carrying `I` into `J` induces a **morphism of
  locally ringed spaces** `Spf S ⟶ Spf R` (EGA I, 10.2.2) — `FormalSpectrum.locallyRingedSpaceMap`,
  built from the underlying continuous map `FormalSpectrum.mapTop` and the comparison morphism of
  structure sheaves `FormalSpectrum.mapSheafHom`. At an adic homomorphism it is
  `IsAdicHom.spfMap`.
* **`Spf R` does not depend on the ideal of definition**: two ideals of definition of the same
  adic ring give isomorphic formal spectra (EGA I, 10.3) —
  `FormalSpectrum.generalCofinalSpfIso`.
* **Formal schemes** are defined as locally ringed spaces locally isomorphic to some `Spf R`,
  and they form a category (EGA I, 10.4.2); the affine ones are
  `AlgebraicGeometry.FormalScheme.Spf`.

### Beyond the affine case

One declaration per statement, chosen to be the entry point rather than to be complete: this list
is representative, and `FormalSchemes.lean` is the only exhaustive index of the library.

* **Gluing**: formal schemes glue from affine charts along open immersions —
  `AlgebraicGeometry.FormalScheme.GlueData`.
* **The colimit property** (EGA I, 10.6.10): a morphism `Spf R ⟶ X` into a formal scheme is
  determined by, and assembled from, its restrictions to the thickenings —
  `FormalSpectrum.existsUnique_hom_thickeningMap_formalScheme`.
* **Formal completion along a closed subset** (EGA I, 10.8): for an affine ambient scheme,
  `formalCompletion R I` is the completion of `Spec R` along `V(I)`. For a scheme presented by
  affine charts it is `AlgebraicGeometry.ChartedCompletionDatum.completionGlued`, with
  `AlgebraicGeometry.ChartedCompletionDatum.toScheme` the canonical morphism `X_{/Y} ⟶ X`.
* **Topologically finite type** (EGA I, 10.13): the property `IsTopologicallyFiniteType`, its
  affine-local character, and the composition law
  `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.trans`.
* **Closed immersions and separatedness** (EGA I, 10.14–10.15):
  `AlgebraicGeometry.FormalScheme.IsClosedImmersion` and
  `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`, the latter through the diagonal of a
  formal scheme over an affine adic base.
* **Fibre products** over an affine adic base, built from the completed tensor product of the
  chart algebras — `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct`.
* **Quotients by a free, properly discontinuous action** of a discrete group, as a formal scheme —
  `AlgebraicGeometry.LocallyRingedSpace.freeActionQuotientFormalScheme`.
* **A formal model of the Tate curve**: `AlgebraicGeometry.tateCurveModel`, the two-chart circular
  quotient of the formal annulus, separated and relatively topologically of finite type over
  `Spf R` (`AlgebraicGeometry.tateCurveModel_isSeparatedOverSpf_and_isRelativelyTopFiniteType`).
  **Its period is `q²`, not `q`.** The parameter it is built from is a square root of the period:
  the object is a Néron 2-gon, and the symbol `𝔈_q` used throughout the library denotes it rather
  than the curve of period `q`. The period-`q` quotient is not reachable by the quotient
  construction above, because the one-patch shift is not properly discontinuous —
  `AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`.
  `FormalSchemes/TateCurveModel.lean` gives two independent derivations of the period.

## Module map: the affine core

`FormalSchemes.lean` imports the whole library — **500 modules** at commit `0bfe6b5`. The table
below is the twelve the library consisted of when this map was first written, and they are still
where the construction above lives and still the place to start reading; it is a sample of the
library, not an index of it.

| File | Contents |
| --- | --- |
| `FormalSchemes/AdicRing.lean` | Adic rings and ideals of definition (`IsAdicRing`); characterization via completeness and Hausdorffness (EGA I, Ch. 0 §7 / Stacks Tag 07E7). |
| `FormalSchemes/FormalSpectrum.lean` | The topological space `Spf R = Spec (R ⧸ I)`, its closed embedding into `Spec R`, functoriality (`FormalSpectrum.map`), and the fact that it is a spectral space. |
| `FormalSchemes/StructureSheaf.lean` | The thickening sheaves `thickeningSheaf I n` and the structure sheaf `O_{Spf R}` as the limit of their inverse system (Stacks Tag 0AI5). |
| `FormalSchemes/StructureSheafSections.lean` | Level-`n` identification of the sections of the thickening sheaves over basic opens. |
| `FormalSchemes/LocalizationQuotient.lean` | Crux lemma: localization commutes with quotient, `Localization.Away (mk K f) ≃+* (Localization.Away f) ⧸ K·A`. |
| `FormalSchemes/AdicCompletionLimit.lean` | The adic completion as the limit of its quotient tower `n ↦ R ⧸ Iⁿ` (`AdicCompletion.limitRingEquiv`). |
| `FormalSchemes/Sections.lean` | Sections of `O_{Spf R}`: `Γ(D(f), -) ≃+* AdicCompletion (I·R_f) R_f` and `Γ(⊤, -) ≃+* R` (EGA I, 10.1.3–10.1.4). |
| `FormalSchemes/GermValue.lean` | Germs of structure-sheaf sections versus their values at points, used for the stalk analysis. |
| `FormalSchemes/LimitUnits.lean` | In a limit of commutative rings, an element all of whose projections are units is itself a unit — the mechanism by which invertibility propagates through `O_{Spf R}`. |
| `FormalSchemes/Spf.lean` | Stalks of `O_{Spf R}` are local rings (EGA I, 10.1.6); `(Spf R, O_{Spf R})` as a `SheafedSpace` / `LocallyRingedSpace`. |
| `FormalSchemes/SpfMap.lean` | Functoriality of `Spf`: the continuous map `mapTop`, the induced morphism of structure sheaves `mapSheafHom`, and the morphism of locally ringed spaces `locallyRingedSpaceMap` they assemble into (EGA I, 10.2.2). |
| `FormalSchemes/FormalScheme.lean` | Formal schemes as locally ringed spaces locally isomorphic to some `Spf R`; the affine formal scheme `FormalScheme.Spf` (EGA I, 10.4.2 / Stacks Tag 0AIL). |

### The rest of the library, by theme

Representative modules only — each theme spans many more. Import `FormalSchemes` and use the
declaration names above to find the rest.

| Theme | Where to start |
| --- | --- |
| Adic algebra: morphisms, cofinal ideals, restricted power series | `FormalSchemes/AdicMorphism.lean`, `FormalSchemes/CofinalAdicRing.lean`, `FormalSchemes/RestrictedPowerSeries.lean` |
| Mapping into a formal scheme; the colimit property | `FormalSchemes/SpfHomOfFamily.lean`, `FormalSchemes/SpfHomFormalScheme.lean` |
| Gluing, charted presentations of schemes and formal schemes | `FormalSchemes/Gluing.lean`, `FormalSchemes/ChartedSchemeDatum.lean` |
| Formal completion of a scheme along a closed subset (EGA I, 10.8) | `FormalSchemes/Completion.lean`, `FormalSchemes/ChartedCompletionDatum.lean`, `FormalSchemes/ChartedCompletionToScheme.lean`, `FormalSchemes/ProjectiveLineCompletion.lean` |
| Finite type, closed immersions, separatedness (EGA I, 10.13–10.15) | `FormalSchemes/TopFiniteType.lean`, `FormalSchemes/TopFiniteTypeHomTrans.lean`, `FormalSchemes/ClosedImmersion.lean`, `FormalSchemes/GeneralSeparatedScheme.lean` |
| Completed tensor products and fibre products | `FormalSchemes/CompletedTensor.lean`, `FormalSchemes/GeneralFibreProductBothObject.lean` |
| Group actions and their quotients | `FormalSchemes/ActionQuotient.lean`, `FormalSchemes/FreeActionQuotientFormalScheme.lean` |
| The Tate annulus, the Tate chain and the Tate curve model | `FormalSchemes/TateAnnulus.lean`, `FormalSchemes/TateChainGlue.lean`, `FormalSchemes/TateCurveModel.lean`, `FormalSchemes/TateSeparatedScheme.lean` |

## Conventions and further documents

* `CONTRIBUTING.md` — the docstring citation convention this library is written to, and the line
  width rule. `scripts/citation_audit.py` is the instrument that enforces the mechanical half.
* `docs/signature-census-concl.md` — a census of the library's duplicate statements, by conclusion,
  with the repairs each finding received.
* `docs/rigid-analytic-interface.md` — the interface to the rigid-analytic generic fibre, which is
  out of scope for this project.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0 §7, §10 and Ch. I §10.
* The Stacks Project, [Formal Schemes](https://stacks.math.columbia.edu/tag/0AHY)
  (Tags 07E7, 0AHZ, 0AI5, 0AI7, 0AIL ff.).
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105 — the
  reference the Tate half of this library follows (Part B, §9).
