# formal-schemes

A [Lean 4](https://leanprover.github.io/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **formal schemes**, following Grothendieck's *Éléments de géométrie algébrique*
(EGA I, Ch. 0 §7, §10 and Ch. I §10) and the corresponding
[Stacks project](https://stacks.math.columbia.edu/) chapters.

The development builds the affine theory from the ground up: adic rings and their ideals of
definition, the formal spectrum `Spf R` as a topological space, its structure sheaf `O_{Spf R}`
as an inverse limit of the structure sheaves of the infinitesimal thickenings `Spec (R ⧸ Iⁿ)`,
the computation of its sections and stalks, and the packaging of `(Spf R, O_{Spf R})` as a
locally ringed space — from which the notion of a formal scheme is defined.

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

The main results currently formalized are:

* **Global sections** recover the ring: `Γ(⊤, O_{Spf R}) ≃+* R` (EGA I, 10.1.3).
* **Sections on a basic open** `D(f)` are the `I`-adic completion of the localization `R_f`:
  `Γ(D(f), O_{Spf R}) ≃+* AdicCompletion (I·R_f) R_f` (EGA I, 10.1.4 / Stacks Tag 0AI7).
* **Stalks are local rings**, so `(Spf R, O_{Spf R})` is a locally ringed space (EGA I, 10.1.6).
* **Functoriality**: a continuous ring homomorphism `R → S` carrying `I` into `J` induces the
  underlying continuous map `Spf S ⟶ Spf R` together with a comparison morphism of structure
  sheaves `O_{Spf R} ⟶ (Spf φ)_* O_{Spf S}` (EGA I, 10.2.2); assembling these into a morphism of
  locally ringed spaces is in progress.
* **Formal schemes** are defined as locally ringed spaces locally isomorphic to some `Spf R`,
  and they form a category (EGA I, 10.4.2).

## Module map

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
| `FormalSchemes/SpfMap.lean` | Functoriality of `Spf`: the continuous map `Spf S ⟶ Spf R` (`mapTop`) and the induced morphism of structure sheaves `O_{Spf R} ⟶ (mapTop)_* O_{Spf S}` (`mapSheafHom`) from an adic ring homomorphism (EGA I, 10.2.2). |
| `FormalSchemes/FormalScheme.lean` | Formal schemes as locally ringed spaces locally isomorphic to some `Spf R`; the affine formal scheme `FormalScheme.Spf` (EGA I, 10.4.2 / Stacks Tag 0AIL). |

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0 §7, §10 and Ch. I §10.
* The Stacks Project, [Formal Schemes](https://stacks.math.columbia.edu/tag/0AHY)
  (Tags 07E7, 0AHZ, 0AI5, 0AI7, 0AIL ff.).
