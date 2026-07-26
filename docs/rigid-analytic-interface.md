# Scope boundary and rigid-analytic interface (Tate curve)

*Issue 70. Companion to issues 64–69 (the Tate-curve prerequisite line).*

This note draws the boundary of the **formal-schemes** project around the Tate curve and
specifies, as an unambiguous checklist, the data a downstream **rigid-analytic** (Raynaud)
layer would consume from it. It is a scoping document, not a Lean deliverable: nothing here is
a theorem to prove inside this project. Its purpose is to let a future rigid-geometry
development — in this repository or a sibling project — attach cleanly to what has been built.

## 1. The mathematical picture, and where the cut falls

The Tate curve as an *elliptic curve* over a complete non-archimedean field `K` is obtained in
two stages:

1. **Formal model (in scope here).** Over the valuation ring `R` (`I`-adic, `I = (t)` with `t` a
   uniformizer), form the formal Tate annulus, the Tate chain `T`, its free properly
   discontinuous `q^ℤ`-action, and the quotient formal scheme `𝔈_q = T / q^ℤ`. This is a
   *compact* (circular) formal `R`-curve, glued from finitely many copies of the annulus.

2. **Generic fibre (out of scope here).** Apply Raynaud's functor `𝔉 ↦ 𝔉_rig` from admissible
   formal `R`-schemes to quasi-compact separated rigid `K`-spaces (Bosch, LNM 2105, Part C).
   Only after this step does one see the elliptic curve `E_q` and Tate's uniformization
   `E_q(K̄) ≅ K̄ˣ / q^ℤ`.

**The cut is exactly between stages 1 and 2.** Everything on the formal-`R`-scheme side of the
generic-fibre functor is in scope; the generic-fibre functor and everything it lands in (rigid
`K`-spaces, affinoids, admissible blow-ups) is out of scope.

### In scope (built in this project — issues 65–69)

| Object | Lean name | File |
| --- | --- | --- |
| Restricted power series `R{X₁,…,Xₙ}` (the `I`-adic completion of `R[X₁,…,Xₙ]`) | `RestrictedPowerSeries` | `RestrictedPowerSeries.lean` |
| tf-type `R`-algebras / affine formal schemes over `Spf R` | `IsTopologicallyFiniteType`, `IsAffineTopFiniteType` | `TopFiniteType.lean`, `GlobalTopFiniteType.lean` |
| Locally / relatively tf-type formal schemes | `IsLocallyTopFiniteType`, `IsRelativelyTopFiniteType` | `GlobalTopFiniteType.lean`, `RelativeTopFiniteType.lean` |
| Formal multiplicative group `Ĝm = Spf R{X, X⁻¹}` | `formalGm` | `FormalGm.lean` |
| Formal Tate annulus `A = R{x,y}/(x·y−q)` and `Spf A` | `annulusAlgebra`, `annulusIdealOfDefinition`, `annulusStructMap` | `TateAnnulus.lean` |
| The Tate chain `T → Spf R` (the `ℤ`-indexed chain of annuli) | `tateChain`, `tateChainStructMap` | `TateChainGlue.lean`, `TateChainStructMap.lean` |
| The free, properly discontinuous `q^ℤ`-action on `T` | `tatePeriodAction`, `tateShift_properlyDiscontinuous`, `tateShiftAut_zpow_eq_one_iff` | `TateAction.lean`, `TateFreenessAdjacent.lean` |
| **The Tate-curve formal model `𝔈_q = T/q^ℤ`** and its structural morphism | `tateCurveModel`, `tateCurveModelStructMap` | `TateCurveModel.lean` |

### Out of scope here (a separate rigid-geometry project)

- Tate algebras `K⟨X₁,…,Xₙ⟩` (in the *analytic*, normed sense) and affinoid `K`-algebras.
- Affinoid spaces `Sp(A)` and the Grothendieck topology of admissible opens.
- Admissible formal blowing-ups and Raynaud's localisation.
- **Raynaud's equivalence** between admissible formal `R`-schemes localised at blow-ups and
  quasi-compact quasi-separated rigid `K`-spaces.
- The **generic-fibre functor** `𝔉 ↦ 𝔉_rig` and the identification `(𝔈_q)_rig ≅ E_q`, together
  with the uniformization `E_q(K̄) ≅ K̄ˣ / q^ℤ`.

## 2. Interface specification (checklist for the rigid layer)

A future rigid-analytic layer building `E_q` and its uniformization would take the following from
this project. Each item is present today unless marked *(gap)*.

1. **The formal model as an object.** `tateCurveModel R I q hq hI : FormalScheme` — the glued
   (non-affine, compact) formal `R`-scheme `𝔈_q`. ✅
2. **Its affine charts as `Spf` of tf-type `R`-algebras.** The two patches are each
   `Spf (annulusIdealOfDefinition R I q)`, with `annulusAlgebra` tf-type over `(R, I)`
   (`annulus_isTopologicallyFiniteType`, `TateAnnulus.lean`). The gluing datum
   (`tateCurveFormalGlueData`) exposes the charts, the coproduct overlap
   `Spf A{1/x} ⨿ Spf A{1/y}`, and the summand-swap transition. ✅
3. **The structural morphism to the base.** `tateCurveModelStructMap : 𝔈_q ⟶ Spf R`. ✅
4. **The `q^ℤ`-descent data.** The action `tatePeriodAction : ℤ → Aut T` with freeness and proper
   discontinuity, the invariance of `tateChainStructMap` (`tateChainStructMap_isActionInvariant`,
   `TateActionQuotient.lean`), and the universal-property interface `IsActionQuotient`
   (`ActionQuotient.lean`). The two-chart `𝔈_q` realises this descent by hand; the general
   quotient `T/G` with `π : T ⟶ T/G` and a proof `IsActionQuotient (tatePeriodAction …) π` is
   issue 224 (interface merged, construction open). *(partial — see §4)*
5. **Admissibility / flatness of the formal model over `R`.** The rigid layer needs `𝔈_q` to be
   an *admissible* formal `R`-scheme: tf-type (✅, item 2) and `R`-flat / `t`-torsion-free
   (the annulus `R{x,y}/(xy−q)` is `R`-flat, but this is not recorded in the repo). *(gap)*
6. **Separatedness of `𝔈_q` over `Spf R`.** Needed for the generic fibre to be *separated*.
   Only the affine/patchwise content exists today (`AffineSeparated.lean`: `Δ_{A/R}` is a split
   mono and a base-closed embedding); the diagonal of the non-affine `𝔈_q` needs fibre products
   of general formal schemes (issue 191 line). This is issue 223 item 3. *(gap)*

Items 1–4 are the concrete geometric hand-off; items 5–6 are the two properties the rigid side
additionally requires and which are the natural remaining formal-scheme-side follow-ups.

## 3. State of Mathlib on the rigid side (survey)

As of the pinned Mathlib (`v4.32.0`), there is **no** rigid-analytic geometry to build on:

- **No** affinoid algebras, affinoid spaces, `Sp(A)`, admissible opens, or a rigid-space category.
- **No** Berkovich spaces or adic spaces (Huber).
- **No** admissible formal blow-ups or a Raynaud generic-fibre functor.
- The one adjacent item is `Mathlib.RingTheory.MvPowerSeries.Restricted`
  (`MvPowerSeries.IsRestricted`): a power series over a *normed* ring is restricted when
  `‖coeff t f‖ · ∏ cᵢ^{tᵢ} → 0` along the cofinite filter. This is the **analytic** (norm /
  Gauss-convergence) notion underlying Tate algebras `K⟨X⟩` — and is *distinct* from this
  project's `RestrictedPowerSeries`, which is the purely algebraic `I`-adic completion of
  `R[X]`. A rigid layer would connect the two (the generic fibre replaces the `I`-adic
  restriction over `R` with norm-restriction over `K`), but no such bridge exists in Mathlib.

**Recommendation for whoever picks up the rigid side.** Expect to build affinoid/Tate-algebra
theory essentially from scratch (starting from `MvPowerSeries.IsRestricted` over a
non-archimedean normed field `K = Frac R`), then the rigid-space category, then the Raynaud
functor. That is a large, self-contained project properly *downstream* of this one, not a
continuation of it. This project's job for the Tate curve ends at `𝔈_q` and its charts/descent
data (§2 items 1–4), plus the two admissibility/separatedness properties (§2 items 5–6) that make
`𝔈_q` a clean input to Raynaud's functor.

## References

- Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105, Part B §§7–9 (formal side, in scope)
  and Part C, §§10–13 (Raynaud's view on rigid spaces, out of scope here).
- Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V (Tate curve).
- EGA I, §10 (formal schemes); Stacks Project, Tag 0AKA ff. (admissible formal schemes).
