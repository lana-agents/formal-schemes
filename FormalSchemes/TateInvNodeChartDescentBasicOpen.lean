import FormalSchemes.TateInvNodeChartDescentIso
import FormalSchemes.BasicOpenSectionsHom

set_option linter.style.header false

/-!
# The sheaf half of hypothesis 4 is a family of ring maps indexed by the node chart's ring

`FormalSchemes/TateInvNodeChartDescentIso.lean` (issue 1730) reduced hypothesis 4 of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` to one isomorphism at a canonical
comparison and split it in two:

> hypothesis 4 ⟺ `IsIso (nodeChartQuotientHom …).base` **and**
> `∀ O, IsIso ((nodeChartQuotientHom …).c.app O)`

(`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_c`, a two-way equivalence). This file
rewrites the second conjunct. It does **not** decide it, and it does not touch the first.

## What comes off

The target of the comparison is `Spf (tateInvNodeChartQuotientIdeal …)`, whose basic opens are a
basis of its topology (`FormalSpectrum.isBasis_basicOpen`), and a morphism of sheaves is invertible
as soon as it is on a basis. So the `∀ O` is a `∀ g`, indexed by the ring
`Γ (T_inv/⟨σ⟩, V₀)` itself; and over `D(g)` the sections of the structure sheaf are the completed
localization `FormalSpectrum.awayCompletion` (EGA I, 10.1.4), so each member of the family is a
plain ring homomorphism. Combining
`FormalSpectrum.isIso_c_app_iff_bijective_basicOpenSectionsHom`
(`FormalSchemes.BasicOpenSectionsHom`) with the reduction above:

> hypothesis 4 ⟺ the base map is an isomorphism **and** for every
> `g : Γ (T_inv/⟨σ⟩, V₀)` the ring homomorphism
> `FormalSpectrum.basicOpenSectionsHom … (nodeChartQuotientHom …) g` is **bijective**

(`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_bijective`). The source of each of
those homomorphisms is `awayCompletion (tateInvNodeChartQuotientIdeal …) g` — a completed
localization of the invariant-sections ring, with no sheaf, no open and no category in it.

## Both halves of the sheaf half move to the chain

The target of `basicOpenSectionsHom … (nodeChartQuotientHom …) g` is
`Γ ((T_inv/⟨σ⟩)|_{V₀}, (nodeChartQuotientHom …)⁻¹ D(g))`, which is not computable as it stands. But
`AlgebraicGeometry.restrictπ_comp_nodeChartQuotientHom` factors
`AlgebraicGeometry.nodeChartAdicHom` through it, and the restricted projection is a quotient
projection, so both halves of bijectivity move to the chain:

* **injectivity** transfers outright, because a quotient projection is injective on sections at
  every open (`CategoryTheory.IsActionQuotient.injective_c_app`) —
  `AlgebraicGeometry.injective_basicOpenSectionsHom_nodeChartAdicHom_iff`;
* **surjectivity** becomes "every invariant section is reached", because the image of that
  projection's comparison map at an arbitrary open is exactly the invariant sections
  (`AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_isInvariantSection'`,
  added to `FormalSchemes.ActionQuotientRestrictQuotient` for this) —
  `AlgebraicGeometry.surjective_basicOpenSectionsHom_nodeChartQuotientHom_iff`.

Putting the three together (`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_chain`):

> hypothesis 4 ⟺ the base map of `nodeChartQuotientHom` is an isomorphism, **and** for every
> `g : Γ (T_inv/⟨σ⟩, V₀)` the ring homomorphism
> `awayCompletion (tateInvNodeChartQuotientIdeal …) g ⟶`
> `Γ (T_inv|_{π⁻¹V₀}, (nodeChartAdicHom …)⁻¹ D(g))` is injective with image the sections
> invariant under `AlgebraicGeometry.tateInvNodeChartRestrictedAction`

**What that costs and what it does not, read off the type Lean prints** for
`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_chain` rather than off the source. The
second conjunct mentions no `CategoryTheory.IsActionQuotient`, no
`CategoryTheory.IsActionQuotient.desc` and **not** `AlgebraicGeometry.nodeChartQuotientHom`: the
morphism out of the quotient survives only in the first conjunct. It does mention
`CategoryTheory.actionQuotient`, exactly once, in the type of the index variable `g` — the family
is indexed by `Γ (T_inv/⟨σ⟩, V₀)`, which is the ring hypothesis 4 is about and cannot be traded
away — and it mentions `AlgebraicGeometry.tateInvNodeChartRestrictedAction`, the action restricted
to the preimage of `V₀`, in the invariance condition. The space the sections live on is
`AlgebraicGeometry.tateChainInv` restricted to that preimage.

## What still does not come off, and it is the point of this file to say so

**The open does not.** Both the source-side `D(g)` and the target-side preimage are honest, but the
preimage is taken along the base map of `AlgebraicGeometry.nodeChartAdicHom`, and the only
description of that morphism on points is chart-by-chart with
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` a `Classical.choice`. So a *concrete*
computation of either clause at a proper `g` needs the same handle the space half needs.

**The quotient does not disappear, only the morphism out of it does.** See the paragraph above for
what the elaborated statement still contains; a reading of these files that says the sheaf half no
longer mentions `T_inv/⟨σ⟩` is wrong.

**So the two conjuncts of `AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_c` are
separate statements but not independent problems.** That is a reading of what is present and not a
theorem; check it against the statements below rather than take it.

## What is *not* proved here

**`hnode` is undecided, in both directions, and nothing here moves it.** Every statement below is
a restatement of hypothesis 4 and inherits everything
`FormalSchemes.TateInvNodeChartDescentIso`'s `## What is *not* proved here` records: in
particular, **refuting hypothesis 4 would not refute `hnode`**, because the hypothesis of
`AlgebraicGeometry.exists_formalScheme_of_isIso_desc` is existential while hypothesis 4 is that
condition at a *named* morphism, and the chain onward through
`AlgebraicGeometry.exists_formalScheme_of_iso_restrict_tateInvNodeChartQuotientOpens` is one-way
as well.

**Hypothesis 4 is undecided in both directions.** No `g` is exhibited at which the comparison
fails, and no argument that none exists is given. The one member that is discharged is `g = 1`, by
`FormalSpectrum.basicOpen_one` out of a `⊤` statement that was already there.

**Neither clause of the chain form is computed at any `g ≠ 1`.** The injectivity clause and the
invariant-image clause are restatements, obtained from general facts about quotient projections;
no property of the node locus, the annulus algebras or the `σ`-action is used anywhere below, and
none is established.

**Nothing about the space half.** `IsIso (nodeChartQuotientHom …).base` is not addressed; no
declaration below mentions it except as a conjunct carried through from
`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_c`.

**No computation of `Γ (T_inv/⟨σ⟩, U)` at a proper open `U`.**
`FormalSchemes.TateInvNodeChartQuotientOpen` performs that computation at `V₀` only
(`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv`), and nothing here extends it.

**Nothing here bears on `AlgebraicGeometry.tateInvNodeChartAmbientHom`**, whose refutation as an
open immersion (`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top`) is
untouched.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.4, §10.6.
* [Deligne–Rapoport], II.1.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable [TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
  (op (tateInvNodeChartQuotientOpens R I q hq hI)))]
variable [IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI)]
variable (hfgI : (tateInvNodeChartQuotientIdeal R I q hq hI).FG)
variable (hX : FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
  (nodeChartPsi R I q hq hI))

/-! ### The `∀ O` is a `∀ g` -/

/-- **The sheaf half of hypothesis 4, on the basic opens.** Every comparison map of
`AlgebraicGeometry.nodeChartQuotientHom` is invertible exactly when the one at `D(g)` is, for every
`g` in the node chart's ring.

`FormalSpectrum.isIso_c_app_iff_basicOpen` (`FormalSchemes.BasicOpenSectionsHom`), which is
`AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_iff_isBasis` at
`FormalSpectrum.isBasis_basicOpen`. The index type of the family is
`Γ (T_inv/⟨σ⟩, V₀)` itself. -/
theorem isIso_c_app_nodeChartQuotientHom_iff_basicOpen :
    (∀ g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
        (op (tateInvNodeChartQuotientOpens R I q hq hI)),
      IsIso ((nodeChartQuotientHom R I q hq hI hfgI hX).c.app
        (op (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g)))) ↔
      ∀ O : (Opens (FormalSpectrum (tateInvNodeChartQuotientIdeal R I q hq hI)))ᵒᵖ,
        IsIso ((nodeChartQuotientHom R I q hq hI hfgI hX).c.app O) :=
  isIso_c_app_iff_basicOpen _ _ (nodeChartQuotientHom R I q hq hI hfgI hX)

/-! ### Hypothesis 4 with the sheaf half written out -/

/-- **Hypothesis 4 as a base map and a family of ring homomorphisms.** The descent of
`AlgebraicGeometry.nodeChartAdicHom` is an isomorphism exactly when

* the base map of `AlgebraicGeometry.nodeChartQuotientHom` is an isomorphism, and
* for every `g : Γ (T_inv/⟨σ⟩, V₀)` the ring homomorphism
  `FormalSpectrum.basicOpenSectionsHom … g`, whose source is the completed localization
  `awayCompletion (tateInvNodeChartQuotientIdeal …) g`, is **bijective**.

`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_c` with its second conjunct rewritten
by `FormalSpectrum.isIso_c_app_iff_bijective_basicOpenSectionsHom`. The equivalence is two-way, so
a single `g` at which that homomorphism fails to be bijective refutes hypothesis 4 — it would not
refute `hnode`; see the module docstring.

The source of each member is a completed localization of a ring and nothing else. The **target**
is `Γ ((T_inv/⟨σ⟩)|_{V₀}, f⁻¹ D(g))`, whose open is a preimage along the base map of the first
conjunct, so the two conjuncts are not independent problems. -/
theorem isIso_desc_nodeChartAdicHom_iff_base_and_bijective :
    IsIso ((isActionQuotient_actionQuotientπ (tateInvNodeChartRestrictedAction R I q hq hI)).desc
        (nodeChartAdicHom R I q hq hI hfgI hX)
        (isActionInvariant_nodeChartAdicHom R I q hq hI hfgI hX)) ↔
      IsIso (nodeChartQuotientHom R I q hq hI hfgI hX).base ∧
        ∀ g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
            (op (tateInvNodeChartQuotientOpens R I q hq hI)),
          Function.Bijective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
            (nodeChartQuotientHom R I q hq hI hfgI hX) g) :=
  (isIso_desc_nodeChartAdicHom_iff_base_and_c R I q hq hI hfgI hX).trans
    (and_congr_right fun _ =>
      (isIso_c_app_iff_bijective_basicOpenSectionsHom _ _
        (nodeChartQuotientHom R I q hq hI hfgI hX)).symm)

/-! ### The injectivity half does not see the quotient -/

/-- **Injectivity at `D(g)` is a statement about the morphism out of the chain.** The sections
homomorphism of `AlgebraicGeometry.nodeChartQuotientHom` at `D(g)` is injective exactly when that
of `AlgebraicGeometry.nodeChartAdicHom` is.

`AlgebraicGeometry.restrictπ_comp_nodeChartQuotientHom` says the second is the first followed by
the comparison map of the restricted projection, and
`CategoryTheory.IsActionQuotient.injective_c_app`
(`FormalSchemes.ActionQuotientSectionInjective`) says that comparison map is injective at *every*
open — a section of a quotient is determined by its pullback. So the two injectivity statements
imply each other, in one direction because a composite that is injective has an injective right
factor and in the other because injectives compose.

**What this moves.** `AlgebraicGeometry.nodeChartAdicHom` is a morphism out of the chain restricted
to `π⁻¹ V₀`, so the left-hand side names no morphism out of the quotient: reading the type Lean
prints, `CategoryTheory.actionQuotient` occurs on the left only in the type of the index variable
`g`, and `AlgebraicGeometry.nodeChartQuotientHom` does not occur there at all. What it does *not*
move is the open: both sides read sections over a preimage of `D(g)`, and those preimages are taken
along base maps that are still undescribed. Nothing here decides either statement. -/
theorem injective_basicOpenSectionsHom_nodeChartAdicHom_iff
    (g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (tateInvNodeChartQuotientOpens R I q hq hI))) :
    Function.Injective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
        (nodeChartAdicHom R I q hq hI hfgI hX) g) ↔
      Function.Injective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
        (nodeChartQuotientHom R I q hq hI hfgI hX) g) := by
  rw [← restrictπ_comp_nodeChartQuotientHom R I q hq hI hfgI hX]
  exact injective_basicOpenSectionsHom_comp_iff _ _ _ _
    ((isActionQuotient_restrictπ_tateInvNodeChartQuotientOpens R I q hq hI).injective_c_app _)

/-! ### The surjectivity half is the invariant sections of the chain -/

/-- **Surjectivity at `D(g)` is the statement that the invariant sections over the preimage are
reached from the chain.** The sections homomorphism of
`AlgebraicGeometry.nodeChartQuotientHom` at `D(g)` is surjective exactly when every section of the
chain over the preimage of `D(g)` that is invariant under
`AlgebraicGeometry.tateInvNodeChartRestrictedAction` is a value of the sections homomorphism of
`AlgebraicGeometry.nodeChartAdicHom`.

Both directions run through
`AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_isInvariantSection'`
(`FormalSchemes.ActionQuotientRestrictQuotient`), which says the image of the restricted
projection's comparison map at an arbitrary open of `(T_inv/⟨σ⟩)|_{V₀}` is exactly the invariant
sections, together with `CategoryTheory.IsActionQuotient.injective_c_app` for the reverse.

**With `AlgebraicGeometry.injective_basicOpenSectionsHom_nodeChartAdicHom_iff` both halves of
bijectivity are now statements about `AlgebraicGeometry.nodeChartAdicHom`, a morphism out of the
chain.** `T_inv/⟨σ⟩` has not gone away: on the right-hand side it survives in the type of the index
variable `g`, in `AlgebraicGeometry.tateInvNodeChartRestrictedAction`, and in the open the chain is
restricted to. What has gone is the morphism out of it —
`AlgebraicGeometry.nodeChartQuotientHom` does not occur on the right-hand side, which is what the
printed type says. Neither half is decided. -/
theorem surjective_basicOpenSectionsHom_nodeChartQuotientHom_iff
    (g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (tateInvNodeChartQuotientOpens R I q hq hI))) :
    Function.Surjective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
        (nodeChartQuotientHom R I q hq hI hfgI hX) g) ↔
      ∀ t, IsInvariantSection (tateInvNodeChartRestrictedAction R I q hq hI) t →
        ∃ r, basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
          (nodeChartAdicHom R I q hq hI hfgI hX) g r = t := by
  have hinj :=
    (isActionQuotient_restrictπ_tateInvNodeChartQuotientOpens R I q hq hI).injective_c_app
      ((Opens.map (nodeChartQuotientHom R I q hq hI hfgI hX).base).obj
        (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g))
  have hiff := fun t => exists_c_app_restrictπ_eq_iff_isInvariantSection'
    (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
    (tateInvNodeChartQuotientOpens R I q hq hI)
    ((Opens.map (nodeChartQuotientHom R I q hq hI hfgI hX).base).obj
      (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g)) t
  rw [← restrictπ_comp_nodeChartQuotientHom R I q hq hI hfgI hX]
  have key : ∀ s, basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
      (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
        (tateInvNodeChartQuotientOpens R I q hq hI) ≫
        nodeChartQuotientHom R I q hq hI hfgI hX) g s =
      ((LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
        (tateInvNodeChartQuotientOpens R I q hq hI)).c.app
        (op ((Opens.map (nodeChartQuotientHom R I q hq hI hfgI hX).base).obj
          (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g))))
        (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
          (nodeChartQuotientHom R I q hq hI hfgI hX) g s) := fun _ => rfl
  constructor
  · intro hsurj t ht
    obtain ⟨r, hr⟩ := (hiff t).mpr ht
    obtain ⟨s, hs⟩ := hsurj r
    exact ⟨s, (key s).trans (by rw [hs]; exact hr)⟩
  · intro hall r
    obtain ⟨s, hs⟩ := hall _ ((hiff _).mp ⟨r, rfl⟩)
    exact ⟨s, hinj ((key s).symm.trans hs)⟩

/-- **Each member of the family, with the quotient gone.** The sections homomorphism of
`AlgebraicGeometry.nodeChartQuotientHom` at `D(g)` is bijective exactly when the sections
homomorphism of `AlgebraicGeometry.nodeChartAdicHom` at `D(g)` is injective and its image is the
invariant sections over the preimage.

`AlgebraicGeometry.injective_basicOpenSectionsHom_nodeChartAdicHom_iff` and
`AlgebraicGeometry.surjective_basicOpenSectionsHom_nodeChartQuotientHom_iff` conjoined. -/
theorem bijective_basicOpenSectionsHom_nodeChartQuotientHom_iff
    (g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (tateInvNodeChartQuotientOpens R I q hq hI))) :
    Function.Bijective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
        (nodeChartQuotientHom R I q hq hI hfgI hX) g) ↔
      (Function.Injective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
          (nodeChartAdicHom R I q hq hI hfgI hX) g) ∧
        ∀ t, IsInvariantSection (tateInvNodeChartRestrictedAction R I q hq hI) t →
          ∃ r, basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
            (nodeChartAdicHom R I q hq hI hfgI hX) g r = t) :=
  and_congr (injective_basicOpenSectionsHom_nodeChartAdicHom_iff R I q hq hI hfgI hX g).symm
    (surjective_basicOpenSectionsHom_nodeChartQuotientHom_iff R I q hq hI hfgI hX g)

/-! ### Hypothesis 4 with no quotient in the sheaf half -/

/-- **Hypothesis 4, with the sheaf half stated entirely about the chain.** The descent of
`AlgebraicGeometry.nodeChartAdicHom` is an isomorphism exactly when

* the base map of `AlgebraicGeometry.nodeChartQuotientHom` is an isomorphism, and
* for every `g : Γ (T_inv/⟨σ⟩, V₀)`, the ring homomorphism
  `FormalSpectrum.basicOpenSectionsHom … (nodeChartAdicHom …) g` — out of the completed
  localization `awayCompletion (tateInvNodeChartQuotientIdeal …) g` and into the sections of the
  **chain** over the preimage of `D(g)` — is injective, and its image is exactly the sections
  invariant under `AlgebraicGeometry.tateInvNodeChartRestrictedAction`.

`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_bijective` with
`AlgebraicGeometry.bijective_basicOpenSectionsHom_nodeChartQuotientHom_iff` at each member.

**What the second conjunct does and does not mention**, read off the type Lean prints for this
declaration: no `CategoryTheory.IsActionQuotient`, no `CategoryTheory.IsActionQuotient.desc`, and
not `AlgebraicGeometry.nodeChartQuotientHom` — the morphism out of the quotient is confined to the
first conjunct. `CategoryTheory.actionQuotient` does occur, once, in the type of `g`, and
`AlgebraicGeometry.tateInvNodeChartRestrictedAction` occurs in the invariance condition.

The equivalence is two-way, so a single `g` at which either clause fails refutes hypothesis 4 — and
refuting hypothesis 4 does not refute `hnode`; see the module docstring. -/
theorem isIso_desc_nodeChartAdicHom_iff_base_and_chain :
    IsIso ((isActionQuotient_actionQuotientπ (tateInvNodeChartRestrictedAction R I q hq hI)).desc
        (nodeChartAdicHom R I q hq hI hfgI hX)
        (isActionInvariant_nodeChartAdicHom R I q hq hI hfgI hX)) ↔
      IsIso (nodeChartQuotientHom R I q hq hI hfgI hX).base ∧
        ∀ g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
            (op (tateInvNodeChartQuotientOpens R I q hq hI)),
          Function.Injective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
              (nodeChartAdicHom R I q hq hI hfgI hX) g) ∧
            ∀ t, IsInvariantSection (tateInvNodeChartRestrictedAction R I q hq hI) t →
              ∃ r, basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
                (nodeChartAdicHom R I q hq hI hfgI hX) g r = t :=
  (isIso_desc_nodeChartAdicHom_iff_base_and_bijective R I q hq hI hfgI hX).trans
    (and_congr_right fun _ => forall_congr' fun g =>
      bijective_basicOpenSectionsHom_nodeChartQuotientHom_iff R I q hq hI hfgI hX g)

/-! ### The member of the family at `g = 1` -/

/-- **The `⊤` case is the basic open at `1`, and that is the whole of it.**
`AlgebraicGeometry.isIso_c_app_top_nodeChartQuotientHom` transported along
`FormalSpectrum.basicOpen_one` and read through
`FormalSpectrum.isIso_c_app_basicOpen_iff_bijective`.

**It is not evidence for hypothesis 4.** The `⊤` case is obtained structurally — the morphism was
built from `AlgebraicGeometry.nodeChartPsi`, which *is* the identification of
`Γ (T_inv/⟨σ⟩, V₀)` with the invariant sections — so it uses no property of the node locus, the
annulus algebras or the `σ`-action, and it says nothing about any other `g`. What it establishes is
that the family of `AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_bijective` is
non-empty at exactly one of its members. -/
theorem bijective_basicOpenSectionsHom_nodeChartQuotientHom_one :
    Function.Bijective (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
      (nodeChartQuotientHom R I q hq hI hfgI hX) 1) :=
  (isIso_c_app_basicOpen_iff_bijective _ _ (nodeChartQuotientHom R I q hq hI hfgI hX) 1).mp
    ((isIso_c_app_basicOpen_one_iff _ _ (nodeChartQuotientHom R I q hq hI hfgI hX)).mpr
      (isIso_c_app_top_nodeChartQuotientHom R I q hq hI hfgI hX))

end AlgebraicGeometry

end
