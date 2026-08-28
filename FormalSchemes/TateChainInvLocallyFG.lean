import FormalSchemes.LocallyFG
import FormalSchemes.TateChainInvGlue
import FormalSchemes.AnnulusNontrivial

set_option linter.style.header false

/-!
# The inversion-glued Tate chain is locally finitely generated

The chain-side companion of `FormalSchemes/TateLocallyFG.lean`, which proves the same thing for the
two-patch Tate scheme `tateTwoPatch`. Both are instances of
`AlgebraicGeometry.FormalScheme.GlueData.gluedFormalScheme_locallyFG`, and for the same reason: the
patches of `tateChainInvGlueData'` are *literally* the patches of `tateTwoPatchGlueData'`, namely
the formal annulus `Spf (I·A)` with `A = R{x, y}/(x·y − q)`. Only the index type changes, from
`ULift Bool` to `ULift ℤ`, so the constant function that discharges the hypothesis on the two-patch
side discharges it here unchanged.

## Why this is wanted

`AlgebraicGeometry.LocallyRingedSpace.formalSchemeOfStalkIso`
(`FormalSchemes/ActionQuotientFormalScheme.lean`) — the criterion that turns a free, properly
discontinuous action quotient into a formal scheme — carries a `LocallyFG` hypothesis on the
*source*, because it produces its affine charts through
`AlgebraicGeometry.FormalScheme.restrictOpen` and that requires one. The Tate action lives on
`tateChainInv`, so applying the criterion there needs `(tateChainInv …).LocallyFG` and nothing on
this tree had it.

## Why this is not vacuous

`AlgebraicGeometry.FormalScheme.LocallyFG` is a `∀ x, ∃ …` statement, so it holds vacuously on an
empty space. `tateChainInv_nonempty` rules that out whenever the Tate parameter `q` lies in a
proper ideal of definition `I`, which is the standing situation of the chain: the special fibre
`A ⧸ I·A = (R ⧸ I){x, y}/(x·y)` is then nontrivial (`annulus_nontrivial`), so the patch has a point
(`annulus_formalSpectrum_nonempty`) and the patch inclusion carries it into the glued object.

## Main results

* `AlgebraicGeometry.tateChainInv_locallyFG`: the inversion-glued Tate chain is `LocallyFG`.
* `AlgebraicGeometry.tateChainInv_nonempty`: it has points when `q ∈ I` and `I ≠ ⊤`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (q : R)

/-- **The inversion-glued Tate chain is locally finitely generated.** Every patch of the chain is
the same affine formal scheme `Spf (I·A)`, whose ideal of definition is finitely generated over a
Noetherian base (`annulusIdealOfDefinition_fg`), so no case split on the index is needed. -/
theorem tateChainInv_locallyFG (hq : q ∈ I) (hI : I.FG) :
    (tateChainInv R I q hq hI).LocallyFG :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  FormalScheme.GlueData.gluedFormalScheme_locallyFG _ (fun _ =>
    ⟨FormalScheme.Spf (annulusIdealOfDefinition R I q),
      FormalScheme.locallyFG_Spf (annulusIdealOfDefinition_fg R I q hI), ⟨Iso.refl _⟩⟩)

/-- **The inversion-glued Tate chain has points** when the Tate parameter lies in a proper ideal of
definition: the special fibre of the annulus is then nontrivial, so `Spf (I·A)` has a point, and
the patch inclusion at index `0` carries it into the glued object. Together with
`tateChainInv_locallyFG` this rules out the vacuous reading of that statement. -/
theorem tateChainInv_nonempty (hq : q ∈ I) (hI : I.FG) (hIne : I ≠ ⊤) :
    Nonempty (tateChainInv R I q hq hI).toLocallyRingedSpace := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  obtain ⟨x⟩ := annulus_formalSpectrum_nonempty R I q hq hIne
  exact ⟨((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.ι
    ⟨0⟩).base x⟩

end AlgebraicGeometry
