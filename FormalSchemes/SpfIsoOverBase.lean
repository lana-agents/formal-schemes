import FormalSchemes.SpfIsoIdealRecovery
import FormalSchemes.TwoChartBasicOpen

set_option linter.style.header false

/-!
# An isomorphism of formal spectra over a base is an isomorphism of algebras over it

`FormalSpectrum.spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`) turns an isomorphism
`e : Spf J₁ ≅ Spf J₂` into a ring isomorphism `A₂ ≃+* A₁`, and
`FormalSpectrum.isCofinal_map_spfIsoRingEquiv` says it carries `J₂` to an ideal cofinal with `J₁`.
Neither statement mentions a base. This file adds the base: if `e` commutes with two morphisms
`m₁ : Spf J₁ ⟶ Spf I`, `m₂ : Spf J₂ ⟶ Spf I` to a common formal spectrum, then the recovered ring
isomorphism intertwines the two ring maps out of `R` that `m₁` and `m₂` induce on global sections.

## Why the tree needs it

`AlgebraicGeometry.IsTopologicallyFiniteType.ofAlgEquiv`
(`FormalSchemes.CofinalTopFiniteType`) transports topological finite type across an isomorphism of
the top ring, and it wants an `R`-**algebra** isomorphism. What geometry supplies is an
isomorphism of formal spectra: `FormalSpectrum.exists_basicOpenChart_inter_iso`
(`FormalSchemes.TwoChartBasicOpen`) produces, for two affine opens of one formal scheme meeting at
a point, a common basic-open refinement together with an isomorphism of the two chart formal
spectra **over** that formal scheme. Its `R`-linearity is what is missing, and it is what turns
that geometric input into an input for the tf-type transport.

## The proof is one application of functoriality

The commuting triangle `e.hom ≫ m₂ = m₁` is carried by `FormalSpectrum.globalSectionsMap_comp`
(`FormalSchemes.SpfGammaFunctorial`) to `Γ (m₁) = Γ (e.hom) ∘ Γ (m₂)`, and `Γ (e.hom)` is by
definition the underlying ring homomorphism of `FormalSpectrum.spfIsoRingEquiv`. So no fullness of
`Spf`, no containment hypothesis relating the ideals, and no adicness of `e` is involved — the same
economy as `FormalSchemes.SpfIsoIdealRecovery`, and for the same reason.

What is *not* free is the algebra structure itself. `Γ (m₁)` and `Γ (m₂)` are bare ring
homomorphisms `R →+* A₁`, `R →+* A₂`; `FormalSpectrum.spfAlgEquivOfComm` therefore takes the two
`Algebra` instances and the two identifications as hypotheses rather than manufacturing instances,
so that a consumer already carrying an algebra structure — as every consumer of
`IsTopologicallyFiniteType` does — can use it without a diamond.

## Main results

* `FormalSpectrum.spfIsoRingEquiv_comp_globalSectionsMap`: **the intertwining**, in `RingHom` form
  and free of any `Algebra` instance.
* `FormalSpectrum.spfAlgEquivOfComm`: the `R`-algebra isomorphism it packages.
* `FormalSpectrum.exists_algEquiv_isCofinal_of_iso_over`: the packaged existential — an
  `R`-algebra isomorphism whose transported ideal is cofinal with the given one. This is the shape
  `IsTopologicallyFiniteType.ofAlgEquiv` and `.ofCofinal` consume, in that order.
* `FormalSpectrum.exists_basicOpenChart_inter_ringEquiv_comp`: non-vacuity — the intertwining at
  the common refinement of two basic-open charts of one formal spectrum, which is the situation
  the statement was written for.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6, §10.5.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R A₁ A₂ : Type u} [CommRing R] [CommRing A₁] [CommRing A₂]
variable {I : Ideal R} {J₁ : Ideal A₁} {J₂ : Ideal A₂}
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A₁] [IsAdicRing J₁] [TopologicalSpace A₂] [IsAdicRing J₂]
variable (e : locallyRingedSpaceObj J₁ ≅ locallyRingedSpaceObj J₂)
variable (m₁ : locallyRingedSpaceObj J₁ ⟶ locallyRingedSpaceObj I)
variable (m₂ : locallyRingedSpaceObj J₂ ⟶ locallyRingedSpaceObj I)

/-- **An isomorphism over the base intertwines the two structure maps.** If `e : Spf J₁ ≅ Spf J₂`
satisfies `e.hom ≫ m₂ = m₁` over a formal spectrum `Spf I`, then the recovered ring isomorphism
`FormalSpectrum.spfIsoRingEquiv e : A₂ ≃+* A₁` carries the ring map `R →+* A₂` induced by `m₂` to
the one induced by `m₁`.

This is `FormalSpectrum.globalSectionsMap_comp` and nothing else; in particular no containment
between the ideals of definition is assumed, which matters because such a containment is not an
isomorphism invariant (`FormalSchemes.SpfIsoIdealRecovery`'s module docstring). -/
theorem spfIsoRingEquiv_comp_globalSectionsMap (hcomm : e.hom ≫ m₂ = m₁) :
    (spfIsoRingEquiv e).toRingHom.comp (globalSectionsMap I J₂ m₂) =
      globalSectionsMap I J₁ m₁ := by
  rw [← hcomm, globalSectionsMap_comp, spfIsoRingEquiv_toRingHom]

/-- **The `R`-algebra isomorphism carried by an isomorphism over `Spf I`.** The two algebra
structures are taken as hypotheses, identified with the maps `m₁` and `m₂` induce on global
sections, rather than manufactured by `RingHom.toAlgebra`: a consumer of
`AlgebraicGeometry.IsTopologicallyFiniteType` already carries an `Algebra` instance, and
constructing a second one here would not be defeq to it. -/
def spfAlgEquivOfComm [Algebra R A₁] [Algebra R A₂] (hcomm : e.hom ≫ m₂ = m₁)
    (h₁ : algebraMap R A₁ = globalSectionsMap I J₁ m₁)
    (h₂ : algebraMap R A₂ = globalSectionsMap I J₂ m₂) :
    A₂ ≃ₐ[R] A₁ :=
  { spfIsoRingEquiv e with
    commutes' := fun r => by
      have := RingHom.congr_fun (spfIsoRingEquiv_comp_globalSectionsMap e m₁ m₂ hcomm) r
      rw [h₁, h₂]
      exact this }

@[simp]
theorem spfAlgEquivOfComm_apply [Algebra R A₁] [Algebra R A₂] (hcomm : e.hom ≫ m₂ = m₁)
    (h₁ : algebraMap R A₁ = globalSectionsMap I J₁ m₁)
    (h₂ : algebraMap R A₂ = globalSectionsMap I J₂ m₂) (a : A₂) :
    spfAlgEquivOfComm e m₁ m₂ hcomm h₁ h₂ a = spfIsoRingEquiv e a :=
  rfl

/-- **The packaged form**: an isomorphism of formal spectra over `Spf I` gives an `R`-algebra
isomorphism of the two global-section rings which moves the ideal of definition only up to
`Ideal.IsCofinal`.

This is exactly the input `AlgebraicGeometry.IsTopologicallyFiniteType.ofAlgEquiv` followed by
`.ofCofinal` (`FormalSchemes.CofinalTopFiniteType`) consumes, and the reason both are needed is
that the on-the-nose statement — that the isomorphism carries `J₂` *onto* `J₁` — is false;
`FormalSchemes.SpfIsoIdealRecovery` refutes it with `L` against `L ^ 2`. -/
theorem exists_algEquiv_isCofinal_of_iso_over [Algebra R A₁] [Algebra R A₂]
    (hJ₁ : J₁.FG) (hJ₂ : J₂.FG) (hcomm : e.hom ≫ m₂ = m₁)
    (h₁ : algebraMap R A₁ = globalSectionsMap I J₁ m₁)
    (h₂ : algebraMap R A₂ = globalSectionsMap I J₂ m₂) :
    ∃ σ : A₂ ≃ₐ[R] A₁, Ideal.IsCofinal (J₂.map σ.toRingEquiv.toRingHom) J₁ :=
  ⟨spfAlgEquivOfComm e m₁ m₂ hcomm h₁ h₂, isCofinal_map_spfIsoRingEquiv e hJ₁ hJ₂⟩

/-- **Non-vacuity, at a genuine pair of distinct charts.** `D(t) = D(t * t)`, so the two
basic-open charts `Spf A{1/t}^ ⟶ Spf L` and `Spf A{1/(t * t)}^ ⟶ Spf L` have the same range and
`LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` (`FormalSchemes.OpenImmersionIsoOfRangeEq`)
produces an isomorphism between them *over* `Spf L`. The theorem above then says the recovered
ring isomorphism intertwines the two structural maps out of `A`.

This is an application, not a restatement, and the two sides are not closed by `rfl`: the source
rings `A{1/t}^` and `A{1/(t * t)}^` are completions of two *different* localizations of `A`, and
the equality of the two ring homomorphisms out of `A` is the content of
`FormalSpectrum.globalSectionsMap_comp` applied to a triangle that had to be built from a range
equality. It is the same shape as the two-chart situation of
`FormalSpectrum.exists_basicOpenChart_le_affine_inter_two_charts`
(`FormalSchemes.TwoChartBasicOpen`), with the common refinement already chosen.

The two `IsAdicRing` hypotheses both follow from `hL` by
`FormalSpectrum.isAdicRing_awayCompletionIdeal` (`FormalSchemes.BasicOpenChart`); they are taken
as instance arguments only because they are needed for the *statement* to elaborate, and a
`haveI` in the proof would come too late. -/
theorem spfIsoRingEquiv_isoOfRangeEq_comp_globalSectionsMap {A : Type u} [CommRing A]
    [TopologicalSpace A] {L : Ideal A} [IsAdicRing L] (hL : L.FG) (t : A)
    [IsAdicRing (awayCompletionIdeal L t)] [IsAdicRing (awayCompletionIdeal L (t * t))] :
    ∃ e : locallyRingedSpaceObj (awayCompletionIdeal L t)
        ≅ locallyRingedSpaceObj (awayCompletionIdeal L (t * t)),
      (spfIsoRingEquiv e).toRingHom.comp
          (globalSectionsMap L (awayCompletionIdeal L (t * t)) (basicOpenChart L (t * t))) =
        globalSectionsMap L (awayCompletionIdeal L t) (basicOpenChart L t) := by
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart L t) :=
    isOpenImmersion_basicOpenChart L t hL
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart L (t * t)) :=
    isOpenImmersion_basicOpenChart L (t * t) hL
  have hEq : Set.range (basicOpenChart L t).base
      = Set.range (basicOpenChart L (t * t)).base := by
    rw [range_basicOpenChart_base L t hL, range_basicOpenChart_base L (t * t) hL,
      basicOpen_mul, TopologicalSpace.Opens.coe_inf, Set.inter_self]
  exact ⟨LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hEq,
    spfIsoRingEquiv_comp_globalSectionsMap _ _ _
      (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hEq)⟩

end FormalSpectrum
