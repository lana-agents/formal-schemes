import FormalSchemes.TateInvGlobalNormalForm

set_option linter.style.header false

/-!
# What the separation hypothesis of the Tate annulus costs

`FormalSchemes.TateInvGlobalNormalForm` proves the headline `Γ (T_inv/⟨σ⟩) ≃+* R` from a single
hypothesis, `AlgebraicGeometry.IsTateInvCoordSeparating`: the two `Ĝm` coordinate maps of
`A = R{x, y}/(x·y − q)` have zero common kernel. That hypothesis is not proved there for any
`R, I, q`, and this file measures it from below.

## The reading

`annulusIdeal` is `Ideal.span {annulusRel R I q}` — the **plain span of the Tate relation, not
its adic closure**. Both coordinate maps out of `R{x, y}` are continuous
(`AlgebraicGeometry.tateInvGlobalCoord_annulusMk_mem_pow` and its flip) and land in `R{X, X⁻¹}`,
which is Hausdorff; so their common kernel is a *closed* ideal containing the span. The
separation hypothesis says that common kernel is exactly the span. Hence:

* `AlgebraicGeometry.adicKerClosed_of_isTateInvCoordSeparating`: separation implies the
  presentation kernel `(x·y − q)` is adically closed.

**So there is no hypothesis-free proof of the separation property** unless `(x·y − q)` is
adically closed in `R{x, y}` for every complete adic base with a finitely generated ideal of
definition — which is exactly what `annulus_isAdicRing` obtains from Noetherianness
(`IsTopologicallyFiniteType.isAdicRing_of_noetherian`) rather than for free, and what
`annulus_isAdicRing_of_kerClosed` exists to carry as a hypothesis. A proof of separation should
therefore be sought with a Noetherian base, or with adic closedness assumed outright. The
contrapositive is `AlgebraicGeometry.not_isTateInvCoordSeparating_of_not_adicKerClosed`.

(The whole `annulus*` family — `annulusIdeal`, `annulusMk`, `annulusFlip`, `annulusAlgebra`,
`annulusIdealOfDefinition`, `annulus_isAdicRing` — lives in the **root** namespace, not under
`AlgebraicGeometry`, even though `FormalSchemes.TateAnnulus` `open`s it. Two issue descriptions
on this cluster say otherwise.)

## The consumer

Read in the other direction, the same implication is a tool rather than a warning:
`annulus_isAdicRing_of_kerClosed` takes precisely adic closedness of the kernel, so

* `AlgebraicGeometry.isAdicRing_of_isTateInvCoordSeparating`: the Tate annulus is a complete
  adic ring **without a Noetherian base**, given separation.

`annulus_isAdicRing` needs `[IsNoetherianRing R]` for the same conclusion.

## What is *not* proved here

Nothing about whether `AlgebraicGeometry.IsTateInvCoordSeparating` holds — in general or in a
single instance. The headline remains conditional exactly as
`FormalSchemes.TateInvGlobalNormalForm` leaves it, and the implication proved here runs *out of*
the hypothesis, never into it. In
particular this file does not show that `A` is Hausdorff or complete unconditionally: the
statements of `FormalSchemes.AdicQuotient` that would give that are consumers of adic closedness,
not independent facts.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13 — quotients of an
  adic ring by a closed ideal.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open RestrictedLaurentSeries

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} [IsAdicComplete I R] {q : R}

/-- **A continuous ring map out of the Tate annulus kills anything adically congruent to the
presentation kernel.** The hypothesis `hF` is the continuity of `F ∘ annulusMk` on the polydisc,
and `hw` says `w` is, modulo every power of the ideal of definition, congruent to an element of
the kernel. Both `AlgebraicGeometry.tateInvGlobalCoord` and its composite with `annulusFlip`
satisfy `hF`, which is why this is stated for an arbitrary `F`. -/
theorem eq_zero_of_forall_sub_ker_mem_pow (hI : I.FG)
    (F : annulusAlgebra R I q →+* RestrictedLaurentSeries R I)
    (hF : ∀ (m : ℕ) {v : annulusRing R I},
      v ∈ (RestrictedPowerSeries.idealOfDefinition R I 2) ^ m →
      F (annulusMk R I q v) ∈ (RestrictedLaurentSeries.idealOfDefinition R I) ^ m)
    {w : annulusRing R I}
    (hw : ∀ m : ℕ, ∃ k ∈ RingHom.ker (annulusMk R I q).toRingHom,
      w - k ∈ (RestrictedPowerSeries.idealOfDefinition R I 2) ^ m) :
    F (annulusMk R I q w) = 0 := by
  refine eq_zero_of_coeff_eq_zero I fun n => ?_
  refine IsHausdorff.haus (I := I) (M := R) inferInstance _ fun m => ?_
  rw [SModEq.zero, Ideal.mem_smul_top_self_iff]
  obtain ⟨k, hk, hwk⟩ := hw m
  have hk0 : annulusMk R I q k = 0 := RingHom.mem_ker.mp hk
  have hFk : F (annulusMk R I q w) = F (annulusMk R I q (w - k)) := by
    rw [map_sub, hk0, sub_zero]
  rw [hFk]
  exact coeff_mem_pow I hI n m
    ((RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m _).mp (hF m hwk))

/-- **The separation property forces the presentation kernel to be adically closed.** The two
coordinate maps are continuous into the Hausdorff ring `R{X, X⁻¹}`, so their common kernel is a
closed ideal containing `(x·y − q)`; separation says it is exactly `(x·y − q)`.

Consequently no proof of `AlgebraicGeometry.IsTateInvCoordSeparating` can avoid a hypothesis
that yields adic closedness — Noetherianness of the base, as in `annulus_isAdicRing`, or
closedness assumed outright, as in `annulus_isAdicRing_of_kerClosed`. Note this implication
itself needs neither: not `q ∈ I`, not `[IsNoetherianRing R]`, not `[TopologicalSpace R]`, not
`[IsAdicRing I]`. -/
theorem adicKerClosed_of_isTateInvCoordSeparating (hI : I.FG)
    (hsep : IsTateInvCoordSeparating R I q hI) :
    (annulusMk R I q).toRingHom.AdicKerClosed
      (RestrictedPowerSeries.idealOfDefinition R I 2) := by
  intro w hw
  have h1 := eq_zero_of_forall_sub_ker_mem_pow hI (tateInvGlobalCoord R I q hI)
    (fun m _ hv => tateInvGlobalCoord_annulusMk_mem_pow R I q hI m hv) hw
  have h2 := eq_zero_of_forall_sub_ker_mem_pow hI
    ((tateInvGlobalCoord R I q hI).comp (annulusFlip R I q hI).symm.toAlgHom.toRingHom)
    (fun m _ hv => tateInvGlobalCoord_annulusFlip_symm_annulusMk_mem_pow R I q hI m hv) hw
  exact RingHom.mem_ker.mpr (hsep _ h1 h2)

/-- **The Tate annulus is a complete adic ring over a base that need not be Noetherian**, given
the separation property: `annulus_isAdicRing_of_kerClosed` takes exactly the closedness that
`AlgebraicGeometry.adicKerClosed_of_isTateInvCoordSeparating` supplies. Compare
`annulus_isAdicRing`, which reaches the same conclusion from `[IsNoetherianRing R]`. -/
theorem isAdicRing_of_isTateInvCoordSeparating (hI : I.FG)
    (hsep : IsTateInvCoordSeparating R I q hI) :
    IsAdicRing (annulusIdealOfDefinition R I q) :=
  annulus_isAdicRing_of_kerClosed R I q hI (adicKerClosed_of_isTateInvCoordSeparating hI hsep)

/-- **A base on which the presentation kernel is not adically closed refutes the separation
property**, and with it every conditional statement of `FormalSchemes.TateInvGlobalNormalForm`
over that base. This is the form in which a counterexample to the headline would be consumed. -/
theorem not_isTateInvCoordSeparating_of_not_adicKerClosed (hI : I.FG)
    (hker : ¬ (annulusMk R I q).toRingHom.AdicKerClosed
      (RestrictedPowerSeries.idealOfDefinition R I 2)) :
    ¬ IsTateInvCoordSeparating R I q hI :=
  fun hsep => hker (adicKerClosed_of_isTateInvCoordSeparating hI hsep)

end AlgebraicGeometry
