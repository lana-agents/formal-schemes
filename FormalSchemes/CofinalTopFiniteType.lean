import FormalSchemes.AwayTopFiniteType
import FormalSchemes.CofinalCompletionAlg

set_option linter.style.header false

/-!
# Topological finite type is invariant under a cofinal ideal of definition on the base

`IsTopologicallyFiniteType R I A L` (`FormalSchemes.TopFiniteType`) is stated at a *fixed* ideal
`I` of the base, and it pins the ideal of the top ring on the nose:
`IsTopologicallyFiniteType.map_eq` says `I · A = L`. An adic ring has no
distinguished ideal of definition, so a predicate stated this way is only useful if it does not
actually depend on the choice. This file proves that it does not.

## Why this is the blocker it is

EGA I 10.13's composition law at a non-affine target needs, per chart, **one** tf-type algebra
whose structural morphism is the whole composite
(`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn`,
`FormalSchemes.TopFiniteTypeHom`). The two halves of a composite are witnessed independently, so
the middle chart arrives with two ideals of definition that agree only up to
`Ideal.IsCofinal` — the naive form, that they are equal, is refuted by `L` versus `L ^ 2`
(`FormalSchemes.TopFiniteTypeHomComp`'s module docstring). `IsTopologicallyFiniteType.ofCofinal`
below is what closes that gap; assembling it into the composition law is a separate matter and is
not attempted here.

## What the transport does and does not say

`IsTopologicallyFiniteType.ofCofinal` **changes the ideal of the top ring too**, and it must: the
conclusion's ideal is `J₂ · A`, not `L = J₁ · A`. Those are different ideals — for `J₂ = J₁ ^ 2`
they differ by a square — and no statement fixing `L` could be true.

What survives is that the two are cofinal, `IsTopologicallyFiniteType.isCofinal_map`. So the
*topology* on `A` is unchanged, which is the invariant that matters: `A` is still the same adic
ring, presented against a different ideal of definition of the base.

The transport is a one-line consequence of `RestrictedPowerSeries.cofinalAlgEquiv` and
`Ideal.map_algebraMap_algHom` (`FormalSchemes.CofinalCompletionAlg`) — the presentation is composed
with the cofinality isomorphism, and the ideal bookkeeping goes through because an `R`-algebra map
fixes the *base* ideal it extends. In particular no property of the completion beyond
`AlgEquiv.commutes` is used.

## Main results

* `IsTopologicallyFiniteType.ofCofinal`: **the invariance**, and the goal of this file.
* `isTopologicallyFiniteType_congr_of_isCofinal`: its symmetric `Iff` form.
* `IsTopologicallyFiniteType.isCofinal_map`: the ideal of the top ring changes only up to
  cofinality, so the adic topology on `A` is unchanged.
* `IsTopologicallyFiniteType.ofAlgEquiv`: transport across an isomorphism of the top ring, the
  second half of what a composite needs.
* `IsTopologicallyFiniteType.pow` and `IsTopologicallyFiniteType.self_pow`: the transport applied
  to a positive power of the base ideal. The second is a closed statement about an arbitrary
  complete adic ring, obtained from `AlgebraicGeometry.IsTopologicallyFiniteType.self`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.5, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/

noncomputable section

universe u

variable {R : Type u} [CommRing R] {I J₁ J₂ : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}
variable {A' : Type u} [CommRing A'] [Algebra R A']

/-- **Topological finite type only depends on the base ideal up to cofinality.** If `A` is
topologically of finite type over `(R, J₁)` and `J₂` is cofinal with `J₁`, then `A` is
topologically of finite type over `(R, J₂)` — with ideal `J₂ · A`, which is *not* `L` but is
cofinal with it (`IsTopologicallyFiniteType.isCofinal_map`).

The proof composes the given presentation `ψ : R{X₁, …, Xₙ}_{J₁} ↠ A` with the cofinality
isomorphism `RestrictedPowerSeries.cofinalAlgEquiv`. Surjectivity is immediate; the ideal
condition is `Ideal.map_algebraMap_algHom` applied twice — once to the isomorphism, once to `ψ` —
which is exactly the observation that an `R`-algebra map carries `J₂ · B` to `J₂ · C` for a *fixed*
ideal `J₂` of `R`. The number of variables `n` is unchanged. -/
theorem IsTopologicallyFiniteType.ofCofinal (hA : IsTopologicallyFiniteType R J₁ A L)
    (h : J₁.IsCofinal J₂) :
    IsTopologicallyFiniteType R J₂ A (J₂.map (algebraMap R A)) := by
  obtain ⟨n, ψ, hs, -⟩ := hA
  refine ⟨n, ψ.comp (RestrictedPowerSeries.cofinalAlgEquiv R n h).symm.toAlgHom, ?_, ?_⟩
  · exact hs.comp (RestrictedPowerSeries.cofinalAlgEquiv R n h).symm.surjective
  · change Ideal.map (ψ.toRingHom.comp
      (RestrictedPowerSeries.cofinalAlgEquiv R n h).symm.toAlgHom.toRingHom) _ = _
    rw [← Ideal.map_map, RestrictedPowerSeries.map_cofinalAlgEquiv_symm_idealOfDefinition,
      Ideal.map_algebraMap_algHom ψ J₂]

/-- The symmetric form of `IsTopologicallyFiniteType.ofCofinal`: for cofinal base ideals, being
topologically of finite type with the *induced* ideal on the top ring is the same condition on
either side. -/
theorem isTopologicallyFiniteType_congr_of_isCofinal (h : J₁.IsCofinal J₂) :
    IsTopologicallyFiniteType R J₁ A (J₁.map (algebraMap R A)) ↔
      IsTopologicallyFiniteType R J₂ A (J₂.map (algebraMap R A)) :=
  ⟨fun hA => hA.ofCofinal h, fun hA => hA.ofCofinal (Ideal.IsCofinal.symm h)⟩

/-- **The ideal on the top ring moves only within its cofinality class.** So the adic topology of
`A` is untouched by `IsTopologicallyFiniteType.ofCofinal`, and `A` remains the same adic ring — it
is only the presentation that changes.

Immediate from `IsTopologicallyFiniteType.map_eq`, which identifies `L` with `J₁ · A`, and
`Ideal.IsCofinal.map`. -/
theorem IsTopologicallyFiniteType.isCofinal_map (hA : IsTopologicallyFiniteType R J₁ A L)
    (h : J₁.IsCofinal J₂) : L.IsCofinal (J₂.map (algebraMap R A)) := by
  rw [← hA.map_eq]
  exact h.map (algebraMap R A)

/-- **Topological finite type transports across an isomorphism of the top ring.** An `R`-algebra
isomorphism `A ≃ₐ[R] A'` carries a tf-type structure to a tf-type structure, with ideal `I · A'`.

`IsTopologicallyFiniteType.of_surjective` (`FormalSchemes.TopFiniteType`) does
the work; the ideal side is `Ideal.map_algebraMap_algHom` again, after
`IsTopologicallyFiniteType.map_eq` has rewritten `L` as `I · A`.

Together with `IsTopologicallyFiniteType.ofCofinal` this is what makes the two halves of a
composite usable. In EGA I 10.13's composition law the middle chart arrives twice: once as a ring
`B` carrying `g`'s witness, once as a ring `B'` carrying `f`'s, with an isomorphism of *formal
spectra* between them. `FormalSpectrum.spfIsoRingEquiv`
(`FormalSchemes.SpfIsoIdealRecovery`) turns that into a ring isomorphism, this lemma moves `g`'s
witness across it — the base `(S, K)` is untouched, so no change of base *ring* is ever needed —
and `IsTopologicallyFiniteType.ofCofinal` then aligns the two base ideals on the common ring, which
`FormalSpectrum.isCofinal_map_spfIsoRingEquiv` says are cofinal. Assembling that into the
composition law is 62h's business and is not attempted here. -/
theorem IsTopologicallyFiniteType.ofAlgEquiv (hA : IsTopologicallyFiniteType R I A L)
    (σ : A ≃ₐ[R] A') : IsTopologicallyFiniteType R I A' (I.map (algebraMap R A')) := by
  refine hA.of_surjective σ.toAlgHom σ.surjective ?_
  rw [← hA.map_eq]
  exact Ideal.map_algebraMap_algHom σ.toAlgHom I

/-- **A tf-type algebra over `(R, I)` is tf-type over `(R, I ^ k)`** for every `k ≠ 0`, since `I`
and `I ^ k` are cofinal (`Ideal.IsCofinal.pow`).

This is the concrete content of the invariance: `I` and `I ^ k` are the standard example of two
ideals of definition that are cofinal but not equal, and they are the counterexample that makes the
naive "an isomorphism of formal spectra identifies the ideals of definition" false. -/
theorem IsTopologicallyFiniteType.pow (hA : IsTopologicallyFiniteType R I A L) {k : ℕ}
    (hk : k ≠ 0) :
    IsTopologicallyFiniteType R (I ^ k) A ((I ^ k).map (algebraMap R A)) :=
  hA.ofCofinal (Ideal.IsCofinal.pow I hk)

/-- **A complete adic ring is topologically of finite type over itself against any positive power
of its ideal of definition.** `AlgebraicGeometry.IsTopologicallyFiniteType.self` gives the case
`k = 1`; the general case is `IsTopologicallyFiniteType.pow`, and the extension
`Ideal.map (algebraMap R R)` collapses because the structural map is the identity.

Note the namespace: the predicate and most of its API are root-level — including
`IsTopologicallyFiniteType.trans` (`FormalSchemes.TopFiniteTypeTrans`) and everything added here —
but `AlgebraicGeometry.IsTopologicallyFiniteType.self` (`FormalSchemes.AwayTopFiniteType`) and
`AlgebraicGeometry.IsTopologicallyFiniteType.structHom` sit inside `AlgebraicGeometry`. The
qualifications in this file are therefore not uniform, and that is not a typo.

An application rather than a restatement: the hypothesis mentions `I` and the conclusion mentions
`I ^ k`, so the two sides are not the same statement and the proof genuinely runs the transport
through a change of presentation. -/
theorem IsTopologicallyFiniteType.self_pow [IsAdicComplete I R] {k : ℕ} (hk : k ≠ 0) :
    IsTopologicallyFiniteType R (I ^ k) R (I ^ k) := by
  have h := (AlgebraicGeometry.IsTopologicallyFiniteType.self (I := I)).pow hk
  rwa [Algebra.algebraMap_self, Ideal.map_id] at h
