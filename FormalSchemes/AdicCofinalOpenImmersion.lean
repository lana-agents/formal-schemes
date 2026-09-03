import FormalSchemes.AffineOpenTopFiniteType
import FormalSchemes.CofinalAdicRing
import FormalSchemes.CofinalSheafComparisonIso

set_option linter.style.header false

/-!
# Adicity of a morphism of formal spectra, up to cofinality

`IsTopologicallyFiniteType.of_openImmersion_of_isCofinal` (`FormalSchemes.AffineOpenTopFiniteType`)
says an affine open of `Spf I` is topologically of finite type over `(R, I)`, and carries exactly
one hypothesis:

> for an open immersion `m : Spf J ⟶ Spf I` with `algebraMap R B = globalSectionsMap I J m`,
> `Ideal.IsCofinal J (I.map (algebraMap R B))`.

That is EGA's *an affine open immersion is adic*, weakened to the only form that can be true. This
file is about that hypothesis. It **does not discharge it in general**; what it does is split it
into a half that is free and a half that is not, settle the free half unconditionally, settle the
whole statement for the opens that are basic, reduce the general hypothesis from a cofinality to a
single containment, and remove one candidate counterexample from consideration.

## Why cofinality, and not a containment

The on-the-nose form `I · B ≤ J` is **false**, and the tree records the refutation twice:
`FormalSchemes.AdicOnSections` (issue 460) and `FormalSchemes.AdicOnSectionsDescent`'s
containment hypothesis `(B)` (issue 480). `IsAdicRing J` fixes the *topology* of `B`, not the
ideal `J`, so `FormalSpectrum.cofinalSpfIso` builds an isomorphism of formal spectra — hence an
open immersion — presenting the same open at `L ^ 2` instead of at `L`. Cofinality survives that,
since `L` and `L ^ 2` are cofinal, and for an isomorphism the statement is already a theorem,
`FormalSpectrum.isCofinal_map_spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`).

## The split

`Ideal.IsCofinal.of_radical_eq` (`FormalSchemes.CofinalIdeal`) reduces the cofinality of two
finitely generated ideals to the equality of their radicals, which in `Spec B` is two inclusions:

* `I · B ≤ √J` — "`I · B` is topologically **nilpotent**";
* `J ≤ √(I · B)` — "`I · B` is **open**".

**The first is free.** `FormalSpectrum.map_le_radical_of_hom` proves it for an *arbitrary*
morphism of formal spectra: no open immersion, no finite generation, no completeness. A prime of
`B` containing `J` is a point of `Spf J` by `FormalSpectrum.range_toPrimeSpectrum`, its
contraction along `globalSectionsMap` is the corresponding point of `Spf I` by
`FormalSpectrum.base_toPrimeSpectrum_eq`, and a point of `Spf I` contains `I`. This is the same
argument `FormalSpectrum.zeroLocus_map_spfIsoRingEquiv` runs, with only one of its two directions
available: an isomorphism can push a point back along `e.inv`, and an immersion has no `e.inv`.

**The second is the whole question**, and it is not settled here.
`FormalSpectrum.le_radical_map_iff_forall_mem_range` says what it asks for, in points:

> every prime of `B` containing `I · B` is a point of `Spf J`.

A prime `q ⊇ I · B` with `q ⊉ J` is a point of `Spec B` lying *outside* `Spf J`, and an open
immersion is a statement about `V (J)` and its image in `V (I)`.

## What is settled here about the openness half

* **Cofinality is a property of the open subset, not of its presentation.**
  `FormalSpectrum.isCofinal_map_of_range_eq`: two open immersions into `Spf I` with the same range
  either both satisfy it or neither does. So one may replace `(B, J)` by any other presentation of
  the same open before attacking it — which is what makes the next item usable.
* **It holds when the open is basic.** `FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart`:
  if `Set.range m.base` is the range of a basic-open chart `Spf R{1/f}^ ⟶ Spf I`, then the
  cofinality holds, because on the chart the containment is an *equality*
  (`FormalSpectrum.map_algebraMap_awayCompletion`) and the previous item transports it. Hence
  `IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen`: conservativity's affine step is
  **unconditional** over a basic open, for an arbitrary presentation of it.
* **The consumer's hypothesis is one containment, not a cofinality.**
  `FormalSpectrum.isCofinal_map_of_le_radical` and
  `IsTopologicallyFiniteType.of_openImmersion_of_le_radical` take `J ≤ √(I · B)` and supply the
  rest.

## The candidate counterexample that does not exist

Both rows that proposed this statement (issues 1211 and 1215) named the same suspect: a
**non-quasi-compact** open `U ⊆ Spf I` whose sections ring is an infinite product, where every
basic open of `U` is fine but `I · Γ (U, 𝒪)` has no reason to be open. There is no such open.
`FormalSpectrum.isCompact_range_base`: the image of *any* morphism of formal spectra is
quasi-compact, because `Spf J` is `Spec (B ⧸ J)` and `FormalSpectrum.instSpectralSpace`
(`FormalSchemes.FormalSpectrum`) makes it a spectral space. So an affine open of `Spf I` is a
quasi-compact open, always, and quasi-compactness is not an extra hypothesis one may add — it is
not a hypothesis at all. The two rows disagreed about whether it was in scope; the answer is that
the question does not arise.

## Why the basic-open cover does not finish the job

`FormalSpectrum.exists_basicOpenChart_inter_iso` (`FormalSchemes.TwoChartBasicOpen`) covers
`Spf J` by basic opens that are simultaneously basic opens of `Spf I`, and the previous paragraph
makes that cover finite. On each such chart the cofinality holds, by the same argument as
`isCofinal_map_of_range_eq_basicOpenChart`. What a cover supplies, in the ring, is
`Ideal.span s ⊔ J = ⊤` (`FormalSpectrum.sup_eq_top_of_forall_exists_mem_basicOpen`) — and that
datum says exactly `V (J) ⊆ ⋃ D(g)`, so it constrains no prime that fails to contain `J`. Those
are precisely the primes the openness half is about. Descending the containment `J ^ n ≤ I · B`
along `B → ∏ B{1/gᵢ}^` would instead need `I · B` to be the sections of a subsheaf, which is a
statement about the structure sheaf and not about the ideals.

## What the openness half needs — the route, now formalised

Recorded so the next worker does not re-derive it. **Every step of it is now a theorem**, under
the hypothesis that the thickenings of the open are affine
(`FormalSpectrum.HasAffineThickenings`, `FormalSchemes.AffineThickenings`); the sentences below
are kept because they are the shape of the argument, not because anything in them is still open.
Write `B` as the inverse limit of `Bₙ = Γ (U, 𝒪_{Spec (R ⧸ Iⁿ)})`. If `U` is an affine open of
`Spec (R ⧸ I)` then each `Uₙ` is affine — it is a nilpotent thickening of `U` — so the transition
maps `Bₙ₊₁ → Bₙ` are surjective, `B ↠ Bₙ`, and `ker (Bₙ₊₁ → Bₙ) = Iⁿ · Bₙ₊₁`. Successive
approximation against a finite generating set of `I`, using completeness of `B` for the filtration
`ker (B → Bₙ)`, then gives `ker (B ↠ B₁) = I · B` **on the nose**, and `√(ker (B ↠ B₁)) = √J`
because both cut out `U`.

* The surjections are `FormalSchemes.AffineThickenings`, the kernel of one step is
  `FormalSchemes.ThickeningTowerKernel`, and the successive approximation is
  `FormalSpectrum.ker_sectionsPi_zero` (`FormalSchemes.TowerLimitKernel`).
* The last step — *"because both cut out `U`"* — is
  `FormalSpectrum.le_radical_map_of_hasAffineThickenings`
  (`FormalSchemes.AdicOpennessHalf`), which reads both `V (I · B)` and `V (J)` off the points of
  `U` through the germs of `𝒪_{Spf R}`; and
  `FormalSpectrum.isCofinal_map_of_hasAffineThickenings` is the cofinality it and the nilpotence
  half assemble to.

**The hypothesis is no longer open.** `FormalSpectrum.hasAffineThickenings_opensRange`
(`FormalSchemes.AffineThickeningsOpenImmersion`) proves that the range of an arbitrary affine open
immersion has affine thickenings, with no hypothesis on `I`, on `J` or on the range. So the whole
of the route above is unconditional, and `FormalSpectrum.isCofinal_map_of_openImmersion` is EGA I
10.12's statement outright.

The paragraph this replaces said the input *"that the reduction of the open is an affine scheme,
not merely a quasi-compact spectral space"* was not derivable from
`LocallyRingedSpace.IsOpenImmersion` alone. It is, and the derivation does not go through the
reduction: the span that the affineness criterion needs is produced in `B` and pushed forward to
every level of the tower at once. `FormalSchemes.AffineThickeningsOpenImmersion` has the argument
and the correction to `FormalSchemes.AffineThickenings`'s account of why it could not work.

## Main results

* `FormalSpectrum.map_le_radical_of_hom`, `FormalSpectrum.exists_pow_map_le_of_hom`,
  `FormalSpectrum.zeroLocus_subset_zeroLocus_map_of_hom`: **the nilpotence half**,
  unconditionally, for an arbitrary morphism of formal spectra.
* `FormalSpectrum.isCompact_range_base`: the image of a morphism of formal spectra is
  quasi-compact.
* `FormalSpectrum.le_radical_map_iff_forall_mem_range`: the openness half, in points.
* `FormalSpectrum.isCofinal_map_of_le_radical`: **the assembly** — the openness half alone gives
  the cofinality.
* `FormalSpectrum.isCofinal_map_of_range_eq`,
  `FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart`: presentation-independence, and the
  basic-open case.
* `IsTopologicallyFiniteType.of_openImmersion_of_le_radical`,
  `IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen`: the two consumers.
* `IsTopologicallyFiniteType.awayCompletion_sq_of_openImmersion`: non-vacuity for the basic-open
  case, at `D(t) = D(t * t)` — a presentation that is not the chart itself.
* `IsTopologicallyFiniteType.self_of_openImmersion_pow`: non-vacuity, through the comparison
  isomorphism `Spf (I ^ 2) ≅ Spf I`, where the openness hypothesis is a genuinely non-reflexive
  containment.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/
noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {B : Type u} [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J]

/-!
### The image of a morphism of formal spectra is quasi-compact

Recorded first because it disposes of the counterexample both predecessor rows suspected; see the
module docstring.
-/

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J] in
/-- **The image of a morphism of formal spectra is quasi-compact**, with no hypothesis on the
morphism at all — in particular an affine open of `Spf I` is a quasi-compact open of it.

There is nothing to prove: `Spf J` is `Spec (B ⧸ J)` by definition, so
`FormalSpectrum.instSpectralSpace` makes it a compact space, and a continuous image of a compact
space is compact. It is recorded because it removes a candidate counterexample to the openness
half discussed in this file's module docstring: there is no non-quasi-compact affine open of
`Spf I`, so no argument about one is needed and none is available.

The instance has to be transported by hand: the carrier of `locallyRingedSpaceObj J` is not
syntactically `FormalSpectrum J`, so instance search does not find `CompactSpace` on it. -/
theorem isCompact_range_base (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) :
    IsCompact (Set.range m.base) := by
  haveI : CompactSpace ((locallyRingedSpaceObj J).toPresheafedSpace.carrier) :=
    inferInstanceAs (CompactSpace (FormalSpectrum J))
  exact isCompact_range m.base.hom.continuous

section Algebra

variable [Algebra R B]

/-!
### The nilpotence half

`I · B ≤ √J`, for an arbitrary morphism of formal spectra. This is the half of the cofinality
that is free.
-/

/-- **The extension of the base ideal is topologically nilpotent**: for an arbitrary morphism of
formal spectra `m : Spf J ⟶ Spf I` whose action on global sections is the `R`-algebra structure of
`B`, the extended ideal `I · B` lies in the radical of `J`.

**Neither an open immersion nor any finiteness is used**, and that is the reusable fact: this is
half of the cofinality hypothesis of
`IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`, available for free and for every
morphism.

A prime of `B` containing `J` is a point `y` of `Spf J` (`FormalSpectrum.range_toPrimeSpectrum`);
its contraction along `globalSectionsMap I J m` is the point `m.base y` of `Spf I`
(`FormalSpectrum.base_toPrimeSpectrum_eq`, which needs no containment hypothesis); and a point of
`Spf I` is a prime containing `I`. `Ideal.map_le_iff_le_comap` turns that into the containment of
the extended ideal. It is the argument of `FormalSpectrum.zeroLocus_map_spfIsoRingEquiv`
(`FormalSchemes.SpfIsoIdealRecovery`) with only one of its two directions available; the other
direction is the openness half, and there the isomorphism's `e.inv` is what is missing. -/
theorem map_le_radical_of_hom (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (halg : algebraMap R B = globalSectionsMap I J m) :
    I.map (algebraMap R B) ≤ J.radical := by
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  intro b hb
  rw [PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  have hqr : q ∈ Set.range (toPrimeSpectrum J) := by
    rw [range_toPrimeSpectrum]; exact hq
  obtain ⟨y, rfl⟩ := hqr
  have hkey := base_toPrimeSpectrum_eq I J m y
  have hmem : toPrimeSpectrum I (m.base y) ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [← range_toPrimeSpectrum]; exact ⟨m.base y, rfl⟩
  rw [hkey] at hmem
  have hcomap : I ≤ Ideal.comap (algebraMap R B) (toPrimeSpectrum J y).asIdeal := by
    rw [halg]; exact hmem
  exact (Ideal.map_le_iff_le_comap.mpr hcomap) hb

/-- **The nilpotence half, in its power form.** `Ideal.exists_pow_le_of_le_radical_of_fg` converts
`FormalSpectrum.map_le_radical_of_hom` into a containment of a *power*, and that is the only place
finite generation of `I` is spent — through `Ideal.FG.map`, since it is `(I · B).FG` that is
wanted. -/
theorem exists_pow_map_le_of_hom (hI : I.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (halg : algebraMap R B = globalSectionsMap I J m) :
    ∃ k : ℕ, I.map (algebraMap R B) ^ k ≤ J :=
  Ideal.exists_pow_le_of_le_radical_of_fg (map_le_radical_of_hom I J m halg) (hI.map _)

/-- **`V (J) ⊆ V (I · B)`**, the geometric form of the nilpotence half: the closed subset of
`Spec B` underlying `Spf J` sits inside the one cut out by the extension of the base ideal. The
openness half is the reverse inclusion, and this file does not prove it. -/
theorem zeroLocus_subset_zeroLocus_map_of_hom
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (halg : algebraMap R B = globalSectionsMap I J m) :
    PrimeSpectrum.zeroLocus (J : Set B) ⊆
      PrimeSpectrum.zeroLocus (I.map (algebraMap R B) : Set B) := by
  rw [← PrimeSpectrum.zeroLocus_radical J]
  exact PrimeSpectrum.zeroLocus_anti_mono_ideal (map_le_radical_of_hom I J m halg)

/-!
### The assembly, and what is left

The openness half `J ≤ √(I · B)` is not proved here. What follows is the reduction of the
cofinality to it, its point-set content, and the class of opens for which it *is* settled.
-/

/-- **The cofinality, given the openness half alone.** The hypothesis of
`IsTopologicallyFiniteType.of_openImmersion_of_isCofinal` is a cofinality, which is two containments
of powers in opposite directions; this reduces it to the single containment `J ≤ √(I · B)`, since
the other direction is `FormalSpectrum.map_le_radical_of_hom` and is free.

`Ideal.IsCofinal.of_radical_eq` (`FormalSchemes.CofinalIdeal`) is the bridge and is where both
`hI` and `hJ` are spent. Note the hypothesis is stated at `J` rather than at `J.radical`:
`Ideal.radical_le_radical_iff` is what moves between the two. -/
theorem isCofinal_map_of_le_radical (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (halg : algebraMap R B = globalSectionsMap I J m)
    (hopen : J ≤ (I.map (algebraMap R B)).radical) :
    Ideal.IsCofinal J (I.map (algebraMap R B)) :=
  Ideal.IsCofinal.of_radical_eq hJ (hI.map _)
    (le_antisymm (Ideal.radical_le_radical_iff.mpr hopen)
      (Ideal.radical_le_radical_iff.mpr (map_le_radical_of_hom I J m halg)))

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J] in
/-- **The openness half, as a statement about points**: `I · B` is open in the `J`-adic topology
exactly when every prime of `B` containing `I · B` is a point of `Spf J`.

This is the precise form of what is left. `FormalSpectrum.map_le_radical_of_hom` says the reverse
containment holds always, i.e. every point of `Spf J` is such a prime; so the residue is that
`V (I · B)` contains no *extra* primes. A prime `q ⊇ I · B` with `q ⊉ J` is a point of `Spec B`
lying outside `Spf J`, about which the morphism `m` says nothing directly, and it is the reason
the argument of `FormalSpectrum.map_le_radical_of_hom` does not run backwards.

Nothing about `m` enters, so this is a restatement of the containment and not a theorem about
formal spectra; it earns a name because it is the shape a successor row has to attack, and because
`FormalSpectrum.range_toPrimeSpectrum` is what makes "is a point of `Spf J`" and "contains `J`"
the same thing. -/
theorem le_radical_map_iff_forall_mem_range :
    J ≤ (I.map (algebraMap R B)).radical ↔
      ∀ q : PrimeSpectrum B, I.map (algebraMap R B) ≤ q.asIdeal →
        q ∈ Set.range (toPrimeSpectrum J) := by
  rw [range_toPrimeSpectrum]
  constructor
  · intro h q hq
    exact h.trans ((Ideal.radical_mono hq).trans (Ideal.IsPrime.radical q.isPrime).le)
  · intro h
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
    intro b hb
    rw [PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    exact h q hq hb

/-!
### The basic-open case
-/

/-- **Cofinality depends only on the open subset, not on the presentation of it.** If two open
immersions `m : Spf J ⟶ Spf I` and `m' : Spf J' ⟶ Spf I` have the same range and the cofinality
holds for `m'`, it holds for `m`.

This is what makes the question well-posed as a question about opens of `Spf I`: the presentation
`(B, J)` of an affine open is not unique even up to isomorphism of ideals — `L` and `L ^ 2`
present the same open (`FormalSpectrum.cofinalSpfIso`) — but the property is insensitive to that.
It is also how `FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` is proved: settle the
statement at one convenient presentation, transport it to all the others.

`LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` turns the range equality into an isomorphism
*over* `Spf I`, `FormalSpectrum.spfIsoRingEquiv_comp_globalSectionsMap`
(`FormalSchemes.SpfIsoOverBase`) says the recovered ring isomorphism intertwines the two algebra
structures — so it carries `I · B'` onto `I · B` — and
`FormalSpectrum.isCofinal_map_spfIsoRingEquiv` says it moves `J'` to something cofinal with `J`.
Transitivity of `Ideal.IsCofinal` assembles the two. -/
theorem isCofinal_map_of_range_eq {B' : Type u} [CommRing B'] [TopologicalSpace B']
    {J' : Ideal B'} [IsAdicRing J'] [Algebra R B'] (hJ : J.FG) (hJ' : J'.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (m' : locallyRingedSpaceObj J' ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m']
    (halg : algebraMap R B = globalSectionsMap I J m)
    (halg' : algebraMap R B' = globalSectionsMap I J' m')
    (hrange : Set.range m.base = Set.range m'.base)
    (hcof' : Ideal.IsCofinal J' (I.map (algebraMap R B'))) :
    Ideal.IsCofinal J (I.map (algebraMap R B)) := by
  set e := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq m m' hrange with he
  have hfac : e.hom ≫ m' = m :=
    LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  have hcomm : (spfIsoRingEquiv e).toRingHom.comp (algebraMap R B') = algebraMap R B := by
    rw [halg, halg']
    exact spfIsoRingEquiv_comp_globalSectionsMap e m m' hfac
  have hmapeq : (I.map (algebraMap R B')).map (spfIsoRingEquiv e).toRingHom =
      I.map (algebraMap R B) := by rw [Ideal.map_map, hcomm]
  have hmoved := hcof'.map (spfIsoRingEquiv e).toRingHom
  rw [hmapeq] at hmoved
  exact ((isCofinal_map_spfIsoRingEquiv e hJ hJ').symm).trans hmoved

/-- **The cofinality holds when the open is basic**, for an arbitrary presentation of it: if
`Set.range m.base` is the range of the basic-open chart `Spf R{1/f}^ ⟶ Spf I`, then
`Ideal.IsCofinal J (I · B)`.

At the chart itself there is nothing to prove — `FormalSpectrum.map_awayCompletionHom` makes the
containment an *equality*, so the cofinality is reflexivity — and
`FormalSpectrum.isCofinal_map_of_range_eq` carries that to every other presentation of the same
open. The hypothesis is on the range and not on `m` itself, which is what makes this more than a
restatement of the chart case: `(B, J)` is arbitrary, and in particular `J` need not be `I · B`
nor even contained in it.

This was the largest class of opens for which the openness half was settled when it was written:
an affine open of `Spf I` need not be basic, and covering it by basic opens does not suffice by
itself — see the module docstring.

**Now a special case** of `FormalSpectrum.isCofinal_map_of_openImmersion`
(`FormalSchemes.AffineThickeningsOpenImmersion`), which settles every affine open and uses neither
`f` nor `hrange`. Kept because it is upstream of that file and cannot cite it. -/
theorem isCofinal_map_of_range_eq_basicOpenChart (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m) (f : R)
    (hrange : Set.range m.base = Set.range (basicOpenChart I f).base) :
    Ideal.IsCofinal J (I.map (algebraMap R B)) := by
  haveI : IsAdicRing (awayCompletionIdeal I f) := isAdicRing_awayCompletionIdeal I f hI
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f) :=
    isOpenImmersion_basicOpenChart I f hI
  have halgaway : algebraMap R (awayCompletion I f) = awayCompletionHom I f :=
    (awayCompletionHom_eq_algebraMap I f).symm
  have hchart : I.map (algebraMap R (awayCompletion I f)) = awayCompletionIdeal I f := by
    rw [halgaway]; exact map_awayCompletionHom I f
  refine isCofinal_map_of_range_eq I J hJ ?_ m (basicOpenChart I f) halg ?_ hrange ?_
  · rw [← hchart]; exact hI.map _
  · rw [globalSectionsMap_basicOpenChart, halgaway]
  · rw [hchart]

end Algebra

end FormalSpectrum

namespace AlgebraicGeometry

open FormalSpectrum

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
variable {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J]
variable [Algebra R B]

/-- **An affine open of `Spf I` is topologically of finite type over `(R, I)`, given only the
openness half.** `IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`
(`FormalSchemes.AffineOpenTopFiniteType`) with its cofinality hypothesis replaced by the single
containment `J ≤ √(I · B)`, through `FormalSpectrum.isCofinal_map_of_le_radical`.

The conclusion's ideal is `I · B` and could not be `J`: `IsTopologicallyFiniteType.map_eq` pins
it. -/
theorem _root_.IsTopologicallyFiniteType.of_openImmersion_of_le_radical (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m)
    (hopen : J ≤ (I.map (algebraMap R B)).radical) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
  IsTopologicallyFiniteType.of_openImmersion_of_isCofinal hI hJ m halg
    (isCofinal_map_of_le_radical I J hI hJ m halg hopen)

/-- **A basic affine open of `Spf I` is topologically of finite type over `(R, I)`, with no
hypothesis beyond finite generation.** If the range of the open immersion is that of a basic-open
chart, `FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` discharges the hypothesis of
`IsTopologicallyFiniteType.of_openImmersion_of_isCofinal` outright.

This is strictly more than `IsTopologicallyFiniteType.of_basicOpenChart`
(`FormalSchemes.AffineOpenTopFiniteType`), which is the case `m = FormalSpectrum.basicOpenChart I f`
on the nose: here `(B, J)` is an arbitrary presentation of the same open, so `J` is pinned only up
to cofinality, which is the strongest thing an open immersion determines. It was the first
unconditional case of conservativity's affine step.

**Now a special case** of `IsTopologicallyFiniteType.of_openImmersion`
(`FormalSchemes.AffineThickeningsOpenImmersion`), which drops the restriction to a basic range and
uses neither `f` nor `hrange`. Kept because it is upstream of that file and cannot cite it — and
because three module docstrings name it as the first unconditional case. -/
theorem _root_.IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m) (f : R)
    (hrange : Set.range m.base = Set.range (basicOpenChart I f).base) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
  IsTopologicallyFiniteType.of_openImmersion_of_isCofinal hI hJ m halg
    (isCofinal_map_of_range_eq_basicOpenChart I J hI hJ m halg f hrange)

/-- **Non-vacuity for the basic-open case, at a presentation that is not the chart itself.**
`D(t) = D(t * t)`, so `Spf R{1/(t * t)}^ ⟶ Spf I` is an open immersion whose range is that of the
chart at `t`, and
`IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen` applies with
`f := t` and `(B, J) := (R{1/(t * t)}^, awayCompletionIdeal I (t * t))`.

This is an application and not a restatement: the two rings are completions of two *different*
localizations of `R`, so `FormalSpectrum.isCofinal_map_of_range_eq` is exercised at a genuine pair
of presentations rather than at `m = FormalSpectrum.basicOpenChart I f`, where the range equality
would be `rfl`. It is the same witness that
`FormalSpectrum.spfIsoRingEquiv_isoOfRangeEq_comp_globalSectionsMap`
(`FormalSchemes.SpfIsoOverBase`) uses, read through this file's theorem.

Every `FormalSpectrum.awayCompletion*` name here carries its namespace prefix even though the file
opens `FormalSpectrum`: a declaration named `IsTopologicallyFiniteType.…` opens that namespace for
its own elaboration, and `IsTopologicallyFiniteType.awayCompletion` then shadows
`FormalSpectrum.awayCompletion`. The resulting error is `failed to synthesize CommRing (Ideal R)`,
which does not name the shadowed identifier. -/
theorem _root_.IsTopologicallyFiniteType.awayCompletion_sq_of_openImmersion (hI : I.FG) (t : R) :
    IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion I (t * t))
      (I.map (algebraMap R (FormalSpectrum.awayCompletion I (t * t)))) := by
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal I t) :=
    isAdicRing_awayCompletionIdeal I t hI
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal I (t * t)) :=
    isAdicRing_awayCompletionIdeal I (t * t) hI
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart I (t * t)) :=
    isOpenImmersion_basicOpenChart I (t * t) hI
  have halgaway : algebraMap R (FormalSpectrum.awayCompletion I (t * t)) =
      FormalSpectrum.awayCompletionHom I (t * t) :=
    (FormalSpectrum.awayCompletionHom_eq_algebraMap I (t * t)).symm
  have hfg : (FormalSpectrum.awayCompletionIdeal I (t * t)).FG :=
    FormalSpectrum.awayCompletionIdeal_fg I (t * t) hI
  have hrange : Set.range (basicOpenChart I (t * t)).base
      = Set.range (basicOpenChart I t).base := by
    rw [range_basicOpenChart_base I (t * t) hI, range_basicOpenChart_base I t hI,
      basicOpen_mul, TopologicalSpace.Opens.coe_inf, Set.inter_self]
  exact IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen hI hfg _
    (by rw [globalSectionsMap_basicOpenChart, halgaway]) t hrange

/-- **Non-vacuity, through a genuinely non-reflexive instance.** `FormalSpectrum.cofinalSpfIso`
presents `Spf I` at the ideal `I ^ 2`; the resulting isomorphism `Spf (I ^ 2) ≅ Spf I` is an open
immersion, its action on global sections is the identity of `R`, and the openness hypothesis it
has to satisfy is `I ^ 2 ≤ √I`, which is not reflexivity and is not closed by `rfl`.

That is the bar for anything about `Ideal.IsCofinal`, in the sense of
`IsTopologicallyFiniteType.self_of_two_charts_pow`
(`FormalSchemes.CofinalTopFiniteTypeAffineLocal`), whose conclusion this shares and whose route it
does not: that one covers `Spf (I ^ 2)` by the two charts `D(a)` and `D(1 - a)`, this one runs the
whole open-immersion machinery on a single open immersion which happens to be an isomorphism.

`Γ` of the comparison isomorphism is computed rather than assumed: `cofinalSpfIso` is the inverse
of `FormalSpectrum.locallyRingedSpaceMap` at `RingHom.id R`, so
`FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap` and
`FormalSpectrum.globalSectionsMap_comp` identify it with the identity. -/
theorem _root_.IsTopologicallyFiniteType.self_of_openImmersion_pow (hI : I.FG) :
    IsTopologicallyFiniteType R I R (I.map (algebraMap R R)) := by
  haveI : IsAdicRing (I ^ 2) := IsAdicRing.of_isCofinal (Ideal.IsCofinal.pow I two_ne_zero)
  have hle : I ^ 2 ≤ I := Ideal.pow_le_self two_ne_zero
  have hIsq : (I ^ 2).FG := hI.pow
  haveI := isIso_locallyRingedSpaceMapId (I ^ 2) I hle hIsq hI
  set e := cofinalSpfIso (I ^ 2) I hle hIsq hI with he
  haveI : LocallyRingedSpace.IsOpenImmersion e.hom := inferInstance
  have hself : I.map (algebraMap R R) = I := by rw [Algebra.algebraMap_self, Ideal.map_id]
  -- `Γ` of the comparison isomorphism is the identity of `R`.
  have hg : algebraMap R R = globalSectionsMap I (I ^ 2) e.hom := by
    have hu := globalSectionsMap_locallyRingedSpaceMap (I ^ 2) I (RingHom.id R)
      (le_comap_id_of_le (I ^ 2) I hle)
    have hcomp := globalSectionsMap_comp (I := I ^ 2) (J := I) (K := I ^ 2) e.hom
      (locallyRingedSpaceMap (I ^ 2) I (RingHom.id R) (le_comap_id_of_le (I ^ 2) I hle))
    rw [hu, RingHom.comp_id] at hcomp
    have hid : e.hom ≫ locallyRingedSpaceMap (I ^ 2) I (RingHom.id R)
        (le_comap_id_of_le (I ^ 2) I hle) = 𝟙 _ := by
      rw [he, cofinalSpfIso]; exact IsIso.inv_hom_id _
    rw [Algebra.algebraMap_self, ← hcomp, hid, globalSectionsMap_id]
  exact IsTopologicallyFiniteType.of_openImmersion_of_le_radical hI hIsq e.hom hg
    (by rw [hself]; exact hle.trans Ideal.le_radical)

end AlgebraicGeometry
