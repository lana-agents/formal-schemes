import FormalSchemes.AwayBaseChangeSeparated
import FormalSchemes.OpenFormalSubscheme

set_option linter.style.header false

/-!
# A morphism that factors through the basic open of its base has its whole source over it

`FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough`
(`FormalSchemes.AwayBaseChangeSeparated`) is row 1987's statement **(B)**: separatedness over
`Spf R` descends along a change of *base* from `Spf R` to the basic open `Spf R{1/f}`, for a source
whose structural morphism factors through that basic open. Its hypothesis is a factorisation

```
t : X ⟶ Spf R{1/f}    with    t ≫ awayBaseChart I f = sX
```

and the question this file answers is **how much that hypothesis asks for**. The answer is: all of
it. A factorisation exists only if the *entire* source already lies over `D(f)`.

## The obstruction

`FormalSpectrum.awayBaseChart I f` is `FormalSpectrum.locallyRingedSpaceMap` of
`algebraMap R (R{1/f})`, and `f` is a unit there
(`FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le` at `g = f`). A point of `Spf S` is an
open prime of `S`, the base map sends it to its preimage in `R`, and no prime contains a unit — so
every point in the range of the chart lies in `D(f)`. That is
`FormalSpectrum.range_awayBaseChart_base_subset`, and it is proved from a statement about an
arbitrary `FormalSpectrum.map` (`FormalSpectrum.map_mem_basicOpen_iff`,
`FormalSpectrum.range_map_subset_basicOpen_of_isUnit`) rather than from the chart's own range
computation `FormalSpectrum.range_basicOpenChart_base`, which is stated at the
`FormalSpectrum.awayCompletionIdeal` spelling of the ideal of definition and would need a transport
to reach the `I.map (algebraMap R (awayCompletion I f))` spelling this file's consumers use.

Composing, a factorisation forces `Set.range sX.base ⊆ D(f)`
(`FormalScheme.range_base_subset_basicOpen_of_factorsThrough`), and therefore **one point of the
source over the complement of `D(f)` refutes every factorisation at once**
(`FormalScheme.not_exists_factorsThrough_awayBase`).

## What this settles about §10.15's open directions

Row 1987's decomposition of §10.15 says that conservativity's hard direction — from
`FormalScheme.IsSeparatedHom hX (locallyFG_Spf hI) g` back to
`FormalScheme.IsSeparatedOverSpf hI X g.toLRSHom` — is statement **(B)** specialised to the
basic-open refinement of the target cover that `FormalSchemes.TargetBasicRefinement` supplies for
§10.13. **It is not**, and the theorems above are why.

That route takes a basic open `D(d) ⊆ V j` of the target inside a member of the witness cover, and
wants separatedness of `X|_{g⁻¹D(d)}` over the away base. The object the witness supplies
separatedness of is `X|_{g⁻¹(V j)}`, over the whole of `V j` and not over `D(d)`, and as soon as
that object has **one** point over `V j` outside `D(d)` —
which is the general case, and is what the refinement is refining away —
`FormalScheme.not_exists_factorsThrough_awayBase` says there is no `t` at that source. So **(B)
does not apply until the source has been shrunk to `X|_{g⁻¹D(d)}`**, and shrinking the source over
a fixed base is statement **(A)**: the step needs **(A) then (B)**, in that order.

`FormalSchemes.TargetBasicRefinement` does shrink a source along with the target — that is what
`AlgebraicGeometry.FormalScheme.BasicTargetChart.src` is — but what it shrinks is an **affine**
chart of `X`, which carries no separatedness statement. The object whose separatedness the witness
of `FormalScheme.IsSeparatedHom` names is the open formal subscheme `X|_{g⁻¹(V j)}`, and nothing
in that refinement restricts *it*.

`FormalScheme.isSeparatedOverSpf_restrictOpen_awayBase_of_restrictOpen` is that composite, stated
with (A) as an explicit hypothesis at the open it is applied to: once (A) is available the step is
one application of (B), and the two theorems together bracket the question from both sides — the
composite says (A) suffices, the obstruction says nothing weaker than (A) will do.

**(A) at a general presented `X` is not proved here and is not proved anywhere on this tree.**
`FormalScheme.isSeparatedOverSpf_restrictOpen_Spf` (`FormalSchemes.SpfOpenSeparated`) has it at
`X = FormalScheme.Spf A`, where the presentation is *built* out of basic opens rather than
restricted from a given one, and that module says in terms that the general case is not attempted.

## Placement

A new module rather than a section of `FormalSchemes.AwayBaseChangeSeparated`, which is where (B)
and the rest of the factorisation API live. That file does not import
`FormalSchemes.OpenFormalSubscheme`, which the composite below needs to name
`FormalScheme.restrictOpen`, and putting the composite there would push that import onto every one
of that module's dependents to serve one theorem. The first three results would fit there; the
module is not worth splitting in two to save one import edge on a leaf.

`FormalSchemes.AwayBaseFactorisationRange` has reverse closure **0** and forward closure **203**,
against `FormalSchemes.AwayBaseChangeSeparated`'s forward closure of **201**. The difference is
that module itself together with `FormalSchemes.OpenFormalSubscheme`, whose own forward closure of
**32** already lies inside it.

## Main results

* `FormalSpectrum.map_mem_basicOpen_iff`: a point of `Spf S` maps into `D(f)` exactly when it lies
  in `D(φ f)`.
* `FormalSpectrum.range_awayBaseChart_base_subset`: the basic-open chart of the base lands in
  `D(f)`.
* `AlgebraicGeometry.FormalScheme.range_base_subset_basicOpen_of_factorsThrough`: **a factorisation
  through the basic open puts the whole source over it.**
* `AlgebraicGeometry.FormalScheme.not_exists_factorsThrough_awayBase`: **one point outside `D(f)`
  refutes every factorisation**, which is what makes (B) unavailable at an unshrunk source.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_restrictOpen_awayBase_of_restrictOpen`: the
  (A)-then-(B) composite, with (A) as a hypothesis.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
* `FormalSchemes.AwayBaseChangeSeparated` — statement (B), and the rest of the factorisation API
  this file's obstruction sits beside.
* `FormalSchemes.SpfOpenSeparated` — statement (A) at an affine source.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry FormalSpectrum

universe u

namespace FormalSpectrum

section MapBasicOpen

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type u} [CommRing S] (J : Ideal S)

/-- **A point maps into `D(f)` exactly when it lies in `D(φ f)`.** `FormalSpectrum.map` is
`PrimeSpectrum.comap` of `Ideal.quotientMap`, so membership at the image unfolds to membership of
the image residue, and `Ideal.quotientMap_mk` identifies that with the residue of `φ f`. -/
theorem map_mem_basicOpen_iff (φ : R →+* S) (h : I ≤ J.comap φ) (f : R) (v : FormalSpectrum J) :
    map I J φ h v ∈ basicOpen I f ↔ v ∈ basicOpen J (φ f) := by
  rw [mem_basicOpen, mem_basicOpen]
  change Ideal.Quotient.mk I f ∉ Ideal.comap _ v.asIdeal ↔ _
  rw [Ideal.mem_comap, Ideal.quotientMap_mk]

/-- **If `φ` inverts `f` then `Spf φ` lands in `D(f)`.** By
`FormalSpectrum.map_mem_basicOpen_iff` the image of a point lies in `D(f)` exactly when the point
lies in `D(φ f)`, and a unit lies in no prime. -/
theorem range_map_subset_basicOpen_of_isUnit (φ : R →+* S) (h : I ≤ J.comap φ) {f : R}
    (hf : IsUnit (φ f)) :
    Set.range (map I J φ h) ⊆ (basicOpen I f : Set (FormalSpectrum I)) := by
  rintro _ ⟨v, rfl⟩
  rw [SetLike.mem_coe, map_mem_basicOpen_iff]
  exact fun hmem => v.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem (hf.map (Ideal.Quotient.mk J)))

end MapBasicOpen

section AwayBaseRange

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R)

/-- **The basic open of the base lands in `D(f)`.** `FormalSpectrum.awayBaseChart` is
`FormalSpectrum.locallyRingedSpaceMap` of `algebraMap R (R{1/f})`, which inverts `f`
(`FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le` at `g = f`, where the hypothesis is
`le_rfl`), so `FormalSpectrum.range_map_subset_basicOpen_of_isUnit` applies.

Stated as an inclusion rather than the equality `FormalSpectrum.range_basicOpenChart_base` gives,
because only the inclusion is used below and the equality is stated at the
`FormalSpectrum.awayCompletionIdeal` spelling of the ideal of definition, which would need a
transport to reach the spelling `FormalSpectrum.awayBaseChart` is written at. -/
theorem range_awayBaseChart_base_subset [TopologicalSpace R] [IsAdicRing I]
    [IsAdicRing (I.map (algebraMap R (awayCompletion I f)))] (hI : I.FG) :
    Set.range (awayBaseChart I f).base ⊆ (basicOpen I f : Set (FormalSpectrum I)) := by
  have hu : IsUnit (algebraMap R (awayCompletion I f) f) := by
    rw [← awayCompletionHom_eq_algebraMap]
    exact isUnit_awayCompletionHom_of_basicOpen_le I f f hI le_rfl
  exact range_map_subset_basicOpen_of_isUnit I _ (algebraMap R (awayCompletion I f))
    Ideal.le_comap_map hu

end AwayBaseRange

end FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable [TopologicalSpace R] [IsAdicRing I]
variable [IsAdicRing (I.map (algebraMap R (awayCompletion I f)))]

include hI in
/-- **A factorisation through the basic open of the base puts the whole source over it.** The
structural morphism is the factorisation followed by
`FormalSpectrum.awayBaseChart`, so its range is contained in the chart's, which is contained in
`D(f)` by `FormalSpectrum.range_awayBaseChart_base_subset`.

This is the necessary condition hidden in the hypothesis `ht` of
`FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough`: statement (B) is not available at a
source that sticks out of `D(f)`, however separated that source is over `Spf R`. -/
theorem range_base_subset_basicOpen_of_factorsThrough {X : FormalScheme.{u}}
    {sX : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (t : X.toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (ht : t ≫ awayBaseChart I f = sX) :
    Set.range sX.base ⊆ (basicOpen I f : Set (FormalSpectrum I)) := by
  subst ht
  rintro _ ⟨x, rfl⟩
  exact range_awayBaseChart_base_subset I f hI ⟨t.base x, rfl⟩

include hI in
/-- **One point of the source outside `D(f)` refutes every factorisation.** The contrapositive of
`FormalScheme.range_base_subset_basicOpen_of_factorsThrough` at a single point, which is the form
the argument about conservativity's hard direction uses: there the source is `X|_{g⁻¹(V j)}` for a
member `V j` of an arbitrary witness cover, `D(f)` is a basic open strictly inside `V j`, and any
point of the source over `V j \ D(f)` is the witness. -/
theorem not_exists_factorsThrough_awayBase {X : FormalScheme.{u}}
    {sX : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I} (x : X)
    (hx : sX.base x ∉ basicOpen I f) :
    ¬ ∃ t : X.toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))),
      t ≫ awayBaseChart I f = sX := by
  rintro ⟨t, ht⟩
  exact hx (range_base_subset_basicOpen_of_factorsThrough hI f t ht ⟨x, rfl⟩)

/-- **(A) then (B): source restriction followed by the change of base.** With separatedness of the
restricted source over `Spf R` supplied — statement (A) at the open `W`, which is what this
hypothesis is — the change of base to `Spf R{1/f}` is one application of
`FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough`.

Stated with (A) as a hypothesis rather than proved outright because (A) at a general presented `X`
is not on the tree; what this records is that **nothing else is missing** from the step
conservativity's hard direction needs. Read against
`FormalScheme.not_exists_factorsThrough_awayBase`, which says the same step cannot be taken before
the source is shrunk, it locates the whole of the remaining work in (A).

The instance `IsAdicRing (I.map (algebraMap R (awayCompletion I f)))` is a spelling rather than a
restriction: it is `FormalSpectrum.isAdicRing_awayCompletionIdeal` transported along
`FormalSpectrum.map_awayCompletionHom`, exactly as the `haveI` inside
`FormalSchemes.AwayBaseChangeSeparated` does. It appears as an instance binder here because (B)
states it that way and the conclusion's type mentions it. -/
theorem isSeparatedOverSpf_restrictOpen_awayBase_of_restrictOpen {X : FormalScheme.{u}}
    (hX : X.LocallyFG) (W : Opens X)
    {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (hA : IsSeparatedOverSpf hI (X.restrictOpen hX W) (X.restrictOpenι hX W ≫ s))
    (t : (X.restrictOpen hX W).toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (ht : t ≫ awayBaseChart I f = X.restrictOpenι hX W ≫ s) :
    IsSeparatedOverSpf (hI.map (algebraMap R (awayCompletion I f))) (X.restrictOpen hX W) t :=
  isSeparatedOverSpf_awayBase_of_factorsThrough hI f t ht hA

end AlgebraicGeometry.FormalScheme

end
