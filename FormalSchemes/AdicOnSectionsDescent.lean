import FormalSchemes.OpenImmersionSheafComponentIso
import FormalSchemes.BasicOpenCoverVanishing
import FormalSchemes.SpfGammaFunctorial

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Adicity on global sections is local on the source

The general statement "an open immersion of affine adic formal spectra is adic on global sections"
is FALSE (issue 460): `IsAdicRing L` fixes only the topology, not the ideal `L`. But adicity on
global sections is a *local* condition on the source: if a morphism `φ : Spf J ⟶ Spf I` becomes
adic on global sections after restriction to an open cover of the source, then `φ` itself is adic on
global sections. This is the structure-sheaf-separatedness content behind the fibre-product
diagonal's continuity witnesses (issue 235c) and the general §10.15 separatedness program.

## The containment hypothesis `(B)`

The bare cover statement — with the pieces' source ideals `Lᵥ` only constrained by `[IsAdicRing]` —
is **false**: an open immersion may realise a *coarser* ideal of definition than the honest
restriction of `J` over its range (the reversed cofinal iso `Spf₍y₎ ⟶ Spf₍y²₎`, cf. issue 480), so
`globalSectionsMap wᵥ t ∈ Lᵥ` need not mean "`t` vanishes over `range wᵥ`". The descent therefore
carries the per-piece containment `hres : Lᵥ ≤ Ideal.map (globalSectionsMap J Lᵥ wᵥ) J` — hypothesis
`(B)` of `FormalSpectrum.reflects_awayCompletionIdeal`. It holds for the concrete
completed-localization pieces the consumer (472) covers with: for `wᵥ ≫ φ = basicOpenChart` pieces
`Lᵥ = awayCompletionIdeal …` and `(B)` is `map_awayCompletionHom` (equality).

## Main result

* `FormalSpectrum.le_comap_globalSectionsMap_of_cover`: adicity on global sections descends along an
  open cover of the source, given the per-piece containment `(B)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §§10.4.6, 10.12.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S)
  [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-- **Adicity on global sections descends along an open cover of the source.**
Let `φ : Spf J ⟶ Spf I` and let `{wᵥ : Spf Lᵥ ⟶ Spf J}` be a family of open immersions whose base
images cover `Spf J`. If `J` is finitely generated, every piece's source ideal is contained in the
restriction of `J` over its range (hypothesis `(B)` `hres`), and every composite `wᵥ ≫ φ` is adic on
global sections, then `φ` itself is adic on global sections. -/
theorem le_comap_globalSectionsMap_of_cover
    (φ : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    {ιidx : Type u} {Sv : ιidx → Type u} [∀ v, CommRing (Sv v)] [∀ v, TopologicalSpace (Sv v)]
    (Lv : ∀ v, Ideal (Sv v)) [∀ v, IsAdicRing (Lv v)]
    (wv : ∀ v, locallyRingedSpaceObj (Lv v) ⟶ locallyRingedSpaceObj J)
    [∀ v, LocallyRingedSpace.IsOpenImmersion (wv v)]
    (hJ : J.FG)
    (hcover : ⋃ v, Set.range (wv v).base = Set.univ)
    (hres : ∀ v, Lv v ≤ Ideal.map (globalSectionsMap J (Lv v) (wv v)) J)
    (hadic : ∀ v, I ≤ (Lv v).comap (globalSectionsMap I (Lv v) (wv v ≫ φ))) :
    I ≤ J.comap (globalSectionsMap I J φ) := by
  intro k hk
  rw [Ideal.mem_comap]
  set t := globalSectionsMap I J φ k with ht_def
  -- Step 1: over each piece `v`, the section `t` vanishes, i.e. `wᵥ` maps `t` into `Lᵥ`.
  have hstep1 : ∀ v, globalSectionsMap J (Lv v) (wv v) t ∈ Lv v := by
    intro v
    have h := hadic v hk
    rw [Ideal.mem_comap, globalSectionsMap_comp, RingHom.comp_apply, ← ht_def] at h
    exact h
  -- Step 2: the basic opens `D(g)` with `D(g) ⊆ range wᵥ` cover `Spf J`, and `t` vanishes on each.
  refine mem_of_forall_basicOpen J hJ t
    {g | ∃ v, (basicOpen J g : Set (FormalSpectrum J)) ⊆ Set.range (wv v).base} ?_ ?_
  · -- The spanning condition, via the empty zero locus of the residues.
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span,
      Set.eq_empty_iff_forall_notMem]
    intro x
    rw [PrimeSpectrum.mem_zeroLocus]
    intro hsub
    -- `x` lies in the range of some piece `wᵥ`; that range is open.
    obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp (hcover.ge (Set.mem_univ x))
    have H : LocallyRingedSpace.IsOpenImmersion (wv v) := inferInstance
    have hopen : IsOpen (Set.range (wv v).base) := H.base_open.isOpen_range
    -- Basic opens form a basis: pick `D(g)` with `x ∈ D(g) ⊆ range wᵥ`.
    obtain ⟨b, ⟨g, rfl⟩, hxg, hgsub⟩ :=
      (isTopologicalBasis_basicOpen J).exists_subset_of_mem_open hxv hopen
    exact (FormalSpectrum.mem_basicOpen J g x).mp hxg (hsub (Set.mem_image_of_mem _ ⟨v, hgsub⟩))
  · -- The vanishing condition, via the reflection lemma for each piece.
    intro g hg'
    obtain ⟨v, hgv⟩ := hg'
    exact reflects_awayCompletionIdeal J (Lv v) (wv v) g t hgv (hres v) (hstep1 v)

end FormalSpectrum

end
