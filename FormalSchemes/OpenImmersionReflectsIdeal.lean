import FormalSchemes.SpfGammaSheafComponentArbComp

set_option linter.style.header false
set_option linter.style.setOption false

/-!
# Reflecting the ideal of definition through the sheaf component of an open immersion

Let `w : Spf L ⟶ Spf J` be a morphism of formal spectra (`w : locallyRingedSpaceObj L ⟶
locallyRingedSpaceObj J`), `Ψ := globalSectionsMap J L w : S → S_L` the induced map on global
sections, and `g t : S`. The basic-open sheaf component `arbSheafComponent J L w g :
R{1/g} →+* S_L{1/Ψg}` fits into the naturality square `θ ∘ awayCompletionHom J g = awayCompletionHom
L (Ψg) ∘ Ψ` (`arbSheafComponent_comp_awayCompletionHom`).

This file records the **reduction of the adic-source-descent crux (issue 471a / 480)** to two
isolated facts. The naive statement "`Ψ t ∈ L ⟹ awayCompletionHom J g t ∈ awayCompletionIdeal J g`"
is *false* for an arbitrary locally-ringed-space open immersion (counterexample: the reversed
cofinal isomorphism `Spf (y) ⟶ Spf (y²)`, where the source ideal of definition `(y)` is **not**
contained in the restriction `(y²)` — see the issue-480 discussion). It becomes true once one
supplies:

* `(A)` `arbSheafComponent J L w g` is **bijective** — a ring iso, which holds for an open immersion
  over basic opens contained in its range; and
* `(B)` `L ≤ Ideal.map Ψ J` — the containment "`L ⊆` restriction of `J` over the range".

Given `(A)` and `(B)`, reflection is elementary ideal algebra (`Ideal.map_map`, `Ideal.map_mono`,
`Ideal.comap_map_of_surjective`), carried out here in `reflects_awayCompletionIdeal_of_bijective`.
The remaining crux — `(A)`, the open-immersion sheaf-component iso over the range — is the reusable
infrastructure the parent (471a) still needs; `(B)` is discharged for the concrete
`liftedBasicCover` pieces the consumer (471c/472) uses, where `L` is the honest
completed-localization ideal.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12.
-/

noncomputable section

open TopologicalSpace Topology Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-- **The reduction of the adic-source reflection to (A) bijectivity + (B) containment.**
For `w : Spf S ⟶ Spf R`, write `Ψ := globalSectionsMap I J w`, `θ := arbSheafComponent I J w g`.
If `θ` is bijective (a ring iso — `(A)`, e.g. `w` an open immersion over `D(g) ⊆ range w.base`) and
`J ≤ Ideal.map Ψ I` (`(B)`, "`J ⊆` restriction of `I`"), then `Ψ` reflects the ideal of definition:
`Ψ t ∈ J` forces `awayCompletionHom I g t ∈ awayCompletionIdeal I g`. This is the elementary,
`(A)`/`(B)`-conditional core of issue 471a. -/
theorem reflects_awayCompletionIdeal_of_bijective
    (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g t : R)
    (hbij : Function.Bijective (arbSheafComponent I J w g))
    (hres : J ≤ Ideal.map (globalSectionsMap I J w) I)
    (ht : globalSectionsMap I J w t ∈ J) :
    awayCompletionHom I g t ∈ awayCompletionIdeal I g := by
  set Ψ := globalSectionsMap I J w with hΨ
  set θ := arbSheafComponent I J w g with hθ
  set Φ := awayCompletionHom I g with hΦ
  set ψ := awayCompletionHom J (Ψ g) with hψ
  -- `K := awayCompletionIdeal I g = Ideal.map Φ I`.
  have hK : awayCompletionIdeal I g = Ideal.map Φ I := (map_awayCompletionHom I g).symm
  -- Step a: `θ (Φ t) = ψ (Ψ t)` from the naturality square.
  have hnat : θ.comp Φ = ψ.comp Ψ := arbSheafComponent_comp_awayCompletionHom I J w g
  have ha : θ (Φ t) = ψ (Ψ t) := by
    have := RingHom.congr_fun hnat t; simpa [RingHom.comp_apply] using this
  -- Step b: `ψ (Ψ t) ∈ awayCompletionIdeal J (Ψ g) = Ideal.map ψ J`.
  have hb : θ (Φ t) ∈ Ideal.map ψ J := by
    rw [ha]; exact Ideal.mem_map_of_mem ψ ht
  -- Step c: `Ideal.map ψ J ⊆ Ideal.map θ (awayCompletionIdeal I g)`.
  have hc : Ideal.map ψ J ≤ Ideal.map θ (awayCompletionIdeal I g) := by
    rw [hK, Ideal.map_map, hnat, ← Ideal.map_map]
    exact Ideal.map_mono hres
  -- Step d–f: reflect through the bijective `θ`.
  set K := awayCompletionIdeal I g with hKdef
  have hd : θ (Φ t) ∈ Ideal.map θ K := hc hb
  have hcomap : Ideal.comap θ (Ideal.map θ K) = K := by
    rw [Ideal.comap_map_of_surjective θ hbij.2, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot θ).mp hbij.1, sup_bot_eq]
  have : Φ t ∈ Ideal.comap θ (Ideal.map θ K) := Ideal.mem_comap.mpr hd
  rwa [hcomap] at this

end FormalSpectrum

end
