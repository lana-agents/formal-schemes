import FormalSchemes.AdicOnBasicOpenSections

set_option linter.style.header false

/-!
# Adicity of a sheaf component over an *arbitrary* open

`FormalSchemes.AdicOnBasicOpenSections` (issue 1290) supplies the structural map
`R → Γ(D(f), O_{Spf R})` and the ideal it extends to, but only over a **basic** open, because
`FormalSpectrum.sectionsBasicOpenEquiv` is what identifies that section ring with a completed
localization. A continuity obligation on a `.c.app` does not need that identification: the
statement "`v ∈ K ^ m → F v ∈ L ^ m`" only needs the two ideals, and both are the extension of the
base ideal along the structural map.

This file therefore drops the basic-open restriction. For an arbitrary open `U` of `Spf R` it
defines the structural map `FormalSpectrum.sectionsOpenHom` and the ideal it extends to,
`FormalSpectrum.sectionsOpenIdeal`, and proves that the sheaf component of **any** morphism of
formal spectra is adically continuous for them, provided its global-sections map is.

## Main results

* `Ideal.map_pow_map_le_pow_map_of_comp` — the ring-theoretic content, with no geometry in it:
  a commuting square `c ∘ sA = sB ∘ φ` together with `K.map φ ≤ L` carries the extension
  filtration `(K.map sA) ^ m` into `(L.map sB) ^ m`.
* `FormalSpectrum.sectionsOpenHom`, `FormalSpectrum.sectionsOpenIdeal` — the structural map
  `R →+* Γ(U, O_{Spf R})` and `I.map` of it, for an arbitrary open `U`. Over a basic open they
  agree with `FormalSpectrum.sectionsBasicOpenHom` and `FormalSpectrum.sectionsBasicOpenIdeal`
  (`FormalSpectrum.sectionsOpenHom_basicOpen`, `FormalSpectrum.sectionsOpenIdeal_basicOpen`).
* `FormalSpectrum.comp_sectionsOpenHom` — **the naturality square**: for
  `w : Spf S ⟶ Spf R` and any open `U`,
  `w.c.app (op U) ∘ sectionsOpenHom I U = sectionsOpenHom J (w⁻¹ U) ∘ globalSectionsMap I J w`.
  This is the arbitrary-open analogue of
  `FormalSpectrum.arbSheafComponent_comp_awayCompletionHom`, and its proof is the same one
  without the two `sectionsBasicOpenEquiv` conjugations.
* `FormalSpectrum.map_sectionsOpenIdeal_pow_le` and
  `FormalSpectrum.sectionsComponent_mem_pow` — **the payoff**: `w.c.app (op U)` carries
  `sectionsOpenIdeal I U ^ m` into `sectionsOpenIdeal J (w⁻¹ U) ^ m`, as an ideal containment and
  as a membership implication. The hypothesis is `I ≤ J.comap (globalSectionsMap I J w)`.
* `FormalSpectrum.comp_eqToHom_sectionsOpenHom`,
  `FormalSpectrum.map_eqToHom_sectionsOpenIdeal` and
  `FormalSpectrum.mem_pow_map_eqToHom_sectionsOpenIdeal` — an equality of opens transports the
  structural map, its ideal and every power of that ideal, so a leg that composes a `.c.app` with
  an `eqToHom` presheaf transport costs no new argument.

## What is *not* proved

* **Nothing here says an arbitrary morphism of formal spectra is adic on global sections.** That
  statement is recorded false in `FormalSchemes.AdicOnSections`' module docstring (issue 460), and
  the hypothesis `I ≤ J.comap (globalSectionsMap I J w)` is carried as an explicit argument in
  every statement below, never derived.
* **`FormalSpectrum.sectionsOpenIdeal I U` is not shown to be finitely generated, Hausdorff or
  complete**, and it is not compared with any other ideal of `Γ(U)` beyond the basic-open case
  handled by `FormalSpectrum.sectionsOpenIdeal_basicOpen`.
* No `AlgHom` structure is put on any section ring, and
  `FormalSpectrum.sectionsBasicOpenEquiv` is not shown to be a map of `R`-algebras.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4, §10.4.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

/-- **A commuting square of ring homomorphisms carries one extension filtration into another.**
If `c ∘ sA = sB ∘ φ` and `φ` sends `K` into `L`, then `c` sends the `m`-th power of the extension
of `K` along `sA` into the `m`-th power of the extension of `L` along `sB`.

This is the whole of the continuity argument for a sheaf component: the two ideals of definition
are extensions of one ideal downstairs, and the component commutes with the two structural maps.
No topology, no completion and no geometry occur. -/
theorem Ideal.map_pow_map_le_pow_map_of_comp {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] {φ : A →+* B} {sA : A →+* C} {sB : B →+* D} {c : C →+* D}
    (hc : c.comp sA = sB.comp φ) {K : Ideal A} {L : Ideal B} (hKL : K.map φ ≤ L) (m : ℕ) :
    ((K.map sA) ^ m).map c ≤ (L.map sB) ^ m :=
  calc ((K.map sA) ^ m).map c = ((K ^ m).map φ).map sB := by
        rw [← Ideal.map_pow, Ideal.map_map, hc, ← Ideal.map_map]
    _ ≤ (L ^ m).map sB := Ideal.map_mono (by rw [Ideal.map_pow]; exact pow_le_pow_left' hKL m)
    _ = (L.map sB) ^ m := Ideal.map_pow sB L m

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-!
### The structural map over an arbitrary open
-/

/-- **The structural map `R → Γ(U, O_{Spf R})` for an arbitrary open `U`**: restrict the global
section attached to `x : R` by `FormalSpectrum.globalSectionsEquiv` along the inclusion `U ⊆ ⊤`.

The inclusion is spelled `homOfLE (le_top (a := U))`, matching
`FormalSpectrum.sectionsBasicOpenHom` and `FormalSpectrum.awayCompletionHom_eq_restrict`; every
consumer has to match that spelling. -/
def sectionsOpenHom (U : Opens (FormalSpectrum I)) :
    R →+* ((structureSheaf I).presheaf.obj (op U) : Type u) :=
  (((structureSheaf I).presheaf.map (homOfLE (le_top (a := U))).op).hom).comp
    (globalSectionsEquiv I).symm.toRingHom

/-- **The ideal of definition of `Γ(U, O_{Spf R})`**: the extension of `I` along the structural
map. Over a basic open this is `FormalSpectrum.sectionsBasicOpenIdeal`, by
`FormalSpectrum.sectionsOpenIdeal_basicOpen`. -/
def sectionsOpenIdeal (U : Opens (FormalSpectrum I)) :
    Ideal ((structureSheaf I).presheaf.obj (op U) : Type u) :=
  I.map (sectionsOpenHom I U)

/-- Over a basic open the structural map is `FormalSpectrum.sectionsBasicOpenHom`, on the nose. -/
theorem sectionsOpenHom_basicOpen (f : R) :
    sectionsOpenHom I (basicOpen I f) = sectionsBasicOpenHom I f :=
  rfl

/-- Over a basic open the ideal is `FormalSpectrum.sectionsBasicOpenIdeal`, i.e. the contraction of
`FormalSpectrum.awayCompletionIdeal` along `FormalSpectrum.sectionsBasicOpenEquiv`. This is
`FormalSpectrum.map_sectionsBasicOpenHom` (`FormalSchemes.AdicOnBasicOpenSections`). -/
theorem sectionsOpenIdeal_basicOpen (f : R) :
    sectionsOpenIdeal I (basicOpen I f) = sectionsBasicOpenIdeal I f :=
  map_sectionsBasicOpenHom I f

/-!
### Transport along an equality of opens
-/

/-- **An equality of opens transports the structural map.** Both sides are restrictions from `⊤`,
and restriction maps in the thin category `Opens` are unique, so the transport is absorbed. -/
theorem comp_eqToHom_sectionsOpenHom {U₁ U₂ : Opens (FormalSpectrum I)} (h : U₁ = U₂) :
    (((structureSheaf I).presheaf.map (eqToHom (congrArg op h))).hom).comp
        (sectionsOpenHom I U₁) = sectionsOpenHom I U₂ := by
  refine RingHom.ext fun r => ?_
  have hmorph : (homOfLE (le_top (a := U₁))).op ≫ eqToHom (congrArg op h) =
      (homOfLE (le_top (a := U₂))).op := Subsingleton.elim _ _
  have hcat : (structureSheaf I).presheaf.map (homOfLE (le_top (a := U₁))).op ≫
        (structureSheaf I).presheaf.map (eqToHom (congrArg op h)) =
      (structureSheaf I).presheaf.map (homOfLE (le_top (a := U₂))).op := by
    rw [← Functor.map_comp]
    exact congrArg (fun m => (structureSheaf I).presheaf.map m) hmorph
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcat) ((globalSectionsEquiv I).symm r)

/-- **An equality of opens transports the ideal of definition.** The `Ideal.map` form of
`FormalSpectrum.comp_eqToHom_sectionsOpenHom`. -/
theorem map_eqToHom_sectionsOpenIdeal {U₁ U₂ : Opens (FormalSpectrum I)} (h : U₁ = U₂) :
    (sectionsOpenIdeal I U₁).map
        (((structureSheaf I).presheaf.map (eqToHom (congrArg op h))).hom) =
      sectionsOpenIdeal I U₂ := by
  rw [sectionsOpenIdeal, Ideal.map_map, comp_eqToHom_sectionsOpenHom I h, sectionsOpenIdeal]

/-- **The transport carries the `m`-th power of the ideal of definition to the `m`-th power**, in
the membership form a leg that composes a `.c.app` with an `eqToHom` presheaf transport needs. -/
theorem mem_pow_map_eqToHom_sectionsOpenIdeal {U₁ U₂ : Opens (FormalSpectrum I)} (h : U₁ = U₂)
    (m : ℕ) {x : ((structureSheaf I).presheaf.obj (op U₁) : Type u)}
    (hx : x ∈ (sectionsOpenIdeal I U₁) ^ m) :
    (((structureSheaf I).presheaf.map (eqToHom (congrArg op h))).hom) x ∈
      (sectionsOpenIdeal I U₂) ^ m := by
  have hpow : ((sectionsOpenIdeal I U₁) ^ m).map
      (((structureSheaf I).presheaf.map (eqToHom (congrArg op h))).hom) =
      (sectionsOpenIdeal I U₂) ^ m := by
    rw [Ideal.map_pow, map_eqToHom_sectionsOpenIdeal I h]
  exact hpow ▸ Ideal.mem_map_of_mem _ hx

/-!
### The naturality square, and adicity of a sheaf component
-/

/-- **The sheaf component of a morphism of formal spectra commutes with the structural maps.**
For `w : Spf S ⟶ Spf R` and any open `U` of `Spf R`,

`w.c.app (op U) ∘ sectionsOpenHom I U = sectionsOpenHom J ((Opens.map w.base).obj U) ∘ φ`

with `φ = FormalSpectrum.globalSectionsMap I J w`. This is naturality of `w.c` along the inclusion
`U ⊆ ⊤`, together with the definition of `globalSectionsMap` at `⊤`; the two restriction morphisms
that appear are equal because `Opens` is thin.

The basic-open analogue, conjugated by `FormalSpectrum.sectionsBasicOpenEquiv` on both sides, is
`FormalSpectrum.arbSheafComponent_comp_awayCompletionHom`. -/
theorem comp_sectionsOpenHom (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (U : Opens (FormalSpectrum I)) :
    ((w.c.app (op U)).hom).comp (sectionsOpenHom I U) =
      (sectionsOpenHom J ((Opens.map w.base).obj U)).comp (globalSectionsMap I J w) := by
  refine RingHom.ext fun r => ?_
  have hnat (y : (structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))) :
      (w.c.app (op U)).hom
          (((structureSheaf I).presheaf.map (homOfLE (le_top (a := U))).op).hom y) =
        ((structureSheaf J).presheaf.map
            ((Opens.map w.base).map (homOfLE (le_top (a := U)))).op).hom
          ((w.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom y) :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (w.c.naturality (homOfLE (le_top (a := U))).op)) y
  have hmorph : ((Opens.map w.base).map (homOfLE (le_top (a := U)))).op =
      (homOfLE (le_top (a := (Opens.map w.base).obj U))).op := Subsingleton.elim _ _
  have hgs : (w.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom ((globalSectionsEquiv I).symm r) =
      (globalSectionsEquiv J).symm (globalSectionsMap I J w r) := by
    rw [globalSectionsMap_apply, RingEquiv.symm_apply_apply]
  change (w.c.app (op U)).hom
      (((structureSheaf I).presheaf.map (homOfLE (le_top (a := U))).op).hom
        ((globalSectionsEquiv I).symm r)) = _
  rw [hnat, hmorph, hgs]
  rfl

/-- **A sheaf component is adically continuous over an arbitrary open, once its global-sections
map is.** `Ideal.map_pow_map_le_pow_map_of_comp` at the naturality square
`FormalSpectrum.comp_sectionsOpenHom`.

The hypothesis is carried, not derived: its unhypothesised form is false already at `U = ⊤`
(`FormalSchemes.AdicOnSections`, issue 460). For `w = FormalSpectrum.basicOpenChart I f` the
hypothesis is the theorem `FormalSpectrum.basicOpenChart_le_comap_globalSectionsMap`. -/
theorem map_sectionsOpenIdeal_pow_le (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (hadic : I ≤ J.comap (globalSectionsMap I J w)) (U : Opens (FormalSpectrum I)) (m : ℕ) :
    ((sectionsOpenIdeal I U) ^ m).map ((w.c.app (op U)).hom) ≤
      (sectionsOpenIdeal J ((Opens.map w.base).obj U)) ^ m :=
  Ideal.map_pow_map_le_pow_map_of_comp (comp_sectionsOpenHom I J w U)
    (Ideal.map_le_iff_le_comap.mpr hadic) m

/-- **The membership form of `FormalSpectrum.map_sectionsOpenIdeal_pow_le`**, which is the shape
a continuity obligation on this tree is stated in (`RingHom.mem_eqLocus_of_forall_sub_mem_pow`,
`Subring.IsAdicallyClosed`). -/
theorem sectionsComponent_mem_pow (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (hadic : I ≤ J.comap (globalSectionsMap I J w)) (U : Opens (FormalSpectrum I)) (m : ℕ)
    {v : ((structureSheaf I).presheaf.obj (op U) : Type u)}
    (hv : v ∈ (sectionsOpenIdeal I U) ^ m) :
    (w.c.app (op U)).hom v ∈ (sectionsOpenIdeal J ((Opens.map w.base).obj U)) ^ m :=
  map_sectionsOpenIdeal_pow_le I J w hadic U m (Ideal.mem_map_of_mem _ hv)

end FormalSpectrum

end
