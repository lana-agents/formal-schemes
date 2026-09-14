import FormalSchemes.OpenFormalSubscheme

set_option linter.style.header false

/-!
# Nested open formal subschemes

`FormalSchemes.OpenFormalSubscheme` builds `X.restrictOpen hX U` and its functoriality, and
`FormalScheme.restrictOpen_locallyFG` says the construction iterates — an open piece of a
`FormalScheme.LocallyFG` formal scheme is again `FormalScheme.LocallyFG`, so `(X|_U)|_V` is a
formal scheme. **Nothing on the tree said what it is.** A scan over every `FormalSchemes/*.lean`
with its comments stripped by `scripts/closure_audit.py`, walking back over the balanced receiver
of each `.restrictOpen`, finds **zero** occurrences anywhere in the library — statement or
proof — where `FormalScheme.restrictOpen` is applied to a term that itself mentions it. This file
supplies the missing comparison.

## The two directions between `Opens X` and `Opens (X|_U)`

`FormalScheme.nestedOpen` is the preimage `Opens X → Opens (X|_U)` along the inclusion, and
`FormalScheme.openOfNested` is the image `Opens (X|_U) → Opens X` along it. The inclusion is an
open embedding, so the image is open and the two compose to the identity in one direction
(`FormalScheme.nestedOpen_openOfNested`); in the other they do not, since
`FormalScheme.nestedOpen` forgets everything outside `U`, and `FormalScheme.openOfNested_le`
records the only thing that survives — the image always lands inside `U`.

## The comparison, and why it takes an equation rather than producing one

`FormalScheme.restrictOpenNestedIso` identifies `(X|_U)|_V` with `X|_W` whenever `V` is `W` seen
inside `U` and `W ≤ U`. It is `FormalScheme.restrictOpenIso` applied to the composite inclusion
`(X|_U)|_V ⟶ X|_U ⟶ X`, whose range is `W` by `FormalScheme.range_nestedι`; so the load-bearing
half is again the triangle over `X`, here `FormalScheme.restrictOpenNestedIso_hom_comp`.

The equation `hW : nestedOpen X hX U W = V` is an **argument**, with `V` a variable, rather than
something the definition computes. That is deliberate and it is what keeps transports out of
consumers' goals: a caller that has the two spellings of a nested open in hand — and there are
always two, since `(Opens.map (restrictOpenMap …).base).obj (nestedOpen …)` and
`nestedOpen … (g⁻¹W')` are equal by `FormalScheme.map_restrictOpenMap_nestedOpen` and not
syntactically so — passes that equality here and `subst` inside the proof does the work.
Reconciling the two spellings with `FormalScheme.restrictOpenCongr` instead was tried first and is
worse: it puts a transport into every consumer's goal, where the `subst` form leaves none.

## The compatibility with functoriality

`FormalScheme.restrictOpenMap_nested` is the square that says the two constructions commute:
restricting `X|_{g⁻¹W} ⟶ Y|_W` further to a nested open of `Y|_W` agrees, through the two nesting
comparisons, with the restriction of `g` at the smaller open `W'`. It is the one statement a
target-local argument about `FormalScheme.restrictOpenMap` needs and could not state before, and
it is proved by cancelling the mono `Y.restrictOpenι hY W'` and rewriting with
`FormalScheme.restrictOpenMap_comp_ι` — no germ-level or chart-level argument appears.

## The preimage abbreviation, weighed against this chain's standing convention

`FormalSchemes.OpenFormalSubscheme`'s functoriality note says the preimage *"is written
`(Opens.map f.base).obj V` throughout, with no abbreviation: a `def` wrapping it would not unfold
at instances transparency and would put a wall between the two spellings of the same open"*.
`FormalScheme.nestedOpen` is an `abbrev` and therefore reducible, so the mechanism that note
names does not apply to it — a reducible definition unfolds at reducible transparency and so at
instances transparency too, and unification never sees a wall.

**That is not by itself a reason to introduce one, and the alternative was measured rather than
dismissed.** Every statement below was written out with the preimage inlined and built the same
way, as a module in this library rather than a scratch file, so that the style linters ran: it is
**EXIT=0 under `--wfail`**, so the convention is affordable and the case for the abbreviation is
not that inlining fails. What inlining costs is three statement lines over a hundred display
columns — 105, 110 and 115 — needing four continuation lines between two statements, and one term
of **96 characters**, the preimage along the inclusion of `g⁻¹W` which is itself a preimage,
split across a line break inside the statement of
`FormalScheme.map_restrictOpenMap_nestedOpen` — the one statement whose entire content is that two
such terms agree.

So this is a decision about register and not about feasibility, and it is taken this way: the
convention is kept wherever the note is about the preimage along an **arbitrary** morphism, which
is how `FormalScheme.restrictOpenMap` and everything around it is still spelled here, and the
abbreviation is introduced only for the preimage along `FormalScheme.restrictOpenι`. That one is
not an abbreviation of a preimage but the name of this file's subject — an open of `X` seen as an
open of `X|_U` — and a reader who has to re-read a split 96-character term to see that two of them
differ is being charged for the convention rather than served by it.

## Placement

Everything here is about `FormalScheme.restrictOpen` and nothing else, so
`FormalSchemes.OpenFormalSubscheme` is where it belongs on subject matter. It is a new module over
that file instead, and the two homes were costed by walking every `import FormalSchemes.` line
transitively over the modules under `FormalSchemes/` — a module is not counted in its own closure,
and the aggregator at the repository root is outside the walk:

* **In the hub.** `FormalSchemes.OpenFormalSubscheme` has reverse closure **73** and forward
  closure **32**, so every edit to it rebuilds seventy-three modules, and every later edit to
  these ten declarations does so again.
* **As a leaf over it**, which is what this file is:
  `FormalSchemes.NestedOpenFormalSubscheme` has reverse closure **1** and forward closure **33**,
  so adding it costs two build jobs and an edit here rebuilds one module. The one module is
  `FormalSchemes.GeneralSeparatedHomLocal`, its only consumer.

The ratio is seventy-three to one and exactly one module reads these declarations, so the leaf
wins on this tree's standing disposition and the hub is not worth re-costing until a second
consumer appears somewhere that cannot reach this file.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.nestedOpen`: an open of `X` seen as an open of `X|_U`.
* `AlgebraicGeometry.FormalScheme.openOfNested`: an open of `X|_U` seen as an open of `X`, with
  `FormalScheme.openOfNested_le` and `FormalScheme.nestedOpen_openOfNested` for the two round trips.
* `AlgebraicGeometry.FormalScheme.restrictOpenNestedIso`: `(X|_U)|_V ≅ X|_W`, with the triangle
  `FormalScheme.restrictOpenNestedIso_hom_comp` over `X`.
* `AlgebraicGeometry.FormalScheme.map_restrictOpenMap_nestedOpen` and
  `AlgebraicGeometry.FormalScheme.restrictOpenMap_nested`: the compatibility of the nesting with
  `FormalScheme.restrictOpenMap`, on opens and on morphisms.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme

variable (X : FormalScheme.{u}) (hX : X.LocallyFG) (U : Opens X)

/-- **An open of `X`, seen as an open of `X|_U`**: the preimage along the inclusion.

An `abbrev` and not a `def`, which is what makes it compatible with the convention
`FormalSchemes.OpenFormalSubscheme` states for the preimage along an arbitrary morphism: an
`abbrev` is reducible, so it unfolds at reducible transparency and hence at instances transparency,
and the wall that note warns a `def` would raise between the two spellings of one open is not
raised here. -/
abbrev nestedOpen (W : Opens X) : Opens (X.restrictOpen hX U) :=
  (Opens.map (X.restrictOpenι hX U).base).obj W

/-- **An open of `X|_U`, seen as an open of `X`**: the image along the inclusion, which is open
because the inclusion is an open embedding. -/
def openOfNested (V : Opens (X.restrictOpen hX U)) : Opens X :=
  U.isOpenEmbedding.isOpenMap.functor.obj V

/-- **The image lands in `U`.** This is the half of the round trip that survives in the direction
`FormalScheme.nestedOpen` forgets information, and it is what lets a cover of `X|_U` be pushed to
a family of opens of `X` refining `U`. -/
theorem openOfNested_le (V : Opens (X.restrictOpen hX U)) : X.openOfNested hX U V ≤ U := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

/-- **The round trip through `X` is the identity on opens of `X|_U`.** The inclusion is injective,
so the preimage of the image is the original open.

Stated through injectivity and `Set.preimage_image_eq` rather than point-wise: after `ext` the
point-wise route leaves `(ConcreteCategory.hom (TopCat.ofHom ⟨Subtype.val, _⟩)) y = _`, which does
not reduce to `y = x` under `simpa [restrictOpenι_base, Opens.inclusion']` and is not repaired by
adding `ConcreteCategory.hom_ofHom` either. -/
theorem nestedOpen_openOfNested (V : Opens (X.restrictOpen hX U)) :
    X.nestedOpen hX U (X.openOfNested hX U V) = V := by
  have hinj : Function.Injective ⇑(X.restrictOpenι hX U).base := by
    rw [restrictOpenι_base]; intro a b h; exact Subtype.ext h
  have himg : ((X.openOfNested hX U V : Opens X) : Set X)
      = ⇑(X.restrictOpenι hX U).base '' (V : Set (X.restrictOpen hX U)) := by
    rw [restrictOpenι_base]; rfl
  ext x
  change x ∈ ⇑(X.restrictOpenι hX U).base ⁻¹' ((X.openOfNested hX U V : Opens X) : Set X)
    ↔ x ∈ (V : Set (X.restrictOpen hX U))
  rw [himg, Set.preimage_image_eq _ hinj]

/-- **A point of a nested open maps into its image.** The membership half of
`FormalScheme.openOfNested`, which turns a cover of `X|_U` into a cover of `U` by opens of `X`. -/
theorem mem_openOfNested (V : Opens (X.restrictOpen hX U)) (x : X.restrictOpen hX U) (hx : x ∈ V) :
    (X.restrictOpenι hX U).base x ∈ X.openOfNested hX U V :=
  ⟨x, hx, rfl⟩

/-- **The composite inclusion `(X|_U)|_V ⟶ X|_U ⟶ X` has range `W`**, which is the hypothesis
`FormalScheme.restrictOpenIso` asks for and hence the whole content of
`FormalScheme.restrictOpenNestedIso`.

Both ranges are pinned by `FormalScheme.range_restrictOpenι_base`, after which the image of a
preimage meets the range in `Set.image_preimage_eq_inter_range` and the hypothesis `W ≤ U`
removes the intersection. -/
theorem range_nestedι {U : Opens X} (V : Opens (X.restrictOpen hX U)) {W : Opens X}
    (hW : X.nestedOpen hX U W = V) (hWU : W ≤ U) :
    Set.range ((((X.restrictOpen hX U).restrictOpenι (X.restrictOpen_locallyFG hX U) V)
        ≫ X.restrictOpenι hX U).base) = (W : Set X) := by
  subst hW
  have hcomp : ⇑((((X.restrictOpen hX U).restrictOpenι (X.restrictOpen_locallyFG hX U)
        (X.nestedOpen hX U W)) ≫ X.restrictOpenι hX U).base)
      = ⇑(X.restrictOpenι hX U).base ∘
        ⇑((X.restrictOpen hX U).restrictOpenι (X.restrictOpen_locallyFG hX U)
          (X.nestedOpen hX U W)).base := rfl
  rw [hcomp, Set.range_comp, range_restrictOpenι_base, Opens.map_coe,
    Set.image_preimage_eq_inter_range, range_restrictOpenι_base]
  exact Set.inter_eq_self_of_subset_left hWU

/-- **A nested open subscheme is an open subscheme**: `(X|_U)|_V ≅ X|_W` whenever `V` is `W` seen
inside `U` and `W ≤ U`.

The equality `hW` is an argument and `V` is a variable, so a caller holding either of the two
spellings of a nested open passes the equation between them and no transport survives into its
goal; see the module docstring for why the `FormalScheme.restrictOpenCongr` route is worse. -/
def restrictOpenNestedIso {U : Opens X} (V : Opens (X.restrictOpen hX U)) {W : Opens X}
    (hW : X.nestedOpen hX U W = V) (hWU : W ≤ U) :
    ((X.restrictOpen hX U).restrictOpen (X.restrictOpen_locallyFG hX U) V).toLocallyRingedSpace
      ≅ (X.restrictOpen hX W).toLocallyRingedSpace :=
  X.restrictOpenIso hX W (((X.restrictOpen hX U).restrictOpenι
    (X.restrictOpen_locallyFG hX U) V) ≫ X.restrictOpenι hX U) (X.range_nestedι hX V hW hWU)

/-- **The triangle over `X`**, which is the load-bearing half exactly as it is for
`FormalScheme.restrictOpenIso`: the comparison followed by the inclusion of `W` is the composite
inclusion it was built from. -/
@[reassoc (attr := simp)]
theorem restrictOpenNestedIso_hom_comp {U : Opens X} (V : Opens (X.restrictOpen hX U))
    {W : Opens X} (hW : X.nestedOpen hX U W = V) (hWU : W ≤ U) :
    (X.restrictOpenNestedIso hX V hW hWU).hom ≫ X.restrictOpenι hX W
      = ((X.restrictOpen hX U).restrictOpenι (X.restrictOpen_locallyFG hX U) V)
        ≫ X.restrictOpenι hX U :=
  X.restrictOpenIso_hom_comp hX W _ (X.range_nestedι hX V hW hWU)

section Map

variable (Y : FormalScheme.{u}) (hY : Y.LocallyFG)
variable (g : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace) (W W' : Opens Y)

/-- **The nesting commutes with the preimage, on opens.** Pulling a nested open of `Y|_W` back
along `FormalScheme.restrictOpenMap` gives the nested open of `X|_{g⁻¹W}` cut out by `g⁻¹W'`.

The two sides are equal and not syntactically so, which is the reason
`FormalScheme.restrictOpenNestedIso` takes its equation as an argument. The proof is
`FormalScheme.base_restrictOpenMap_comp_ι` at a point, reached by a `show` down to the `Set`
spelling: after `ext x` a goal about `(Opens.map _).obj _` does not admit
`rw [Opens.mem_mk, Set.mem_preimage]`, which reports *"Did not find an occurrence of the pattern
`?m ∈ { carrier := ?m, is_open' := ?m }`"*. -/
theorem map_restrictOpenMap_nestedOpen :
    (Opens.map (X.restrictOpenMap hX Y hY g W).base).obj (Y.nestedOpen hY W W')
      = X.nestedOpen hX ((Opens.map g.base).obj W) ((Opens.map g.base).obj W') := by
  ext x
  change (Y.restrictOpenι hY W).base ((X.restrictOpenMap hX Y hY g W).base x) ∈ W'
    ↔ g.base ((X.restrictOpenι hX ((Opens.map g.base).obj W)).base x) ∈ W'
  rw [X.base_restrictOpenMap_comp_ι hX Y hY g W x]

/-- **The nesting commutes with the induced morphism.** Restricting `X|_{g⁻¹W} ⟶ Y|_W` further to
the nested open cut out by `W' ≤ W` is, through the two comparisons of
`FormalScheme.restrictOpenNestedIso`, the morphism `X|_{g⁻¹W'} ⟶ Y|_{W'}` induced by `g` at `W'`.

This is the compatibility a target-local argument about `FormalScheme.restrictOpenMap` needs. Both
sides are monomorphisms after composing with the inclusion of `W'`, so the proof is
`cancel_mono` followed by three applications of `FormalScheme.restrictOpenMap_comp_ι` and the two
triangles. -/
theorem restrictOpenMap_nested (hW' : W' ≤ W) :
    (X.restrictOpen hX ((Opens.map g.base).obj W)).restrictOpenMap
        (X.restrictOpen_locallyFG hX _) (Y.restrictOpen hY W) (Y.restrictOpen_locallyFG hY W)
        (X.restrictOpenMap hX Y hY g W) (Y.nestedOpen hY W W')
      ≫ (Y.restrictOpenNestedIso hY (Y.nestedOpen hY W W') rfl hW').hom
      = (X.restrictOpenNestedIso hX
            ((Opens.map (X.restrictOpenMap hX Y hY g W).base).obj (Y.nestedOpen hY W W'))
          (X.map_restrictOpenMap_nestedOpen hX Y hY g W W').symm
          (fun _ hx => hW' hx)).hom
        ≫ X.restrictOpenMap hX Y hY g W' := by
  rw [← cancel_mono (Y.restrictOpenι hY W')]
  rw [Category.assoc, restrictOpenNestedIso_hom_comp, Category.assoc,
    restrictOpenMap_comp_ι, ← Category.assoc, restrictOpenMap_comp_ι, Category.assoc,
    restrictOpenMap_comp_ι, restrictOpenNestedIso_hom_comp_assoc]

end Map

end AlgebraicGeometry.FormalScheme
