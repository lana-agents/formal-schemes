# Pending: bothAlgDataT'_fac 12 mixed leaves

Template proven for snd_snd/fst_fst/both_both_both (same-shape). 12 mixed leaves left.
Working file: FormalSchemes/GeneralFibreProductBothAlgebraDataTPrimeFac.lean

## Leaf order (idxTrans first): snd_fst, fst_snd, snd_both_fst, snd_both_both,
## fst_both_snd, fst_both_both, both_snd_*, both_fst_*, both_both_snd, both_both_fst

## Closer types per leaf (A factor / B factor), genuine vs structural:
1 snd_fst:      A idxTransA(structural) / B genuine τY+selfMul
2 snd_both_fst: A idxTransA / B genuine τY+selfMul(collapse)
3 snd_both_both:A idxTransA / B genuine σY+mulcomm
4 fst_snd:      A genuine τX+selfMul / B idxTransB
5 fst_both_snd: A genuine τX+selfMul(collapse) / B idxTransB
6 fst_both_both:A genuine σX+mulcomm / B idxTransB
7 both_snd_fst: A τX+selfMul / B τY+selfMul(collapse)
8 both_snd_both:A τX+selfMul / B σY+mulcomm
9 both_fst_snd: A τX+selfMul(collapse) / B τY+selfMul
10 both_fst_both:A σX+mulcomm / B τY+selfMul
11 both_both_snd:A τX+selfMul(collapse) / B genuine σY
12 both_both_fst:A genuine σX / B τY+selfMul(collapse)

Helpers to build: idxTrans-vs-IsScalarTower compat; selfMul expand/collapse compat; mulcomm transport.

## STATUS 2026-08-08
- snd_fst template written & verified up to the final two-mapSpf merge (compiles; temp `sorry` at closer).
- Delegated full completion (infra helpers + all 12 leaves) to lean-proof-agent (has LSP). It owns the
  file; do NOT edit concurrently.
- Verified facts for the agent: only snd_fst/fst_snd (src leg) and snd_both_fst/fst_both_snd (tgt leg)
  need `interchangeOpenImmersion_eq_mapSpf`/`rightInterchangeOpenImmersion_eq_mapSpf`; all other leg
  laws give mapSpf directly. Closer kinds: (a) idxTrans-vs-IsScalarTower [subst], (b) furtherLoc↔selfMul
  collapse [localization ringHom_ext + mapCompletion congr, or continuous ext], (c) genuine = hστX/hστY
  (± mul_comm awayCongrElt transport).
