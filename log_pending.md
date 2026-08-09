# Pending: 5 mixed cocycle leaves in GeneralFibreProductBothAlgebraDataCocycle.lean

Template: bothAlgDataT'_cocycle_snd_fst (already proven, lines ~180-218).

## Shape analysis (edges e01=shape(p,p'), e02=shape(p,p''), e12=shape(p',p''))
shape: snd if X-coords equal, fst if Y-coords equal, else both.
Term (a,b,c) reduction lemma = <shape(a,b)>_<shape(a,c)>[ _<shape(b,c)> if either leg both].
A-map/B-map types: I=idxTrans, Fwd=τ.trans(selfMul.trans congr), Bwd=congr.trans(selfMul.symm.trans τ).
Rotations of [I,Fwd,Bwd]: R0=[I,Fwd,Bwd], R1=[Fwd,Bwd,I], R2=[Bwd,I,Fwd].
Existing closers: cocycle_snd_fst_hfA = A/R0 ; cocycle_snd_fst_hfB = B/R1.

Leaf1 fst_snd (h1'≠,h2'=,h1''=): e01=fst,e02=snd,e12=both. terms fst_snd/both_fst_snd/snd_both_fst. A=R1,B=R0. NEED A/R1,B/R0
Leaf2 snd_both_fst (h1'=,h1''≠,h2''≠,h2t=): e01=snd,e02=both,e12=fst. terms snd_both_fst/fst_snd/both_fst_snd. A=R0,B=R2. NEED B/R2
Leaf3 fst_both_snd (h1'≠,h2'=,h1''≠,h2''≠,h1t=): e01=fst,e02=both,e12=snd. terms fst_both_snd/snd_fst/both_snd_fst. A=R2,B=R0. NEED A/R2
Leaf4 both_snd_fst (h1'≠,h2'≠,h1''=,h2t=): e01=both,e02=snd,e12=fst. terms both_snd_fst/fst_both_snd/snd_fst. A=R1,B=R2. (reuse)
Leaf5 both_fst_snd (h1'≠,h2'≠,h1''≠,h2''=,h1t=): e01=both,e02=fst,e12=snd. terms both_fst_snd/snd_both_fst/fst_snd. A=R2,B=R1. (reuse B/R1 exists)

New closers to add: cocycle A/R1, A/R2, B/R0, B/R2.

## Status
- [ ] Leaf1, Leaf2, Leaf3, Leaf4, Leaf5
