# Done: 5 mixed cocycle leaves (task 378)

All in FormalSchemes/GeneralFibreProductBothAlgebraDataCocycle.lean, green, axioms = [propext, Classical.choice, Quot.sound].

Leaves: bothAlgDataT'_cocycle_{fst_snd, snd_both_fst, fst_both_snd, both_snd_fst, both_fst_snd}.

New generic per-factor closers added:
- cocycle_fst_snd_hfA : A-factor, order [Fwd,Bwd,I] (idxTrans last), single element.
- cocycle_fst_snd_hfB : B-factor, order [I,Fwd,Bwd] (idxTrans first), single element (B-mirror of cocycle_snd_fst_hfA).
- cocycle_snd_both_fst_hfB : B-factor, order [Bwd,I,Fwd] (idxTrans middle), product domain gY j j' * gY j j''.
- cocycle_both_snd_fst_hfB : as above but reversed product gY j j'' * gY j j' (both_snd source iso).
- cocycle_fst_both_snd_hfA : A-mirror of cocycle_snd_both_fst_hfB, product gX i i' * gX i i''.
- cocycle_both_fst_snd_hfA : A-mirror of cocycle_both_snd_fst_hfB, reversed product gX i i'' * gX i i'.
