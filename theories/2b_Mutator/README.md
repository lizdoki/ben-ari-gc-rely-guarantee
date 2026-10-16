# 2b_Mutator: Part 2 for the Mutator (§4.6)

`GC_Mutator.thy`: the Mutator's code (Algorithm 12, with Redirect, Malloc and Zap of §4.6)
meets its specification (`../1_Specifications/GC_Mutator_Spec.thy`). It is proved with the
VDM rules of `RG_VDM`, for each operation (`Redirect_sat`, `Malloc_sat`, `Zap_sat`) and
then for the whole Mutator (`Mutator_sat`).
