# 0_Framework: rely/guarantee in general (§2.2, Appendix B.1)

Nothing here is about garbage collection.

1. `RG_Semantics.thy`: rely/guarantee quadruples, given a meaning over computations with
   program and environment steps, and the parallel rule, proved sound (`rg_parallel`).
2. `RG_VDM.thy`: a small language of programs (the language of Appendix C), VDM-style
   quadruples over it, and the rules the thesis uses (Appendix B.1), each proved sound.
   `vdm_rg_sat` turns a VDM quadruple about a program into a quadruple of `RG_Semantics`
   about the program run as a process.
