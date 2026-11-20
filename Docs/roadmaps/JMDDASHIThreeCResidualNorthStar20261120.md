# JMD–DASHI 3B/3C residual and North Star roadmap (2026-11-20)

## Attribution
JMD: supplied 3C centralizer diagram and NorthStarCompletionAudit / H1–H5 diagram.
DASHI: supplied five-orbit origami diagram, residual 54; existing Heisenberg and cyclotomic owners.
Joint synthesis: comparison, S3 candidate, Laplacian transfer. Diagrams are source records, not proof certificates.
Published inputs: ATLAS of Finite Groups, Th and Fi23 page (https://gaetan.chenevier.perso.math.cnrs.fr/ALG1/ATLAS.pdf); Monster character table north-west corner, https://doi.org/10.1017/9781009401586 (chapter Monstrous Moonshine: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/E48A79B810EB9DE3D68ED68C97CEE07B/9781009401586c7_402-434.pdf/monstrous_moonshine.pdf).
3B and 3C reduced traces 53 and -1; conformal extension 54 and 0. Normalizer S3 x Th is sourced, not constructed.

## Exact finite model
Q=F3^2/{±1}: one singleton and four pairs. D=Q x C2. Core D x F3^8 x C3, translation on last coordinate. Residual ordered distinct ternary pairs x F3^2, 54 states. B fixes residual; C translates last coordinate. Both have 196884 states, traces (196884,54,54) and (196884,0,0). Multiplicity difference (36,-18,-18)=18 L e0, L=3I-J, L²=3L. Sixfold factor is naturally S3 but a residual submodule inside the original Monster is not established.

Local prior verifier rerun in Python/SymPy 1.14: PASS, explicit enumeration of both carriers. Agda and GAP not installed; new Agda source is UNVERIFIED.

## Gates
W01 attribution recorded; W02–W08 finite model derivation and local enumeration PASS; W09 published character input recovered, independent GAP certificate OPEN; W10 actual Th action OPEN; W11 cube-root/twisted VOA OPEN; W12 original Griess product OPEN; W13 sixfold model PASS; W14 Laplacian PASS; W15 source normalizer recovered, canonical residual embedding OPEN.
W16 reflection discriminator: S3 irreducible multiplicities on weight two are (32814+t/2,32814-t/2,65628) for reflection trace t. Actual fusion and restricted character OPEN.
JMD H1 common rational coordinate map OPEN; H2 original product preservation OPEN; H3 form preservation OPEN; H4 visible generator transport OPEN; H5 triality transport OPEN. These must all use the same map. JMD NorthStarCompletionAudit gate explicitly NOT PASSED; exact upstream Lean source not located by connector search. No promotion from finite character tests to H1–H5.

## Continuation: source-owned 2A reflection and maximal S3 regular core
Breuer, Magaard, Wilson, arXiv:2412.12182v1, Fact 1, constructs 3C from a product of two 2A involutions and identifies Th as stabilizer. This fixes the selected S3 reflection as 2A. Weight-two trace vector (196884,4372,0) gives multiplicities (35000,30628,65628). Maximal regular multiplicity is 30628, bounded by the sign constituent. Remainder (4372,0,4372) is 4372 natural ternary permutation representations. This is an abstract S3 representation isomorphism, not an actual selected basis or Th-equivariant splitting.
Local SymPy 1.14 PASS: exact inverse, reconstruction, maximality negative control, regular and ternary character rows. Prior downloaded finite verifier rerun PASS; identified and corrected repository orbit assertion [1,2,2,2] to [1,2,2,2,2]. 
W16 reflection source selection closed; arithmetic locally tested. W17 OPEN: CTblLib catalog https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/S3xTh.html confirms 144 classes and stored fusion into M. Literal table rows not retrieved; local network DNS fails and GAP unavailable. Added local GAP acceptance program (UNEXECUTED) that requires full stored fusion, reconstructs all 144 classes, prints constituents, and checks selected reflection and rotation. W17 will close only on actual execution and constituent identification, not merely this runner.
For each h in Th write x=character(1,h), y=character(s,h), z=character(r,h). The three multiplicity-space characters are x/6+y/2+z/3, x/6-y/2+z/3, (x-z)/3 respectively. Need their actual classwise values and irreducible decomposition. H1–H5 remain OPEN; Agda kernel acceptance remains OPEN. No attribution change.
