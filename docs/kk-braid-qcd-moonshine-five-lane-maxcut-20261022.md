# Five-lane roadmap max-cut — October 22, 2026

## Evidence accepted this round
**A — KK curvature:** new `scripts/check_kk_coupled_radion_magnetic_5d.py` calculates the full 5D Christoffel and Ricci tensors for the exact fixture `g4=diag(-1,1,1,1)`, `A_y=bx`, `phi=phi(x)`, `kappa=1`. Independent execution of equivalent code returned `R5=-(b² phi³+4phi'')/(2phi)` and `det(G5)=-phi²`; compared to analytic `-phi² F²/4 -2phi''/phi` with F²=2b², residual exactly zero. Previous pure magnetic constant-radius and pure varying-radius are subsumed as limits. **Not** full general curved-base tensor proof, not a 5D vacuum solution.

**B — C3/braid/O2 framing:** `scripts/check_c3_braid_o2_gluing_obstructions.py` verifies actual 12-sample selected trajectory: six-step *horizontal mirror* on balanced 3×3 sheet, four-step cyclic permutation of three strands, and demonstration that terminal S1 phase loses integer winding. This is not a continuous full-framing geometry or proof spatial mirror acts on internal KK circle.

**C — nonabelian gauge:** `scripts/check_su3_commutator_closure.py` constructs eight traceless anti-Hermitian SU3 infinitesimal generators, checks all 64 pairwise Lie commutators close in their span, and verifies the invariant trace pairing. Independently ran an equivalent SymPy eight-generator closure computation: passed. This supplies a real su3 Lie-algebra fixture and exact algebraic donor to the existing W3/M3, colour-lane and Yang–Mills owners; NOT a physical QCD derivation, confinement or beta running. Existing colour-lane unequal-metric obstruction can be avoided only with a justified colour/flavour separation.

**D — Monster/moonshine / QG:** existing `CommonActionQFTGRVariationCompilerExact.agda` demands identical external metric perturbation language and commuting QFT/GR stress variations; `QuantumGravityTheoryBoundary.agda` demands gauge quotient, anomaly-free dynamics, semiclassical limit and empirical predictions. Current `KKBraidMoonshineGaugeSameObjectCutExact.agda` derives gauge-invariant readout from paid curvature equivariance and readout-invariance and specifies genuine physical same-object observation proof fields. Those records have **no automatic Monster→gravity or braid→KK inhabitant**. Generating one requires new model-defining data; adding another modular coefficient match would not help.

**E — physical discrimination:** candidate test quantities: (i) radius/KK-mass (m_n=|n|/R) in units where the fifth-direction mode normalization is canonical, with tests of actual mode couplings; (ii) independently reconstructed braid word and ribbon integer framing with known endpoint clamp/control law; (iii) compactification-dependent colour spectrum and QCD running matched to measured quantities; (iv) Monster modular spectral constraints evaluated on the *same* model, not selectively selected numerical correspondences. These are **candidate predictions**, not locked numerical predictions, until physical parameters, uncertainty and units are specified.

## Priority remaining irreducible mathematical cutset
1. Prove the full curved-base **tensor** KK reduction (not just flat-base scalar fixture); compute separate GR/Maxwell/radion Euler–Lagrange equations and boundary terms; include negative/null field controls.
2. Prove a physically supplied framed-braid continuous path-lift and reconstruction guarantee; preserve separate Z winding, C2 orientation and C3 labelling; weld to pants gluing with exact transition cocycle.
3. Import established SU3/W3 Lie action and explicit nonabelian principal connection; if KK geometrisation is demanded, specify larger internal compact space and reduce its genuine isometries.
4. Supply real common-action/metric-stress identification for Monster sector with gauge, dynamics and independent observable constraints, or reject the physical map.
5. Obtain a full measured, parameter-locked, falsifiable dataset confrontation with alternatives.

## Honest no-go boundaries
**Ordinary five-dimensional S1 KK gives abelian U1**, not colour SU3 by itself.
**Modular/Monster symmetry is not a gravitating energy-momentum tensor** by notation.
**Finite ternary coordinate count is not a continuum scalar degree of freedom.**
**T3=one ternary line, T6=two glued lines, T9=sheet, T18=two glued sheets, T27=cube or typed graph extension**. Twelve here counts *time samples*, not lattice sites.
**A source-written Agda interface is not an inhabited physical theory or a kernel receipt.**

## Runnable commands
```bash
python3 scripts/check_kk_coupled_radion_magnetic_5d.py
python3 scripts/check_c3_braid_o2_gluing_obstructions.py
python3 scripts/check_su3_commutator_closure.py
agda -i . -i /path/to/agda-stdlib DASHI/Unified/KKBraidMoonshineGaugeSameObjectCutExact.agda
```
Only independently replicated Python assertions have been executed; exact PR-head CI and Agda kernel not run.
