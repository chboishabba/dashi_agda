# NV quantum computation × diamond MCG × crystal symmetry × TSFV: cross-PR integration (2026-10-26)

## Critical prior-art correction

**Diamond MCG is the existing implementation owner, Agda PR #1238** (branch `chatgpt/diamond-mcg-causal-bioem-20261022`). It already includes many of the physical refinements previously proposed as "next work" in NV quantum-computing PR #1262:

| Source-owner file on #1238 | Reusable object | Status / limitation |
| --- | --- | --- |
| `NVSpinOneAxialExact.agda` | `AxialNV`, qutrit-basis rational axial energies `D ± γB, 0`, matrix transpose symmetry, signed splitting | Finite algebra, not calibrated ODMR |
| `NVCrystalOrientationExact.agda` | Four finite unoriented diamond <111> NV axes and rational magnetic-field projection | Not full tetrahedral defect group or orientation tomography |
| `NVODMRDetuningSymmetryExact.agda` and `NVFiniteResonanceReadoutExact.agda` | Resonance/readout refinement | Must retain physical calibration gates |
| `NVFiveLevelOpticalMasterExact.agda`, `NVOpticalRateSteadyStateExact.agda` | Optical preparation / effective master-rate candidates | Not automatic CPTP or experimentally established rates |
| `NVComplexC3NSBornExact.agda` | Exact three-complex-amplitude interference decomposition and *optical triple* C3 invariance | C3 permutes amplitude *slots*, not spin eigenlevels |
| `NVShorTSFVCoherentObservationExact.agda`, `NVTSFVFinitePathInterferenceExact.agda` | Two-path amplitude sum before Born squaring, coherent/incoherent distinction | Not physical TSFV S/hbar calibration |
| `NVPhotonBinaryLikelihoodExact.agda` | Source-to-detection likelihood seam | Physical photon calibration remains separate |
| `NVYM369C3OpticalFourierExact.agda` | Candidate 369/YM/finite-Fourier bridge | Distinct physical carriers remain separately typed |

**Important group-theoretic counterpoint.** In PR #1262's *spin-level* carrier, the candidate three-cycle fails to commute with `Sz² = diag(1,0,1)`; the plus/minus exchange is an order-two symmetry. In the MCG donor's *optical-amplitude triple*, rotating the slots preserves `|a+b+c|²` by commutativity of addition. These are not contradictory results: the maps act on different carriers with different invariants. A sound weld must explicitly supply an intertwiner, not rename a C3 action or infer physical equivalence. The four diamond <111> orientation axes likewise are not an automatic spin-level C3 orbit.

## Crystallography donor boundary

Agda #1261 (`feat/tetragonal-d4h-exact-20261025`) has exact D4h 4/mmm integer symmetry, point-group catalogs, 7-system/14-Bravais classifications and lattice/hyperfabric contracts. It is relevant as a **generic classification and equivariance method**, not as the **physical diamond** point group. Diamond bulk is cubic with crystallographic group `Fd-3m` (space group 227), point group `O_h`; the NV defect reduces site symmetry to `C3v` along a <111> axis (subject to charge/strain/environment). Do not apply D4h transformations directly to an NV defect without a justified embedding/restriction. For defects, `C3v` (order 6) and the pure cyclic `C3` subgroup are distinct; a spatial 120-degree rotation about the NV axis is not the arbitrary 3-cycle among electronic spin levels.

A valid refinement sequence:
1. crystallographic group and four <111> oriented-axis labels;
2. site stabilizer / chosen-axis symmetry (`C3v` under ideal conditions);
3. spin-one representation and actual transformation of Hamiltonian coefficients;
4. subspace encoding and controlled gates;
5. optical amplitudes and detector records;
6. same-device experiment and measurement-fidelity witnesses.

## TSFV donor boundary

Agda #621 supplies `TSFVActionPhaseWeightSeparationExact`, `TSFVNonseparableTransitionKernelExact`, and history-conditioned / bidirectional admissibility constructions. Agda #1238 already specializes some to NV optical observations. The useful exact distinction is:
- **coherent**: `|A_1+A_2|²` includes interference;
- **distinguishable/decohered**: `|A_1|²+|A_2|²` loses the cross term;
- **TSFV action claim**: requires independent provenance and actual phase `S/ℏ`, not merely an abstract coefficient algebra.
Thus quantum-computation gate-depth/coherence analysis may reuse the observation machinery, but neither the TSFV history semantics nor MCG measurement data proves quantum advantage.

## SUSY compatibility and obstruction

PR #1262 also proves an ideal `H = Sz² = {Q,Q†}` finite SUSY-QM factorisation with `Q = |-1><+1|` and an unpaired zero mode. This depends on degeneracy `E(+1)=E(-1)`. PR #1238's axial model has `E(±1)=D±γB`; the two levels are *not* degenerate for generic nonzero `γB`. The previously constructed `Q` therefore cannot preserve that physical axial Hamiltonian in general. A calibrated drive could lead to a separately proved *effective* SUSY Hamiltonian, but this requires an actual rotating-frame/Floquet construction and measurement.

## Data and source roots

The MCG donor attributes human cardiac results to Muhib Omar et al., *Human cardiac measurements with diamond magnetometers*, *Science Advances* 12(38), eaeg5281 (2026-09-16), DOI 10.1126/sciadv.aeg5281, and carefully distinguishes the three independent platforms and their reported system sensitivities. Its calibration document is `Docs/physics/DiamondComplexC3MCGMeasuredCalibrationMaxCut20261024.md`. Never use MCG measured magnetic-field sensitivity as a quantum gate fidelity or as a processor benchmark.

# Repository dependency and integration plan

**Do not import unmerged #1238/#1261 modules directly into #1262, which currently targets `master`: that would break the branch unless it is restacked, merged, or its dependencies are explicitly vendored (undesirable).** Current PR #1262 remains a small standalone theorem slice; its next actual integration should be stacked on #1238's head, or wait for that PR to merge. Preserve original authorship, historical SHA and proof statuses in the resulting cross-repo receipts.

In addition to those Agda donors, Lean quantum mereology #76 is the proper partial-trace/g-TPS owner; Lean quantum channels #85 offers channel methods but not the same physical Hilbert space; dashiQ #2/#3 is the experiment promotion runtime. Same-object alignment is mandatory prior to any cross-prover or device benchmark claim.

## Payable next exact leaves
- Import `NVSpinOneAxialExact` and `NVSpinOneFiniteSUSYFactorisationExact` into a common *stacked* branch; prove the B=0 specialization and the nonzero-splitting obstruction via exact rational data.
- Define explicit spatial C3v and its C3 subgroup using real defect-axis stabilizers; distinguish it from C3 on spin basis labels and optical path slots.
- Prove fidelity/measurement bounds *conditionally* from typed noise and photon-channel estimates and keep them separate from measured sensitivity.
- Require per-platform MCG provenance and actual processor measurement records for any cross-device comparison.
- Keep source-written receipts distinct from compiler/kernel receipts, and analogies distinct from physical equivalences.
