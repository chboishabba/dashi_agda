# Monster / V-natural / KK / AdS3 / Yang–Mills / FRACTRAN physical-information maximum cut

**Date:** 2026-11-14  
**Controlling owner:** [DASHI Agda PR #1472](https://github.com/chboishabba/dashi_agda/pull/1472), branch `agent/y443-monster-vnatural-maxcut-20261106`.  
**Scope:** source-preserving same-object theorem integration and falsifiable physical tests. **Not** a claim that the Clay problem, AdS3 pure-gravity duality, 5D/26+1D physical solutions or information–mass equivalence are solved.

## 0. Acceptance contract and provenance

Status vocabulary (never collapse):
- **PROVED+KERNEL:** proof accepted by pinned Agda 2.9 on the *exact changed head* with dependency closure; cite exact command and receipt.
- **SOURCE-WRITTEN:** a concrete proof candidate committed, but no matching kernel receipt.
- **CONDITIONAL:** theorem proven only under an explicitly passed record of witnesses.
- **FINITE-TEST:** independent exhaustive or exact-rational execution, not a physical theorem.
- **OPEN:** not constructed or no source-backed witness for the named target.
- **EMPIRICAL-OPEN:** physical implementation/measurement absent.

Source-of-truth heads read 2026-11-14:
| PR | Exact inspected head | Role |
| --- | --- | --- |
| [#1472](https://github.com/chboishabba/dashi_agda/pull/1472) | `00eadae44260` **before this roadmap's new commits** | Y443, original `Vnatural`, FLM/Griess, gravity comparison |
| [#1162](https://github.com/chboishabba/dashi_agda/pull/1162) | `428e16375796` | Monster C3 physical ensemble / entropy / gravity |
| [#1179](https://github.com/chboishabba/dashi_agda/pull/1179) | `cbbab3579ae6` | Albert/F4, actor-scoped state → stress → cosmology |
| [#1489](https://github.com/chboishabba/dashi_agda/pull/1489) | `bf2eef076b2a` | finite C3-equivariant same-H heat/zeta/trace |
| [#1474](https://github.com/chboishabba/dashi_agda/pull/1474) | `fcadcb35b2d6` | Conway/FRACTRAN/N21 original machine |
| [#1460](https://github.com/chboishabba/dashi_agda/pull/1460) | `ed4cd2edf5f9` | Lorentz 3+1/TSVF/KK source bridge |
| [#1493](https://github.com/chboishabba/dashi_agda/pull/1493) | `11e8ae6a24d4` | TSVF/OS physical generator/resolvent |
| [#1444](https://github.com/chboishabba/dashi_agda/pull/1444) | `7a559643506c` | YM original E1/D1/D2 mass-gap lane |
| [#1498](https://github.com/chboishabba/dashi_agda/pull/1498) | `2c4204914d93` | Wilson/ghost/Haar original B4 P0 scalar |
| [#1499](https://github.com/chboishabba/dashi_agda/pull/1499) | `0ec0d5e67221` | all-lane integration / negative controls |

**Rule:** these branches are not one kernel-checked source tree. Imports from other heads must be pinned, copied with full transitive closure into an isolated working branch, and Agda-checked before “same-source theorem” promotion.

## 1. Existing owners that MUST be reused

- `DASHI/Moonshine/VNaturalOrbifoldConstruction.agda`: actual fixed/twisted input, *paired linear* carrier; the old disjoint tagged carrier is not a direct sum.
- `DASHI/Moonshine/VNaturalOriginalPairedFourSectorModesExact.agda`: original FF/FT architecture, TF/TT and mixed physical laws still needed.
- `DASHI/Moonshine/Y443FLMDirectSameObjectCapstoneExact.agda`: `originalAndPublishedActionsAgreeEverywhere` already transports agreement on JMD u/v to all group elements **conditional on** `PublishedFLMAndJMDSource`.
- `DASHI/Moonshine/Y443FLMGriessFullAutSelectedVOAExact.agda`: `ConcreteGriessProduct`, `WeightTwoGeneration`, `SelectedFLMExtension`, `SelectedMonsterGriessIdentification`.
- `DASHI/Moonshine/MoonshineOrbifoldWeightTwoDecompositionExact.agda`: sourced `300 + 98280 + 98304 = 196884`; conformal line and 196883 constituent.
- `DASHI/Moonshine/MonsterSpecialGravityKKWeightTwoCrosswalkExact.agda`: proposed gravity-sector counts and typed coordinate labels, *no* asserted physical isomorphism.
- `DASHI/Physics/Closure/MonsterExceptionalEntropyGravityCompilerExact.agda` (#1179): `Native369PhysicalEnsemblePayment`, `MonsterExceptionalStateIntertwiner`, `ProofRelevantEntropyGravityPayment`, `MonsterExceptionalStressHandoff`, `MonsterExceptionalCosmologyRecognition`.
- `DASHI/Physics/Closure/InformationParadoxCrossGateObstruction.agda`: semiclassical/OS/DHR/entropy/black-hole gates.
- `DASHI/Combinatorics/FractranComputationEquivalence.agda`, PR #1474 and FRACDASH: first-enabled and original-machine semantics.
- `DASHI/Physics/YangMills/` and the original `BalabanClay...` owners: actual physical Wilson/Haar/ghost and continuum constraints.

**Negative controls:** arbitrary equality of dimensions/characters does not imply same operator; a set-level coproduct is not a vector-space direct sum; a selected scalar entropy does not determine a conserved tensor; abstract prime-exponent registers are not physical p-level qudits; no finite-grid estimate substitutes for interacting continuum limits.

## 2. Phased roadmap, exact theorem obligations and deliverables

### Phase P0 — Typed gravity–FLM coordinates and first falsification tests

**New source-written output:** `DASHI/Moonshine/MonsterSpecialGravityKKRefinedCoordinateBidiExact.agda`, added 2026-11-14. It defines:
- `RefinedFLMWeightTwoCoordinate` with the FLM `Fin300 ⊎ Fin98280 ⊎ Fin98304` nesting;
- `gravityToRefinedFLM`, `refinedFLMToGravity`;
- `gravityToFLMToGravity`, `flmToGravityToFLM` (two inverse equations);
- `gravityDilatonMapsToFLMScalar`, `gravityMetricMapsToFLMSymmetricSquare`, `gravityPFormMapsToFLMNormFourPair`, `gravityTwistedMapsToFLMTwisted`.

This is **an actual bijection of chosen finite coordinate labels only**, not a claim of an invariant Monster subrepresentation, Griess homomorphism or gravitational mode equivalence.

**P0a OPEN** `originalRefinedFLMToOrbifoldWeightTwoBidi`: actual sector-preserving bijection to the selected original FLM *weight-two basis*, not merely to the numerically typed `Fin` chart. Must preserve its fixed/twisted provenance.  
**P0b OPEN** `originalGravityFieldModeSourceMap`: select the physical 26+1 or 5D field solution/mode carrier and construct its on-shell gauge-quotiented states with normalization. Do **not** identify 5D with 26+1.  
**P0c OPEN** `gravityFLMCharacterFalsificationReceipt`: for each common genuinely acting subgroup, compute exact characters on each side and exhibit either equality plus explicit intertwiner or a mismatch witness. Compare invariant subspace dimensions and stabilizers; do not assume either outcome.

**Deliverable:** pinned `agda --safe` proof receipt for the new coordinate file; exact dual round-trip tests; explicit physical carrier selection; non-promotion record.

### Phase P1 — Original V-natural / FLM / Y443 same-object construction

**P1.01 OPEN** `originalLeechInvolutionFixedTwistedLinearEquivalence`: actual original (V_\Lambda^+ \oplus (V_\Lambda^T)^+) linear-source identification, shared zero and inverse.  
**P1.02 OPEN** `originalVNaturalTFIntertwiningModes`; **P1.03 OPEN** `originalVNaturalTTIntertwiningModes`: original mixed modes of the same selected `Vnatural`.  
**P1.04 OPEN** `originalVNaturalMixedJacobiLocality`: all FF/FT/TF/TT mixed Jacobi, locality, translation, conformal and grading obligations on the selected source.  
**P1.05 OPEN** `originalSelectedConcreteGriessProduct`: inhabit `ConcreteGriessProduct`, including actual mode-one product and bilinear form on `Vnatural_2`.  
**P1.06 OPEN** `originalSelectedWeightTwoGeneration`: inhabit `WeightTwoGeneration` for actual selected `Vnatural`.  
**P1.07 OPEN** `originalSelectedFLMExtension`: inhabit `SelectedFLMExtension` for its actual Griess product, preserving all VOA modes.  
**P1.08 OPEN** `originalSelectedMonsterGriessIdentification`: full source-justified Monster group ↔ selected Griess automorphism identification.  
**P1.09 OPEN** `originalY443AllNodePairWordCertificate` and `originalY443EightyRelatorsSatisfied`: original selected same-group 80-relator and all-word-generation witnesses, plus actual Y443 quotient-to-Monster isomorphism.  
**P1.10 OPEN** `originalJMDAndPublishedActionsAgreeOnUV`: inhabit the exact `agreesOnJMDU` and `agreesOnJMDV` terms together with `originalAction` and `classicalAction`.

**Reuse, do not rewrite:** `originalAndPublishedActionsAgreeEverywhere` already closes the all-element conditional transport once `PublishedFLMAndJMDSource` is supplied.

**Deliverable:** an **inhabited** `PublishedFLMAndJMDSource` for the original selected carrier; exact-head golden kernel receipt; same-state action regression. Source signatures or `Set`-valued fields alone are not inhabited receipts.

### Phase P2 — Genuine gravity/VOA operator crosswalk (test before promoting)

**P2.01 OPEN** `gravityFLMOriginalSectorMap` and `gravityFLMOriginalSectorInverse`: linear bounded/gauge-reduced map and two inverse identities on a well-defined domain (or an exact failure witness).  
**P2.02 OPEN** `gravityFLMOriginalIntertwiner`: `F (U_grav(g)x) = U_Vnatural(g)(F x)` for the actual same group (g).  
**P2.03 OPEN** `gravityFLMOriginalModeOneCompatibility`: source-defined first product and actual gravity-side operation, when physically meaningful, commute through `F`.  
**P2.04 OPEN** `gravityFLMOriginalPhysicalPairing`: norm/inner-product conservation with physical states and positivity.  
**P2.05 OPEN** `gravityFLMOriginalDynamicsCompatibility`: `F H_grav = L0 F` or a precisely defined spectral/functional-calculus equivalence; compare domains and self-adjoint closures.  
**P2.06 OPEN** `gravityFLMOriginalSpectrumCompatibility`: matched spectral projectors and multiplicities, with matching representations rather than total-dimension counts.  
**P2.07 OPEN** `gravityFLMObstructionOrWeld`: either a complete set of P2.01–P2.06 witnesses or an explicit incompatibility (character, signature, product, domain or spectral difference).

**Deliverable:** executable exact small-subgroup and low-level trace/pairing/projection tests; typed theorem/obstruction; no forced positive result.

### Phase P3 — Physical KK field equations, 4D reduction and stress

**P3.01 OPEN** `originalFiveDimensionalEinsteinMatterSolution`: explicit 5D geometry, couplings and matter satisfying sourced Euler–Lagrange equations; derive variation, constraints and boundary conditions.  
**P3.02 OPEN** `originalKKReductionMetricEquality`: an actual 5D-to-4D field reduction including metric, connection, gauge strength, scalar and stress sources and physical dimensions.  
**P3.03 OPEN** `originalTwentySevenDimensionalProposedSpectrumDynamicalSolution`: separate 26+1 proposal; construct an on-shell background and physical linearized mode quotient before identifying its 196884 tally.  
**P3.04 OPEN** `originalKKMonsterActionIntertwiner`: source action on on-shell solutions and a same-group intertwiner to selected VOA states.  
**P3.05 OPEN** `originalRenormalizedStressConservation`: specify a stress tensor with covariant conservation and the same selected state/metric, including counterterms.  
**P3.06 OPEN** `originalMonsterStressCMP119SameObjectWeld`: consume the actual `MonsterExceptionalStressHandoff`, the original CMP119 stress source and exact curvature/conservation compatibility.

**Deliverable:** sourced variational derivation, exact tensor/coordinate checks, gauge-invariant observables, renormalization receipt and independently reproducible physical solution. An arithmetic 299+1 split is not payment.

### Phase P4 — AdS3 / Monster boundary and black-hole thermodynamics

**P4.01 OPEN** `originalAdS3BulkBoundaryHilbertDictionary`: specify a consistent 3D bulk theory, physical Hilbert space, boundary CFT and operator dictionary with matching central charge and boundary conditions.  
**P4.02 OPEN** `originalMonsterPartitionFunctionEquality`: derive properly normalized same-regime bulk and (V^\natural) partition functions (including vacuum shift, modular properties and quantum corrections).  
**P4.03 OPEN** `originalBTZMicrostateEntropyAsymptotics`: extract state degeneracies at physically specified energy/angular momentum and compare with BTZ entropy, including subleading errors.  
**P4.04 OPEN** `originalAdS3StressWardVirasoroCompatibility`: prove conserved charge, stress Ward and Virasoro compatibility under the same dictionary.  
**P4.05 OPEN** `originalAdS3GravityDualityOrCounterexample`: genuine equivalence with the specified assumptions or decisive mismatch; distinguish pure-gravity conjecture from existence of the Monster CFT.

**Deliverable:** exact modular-coefficient test suite beyond (196884), character decomposition and controlled asymptotics; no conclusion from `ln(196883) ≈ 4π` alone.

### Phase P5 — 4D Yang–Mills and physical observer/OS mass-gap endpoint

**P5.01 OPEN** `originalWilsonWardScalarPhysicalEquality`: complete original Wilson/reduced-FP/Haar Ward scalar, exact tensor/symmetry attribution and rigorous remainder.  
**P5.02 OPEN** `originalUniformDifferentiatedAnalyticShellEstimate`: uniform physical differentiated-shell bound for all three actual response marks.  
**P5.03 OPEN** `originalPhysicalDoobNegativeHessianDebtBound`: continuous-time source heat/Doob/Hessian inequality.  
**P5.04 OPEN** `originalInteractingContinuumMeasure`: nontrivial uniform infinite-volume/continuum constructive YM state and correlators.  
**P5.05 OPEN** `originalSameContinuumOSPositiveHilbert`: actual OS reconstruction, same selected E1 measure and correct operator domains.  
**P5.06 OPEN** `originalOSHamiltonianPositiveGap`: strictly positive gap in the reconstructed physical Hamiltonian with the needed nontrivial observables.  
**P5.07 OPEN** `originalRenormalizedCompositeStressOPE`: curvature/composite fields, stress, OPE coefficients, short-distance behavior and conservation on that same continuum.  
**P5.08 OPEN** `originalYangMillsAllGroupsClayTransfer`: required compact simple groups and full Clay scope.

**Deliverable:** pinned Agda/Lean source acceptance, physical continuum estimates, rigorous OS spectral statement. The mass-gap theorem **remains OPEN**; no declaration is made to the contrary.

### Phase P6 — FRACTRAN / FRACDASH logical-to-physical computation

**P6.01 OPEN** `fractranReversibleStepWithHistory`: exact reversible encoding of first-enabled rule, old state and necessary history; prove forward/inverse laws.  
**P6.02 OPEN** `fractranComputeCopyUncompute`: reversible clean-output execution and restoration of ancillas; quantify persistent history.  
**P6.03 OPEN** `fractranOriginalPeakSpaceBound`: count live heap, tapes, pointers, temporary buffers and copied words for the *actual* N21 verifier.  
**P6.04 OPEN** `karpFractranBitMachineClockPolynomial`: prove true polynomial native-bit clock for the compiled same-original input; no unary cost substitution.  
**P6.05 OPEN** `physicalEncodingDecoderInverse`: define physical degrees of freedom, state preparation and detector readout for both representations.  
**P6.06 OPEN** `samePhysicalHamiltonianEvolution`: literal device Hamiltonian/Lindbladian and physical transition semantics with error bounds.  
**P6.07 OPEN** `physicalWorkHeatEntropyBalance`: closed first-law and entropy-production accounting (switching, data movement, clocks, leakages, erasure, cooling).  
**P6.08 EMPIRICAL-OPEN** `matchedFRACDASHBinaryEnergyReceipt`: identical input/output, reliability and throughput; measured energy, traffic, uncertainty and repetitions on the same machine.

**Deliverable:** formal logical-correctness certificate plus separate recorded instrumented CPU/GPU receipts. Do not mistake Hamming distance or compression ratio for physical heat.

### Phase P7 — Same-H transport and controlled joint physical prediction

**P7.01 OPEN** `nativeC3HamiltonianToSelectedMonsterState`: actual spectral intertwiner from #1489 finite C3 model into selected Monster representation, rather than same character count.  
**P7.02 OPEN** `selectedDensityEntropyWithHamiltonian`: positive normalized density operator, physical temperature/control, same-H thermal trace and entropy.  
**P7.03 OPEN** `selectedStressTraceGRCompatibility`: conserved stress and gravity dynamics on this same physical state.  
**P7.04 OPEN** `sameStateObservableErrorBound`: quantitative prediction with calibration, uncertainties, finite-size limits and fixed observational regime.  
**P7.05 EMPIRICAL-OPEN** `heldOutPhysicalValidation`: independently measured prediction separating model from a baseline.

**Deliverable:** a single traceable chain `source representation → physical state/H → entropy → stress/dynamics → observable → held-out receipt`, or a decisive failed commutation/counterexample.

## 3. Dependency DAG and maximum cut

```text
P0 finite inverse chart  [SOURCE-WRITTEN; KERNEL PENDING]
  ├─ P1 original Vnatural + Griess + Y443 ─┐
  └─ P0b original physical field modes ────┼─ P2 same-object intertwiner ─┐
P3 five-dimensional/27D field dynamics ────┘                              ├─ P7 physical state+stress+prediction
P4 independent AdS3 bulk/boundary dictionary ─────────────────────────────┘
P5 original YM E1 → OS4 → spectral gap (independent Clay endpoint)
P6 FRACTRAN reversible proof → real physical device model → measured energy
P6 + P7 join ONLY at a specified same-H physical device or quantum system
```

**Highest information per proof effort now:**
1. Kernel-check P0 and test an actual explicit candidate group action on its sectors (character/commutator falsification).
2. Inhabit original `PublishedFLMAndJMDSource` on #1472, targeting mixed VOA and Griess operations before any new global action proof.
3. Provide one actual background/on-shell spectrum for proposed gravity-side states and compare character and form to FLM. If characters disagree, record no-go with exact assumptions.
4. Reuse #1489 same-H finite thermal setup only after a real representation-state intertwiner.
5. Execute P6 reversible/logical proofs and instrumentation separately; do not make the YM Clay programme a prerequisite to energy measurements.
6. In parallel pursue P5 physical inequalities and E1/OS continuum. The Clay endpoint is independent and cannot be inferred from P0–P4.

## 4. Kernel, test, source and empirical receipts

**Phase 0 local golden candidate** (from the PR's repository worktree with pinned Agda 2.9 and stdlib):
```bash
agda -i . DASHI/Moonshine/MonsterSpecialGravityKKRefinedCoordinateBidiExact.agda
python3 scripts/check_y443_vnatural_pair_bridge.py --finite-only
python3 scripts/check_y443_vnatural_pair_bridge.py
```
The final command is intended to fail closed if Agda is absent. Run the repository's pinned golden wrapper where required; no command above was executed merely by writing this roadmap. Record the tested full commit SHA, toolchain hash, exit code and stdout/stderr digest.

For each theorem, keep an append-only receipt row:
`gate | original source path | branch@full SHA | target exact type | witness provider | import closure | Agda/Lean kernel receipt | independent finite test | physical test | status | falsifier`.

**No-go priority:** make each claimed physical equivalence falsifiable by an exact character mismatch, inner-product signature mismatch, failed product preservation, spectral/domain mismatch, gauge-noninvariance or energy conservation violation.

## 5. Next phase deliverables checklist

- [x] Source-write P0 refined coordinate maps and both inverse equations; commit to #1472 branch (new proof candidate).
- [x] This source-owned, phase-scoped exact maximum-cut roadmap.
- [ ] Agda 2.9 exact-head kernel verification of P0.
- [ ] Source selection of actual original on-shell gravity modes (5D and proposed 26+1 treated distinctly).
- [ ] Concrete character and operator-level P2 falsification tests.
- [ ] Original P1 genuine Griess + four-sector VOA witness providers.
- [ ] Physical P3/P4/P5 source proofs or explicit no-go receipts.
- [ ] P6 device measurements and full physical cost accounting.
- [ ] P7 physical prediction with held-out validation.

**Last audit state:** 2026-11-14; do not mark new proof code kernel-accepted or mark the unsolved physical endpoints closed without the matching receipts.
