# DASHI Yang–Mills: reconciled maximum cut, exact lemmas and trust boundary

**14 November 2026.** Source-only handoff. Four physical research packages (Round87), six analytic families (Round84), seven named duties (Round83), 43 residual source/semantic slots (Round518), and five C-sector source packages (Round527) are **different projections of one research dependency graph**, not additive completion counters.

## Acceptance and latest concrete changes

- Original source owners: `BalabanClayHighestAlphaRound83SevenAnalyticLemmaExact`, `BalabanClayHighestAlphaRound84SixAnalyticLemmaExact`, `BalabanClayHighestAlphaRound87FourAnalyticLemmaExact`, `YangMillsClayPostStructuralT1ResidualRound518Exact`, `YangMillsClayCPhysicalPackageMaxCutRound527Exact`.
- This PR: `YangMillsClayMergedResearchAndResidualCountRound528Exact.agda` records 7, 6, 4, 43 and 5 without conflation; `YMClayRound83Round84Round87Round518Round527MergedMaxCut20261114.json` has every exact original Round518 leaf and its owner; `scripts/check_ym_round83_to_527_merged_maxcut.py` is fail closed.
- PR #1444 continuation: `BalabanCMP109116ConstructiveScalarCoreExact.agda`, `BalabanCMP109116BishopRealSetoidInstantiationExact.agda`, `YangMillsStressOSCommonSemigroupDerivativeExact.agda`, `YangMillsStressOSSourceFirstSemigroupCoreToClosureExact.agda`. Seven legacy real-dependent Round103/108/119 modules had misleading `--safe` annotations removed. More downstream safe-import audits are required.
- PR #1498: the source-independent compact-simple Haar local remainder and exact rational budget were delivered previously; its physical cutoff chart and Ward scalar remain open.
- No source change in these PRs has a new pinned Agda 2.9 kernel receipt here. No Clay endpoint is closed.

## Four research completion packages

| Research package | Physical completion criterion | Remaining independent mathematics |
| --- | --- | --- |
| A: positive tuned beta | Same generated coupling history gives a strict bilateral terminal-tail slope and tuned nonvanishing observation window | Literal constrained Wilson/FP/Haar coefficient, nonlinear remainder, uniform response/history bounds, tuned trajectory |
| B: differentiated marked locality | Same CMP116 activities give distinct beta/spatial/composite marks with uniform radii and a geometric shell energy estimate | Actual interacting rooted-polymer bounds, differentiated response and energy tail |
| C: same-density heat/mass gap | On the literal Gibbs density, finite integrated negative Hessian/Doob debt plus dynamic weighted influence yield clustering and a common OS spectral gap | Physical continuous-time heat/Doob curvature, spatial influence, full nonvacuum physical-time decay |
| D: continuum local QFT | Same E1 continuum admits local gauge-invariant composite fields, physical OPE/AF coefficients, and renormalized stress/translation Ward identity | Nonperturbative local-field, coefficient and stress Ward constructions |

## The seven duties / six independent families

| Duty | Exact remaining theorem | Classification |
| --- | --- | --- |
| L1 | Construct literal indexed four-sector `PhysicalIndexedFourSource`, prove Ward defect cancellation on original source, four diagram off-diagonal mixed jets and the selected `C_A*(11/24)` coefficient, then an admissible cutoff-uniform same-step remainder | Perturbative source evaluation + genuinely new nonperturbative remainder |
| L2 | Derive original `CMP116CommonAnalyticRadius` and the three differentiated response bounds with **distinct typed depth metrics**; beta mark is irrelevant/polymer memory at fixed marginal coupling, not exponential forgetting of `g_(j-1)` | Uniform analytic estimate + same-object coordinate welds |
| L3 | For original `u_t=H_t(e^{-V_0})`, prove positivity and `(D_X u_t)^2-u_t D_X^2 u_t+eta_t u_t^2 |X|^2>=0`, with `integral_shell eta_t dt <= C*(17/32)^n`; then Ricci reserve yields uniform LSI | Genuine physical continuous-time analytic inequality |
| L4 | Construct selected gauge-invariant curvature/composite family as nuclear distributions/operators on SAME E1 limit and prove first-variation/Hilbert continuity and locality | Genuine continuum construction, with existing completion compiler |
| L5 | Identify actual physical OPE remainder with `PhysicalOPERemainderSharedTail`, prove actual one-step operator-mixing coefficients and UV normalization | Physical OPE/AF identification; tail summation downstream |
| L6 | On SAME original renormalized density, prove metric variation is CMP119 insertion, local translation Ward identity and spatial cutoff removal for stress charge | Genuine local-QFT source construction + weld |
| L7 | Show stress charge acts as the **negative right derivative of the same Euclidean OS contraction semigroup**, on a common graph core with suitable essential self-adjointness. Then operator equality follows from the existing Round86 closure theorem | Physical same-core Ward/domain theorem; operator uniqueness established standard analysis |

Round84 combines L6/L7 into one family; the physical L7 action/domain identification remains mandatory. Also note that Round518 does **not** have a standalone L3 or L7 leaf: these cannot be silently dropped by its 43-entry list.

## Exact L7 proof contract

On the **same Schwinger/OS reconstruction** `(H_OS, H, Omega)`, define `T(t)=exp(-t H)` for `t>=0`. For every `psi` in one dense graph core `D`, prove:

```
  lim_(t downarrow 0) (T(t)psi-psi)/t = -H psi
  lim_(t downarrow 0) (T(t)psi-psi)/t = -Q psi
```

The second identity is the *physical* renormalized Ward theorem for the integrated `T_00` charge `Q`, not a freely selected operator. By uniqueness of the Hilbert-norm limit, `Qpsi=Hpsi` on `D`. Prove `D` is a graph core for `H`, and the symmetric `Q|_D` is essentially self-adjoint with closure `Q`. Then `Q=H` as closed operators. Only after this may one conclude `exp(i sQ)=exp(i sH)` for real time. The Euclidean semigroup itself is NOT a unitary group.

Existing owner `YangMillsStressWardCommonCoreGeneratorExact` compiles core-action equality + equal closure data; `YangMillsClayPinnedCMP119StressCommonCoreExact` anchors it to the SAME CMP119 OS Hamiltonian; `YangMillsClayPinnedCMP119Round109ToCommonCoreExact` anchors the completed stress source. The new source-first semigroup adapter reuses Round86 without inventing a second Hamiltonian. **Its derivative/closure fields remain physical obligations**, not completed source proofs.

## Constructive real migration

The older `RealAnalysisAxioms` declares a postulated `ℝ` with `≡` ring equations. DASHI's actual Bishop carrier uses mathematical `≃`. Silent aliasing is invalid for distinct Cauchy representations. The safe migration is:

1. Make the original finite CMP109/CMP116 same-potential algebra parametric in `Scalar`; prove same-source second-variation and covariance **definitionally** without real postulates. This is now source-written as `BalabanCMP109116ConstructiveScalarCoreExact`.
2. Instantiate that generic kernel on `Real.ℝ`, `Real._≃_`, `Real._+_`, `Real._*_`, `Real._-_` using the vendor Bishop implementation. This is now source-written as `BalabanCMP109116BishopRealSetoidInstantiationExact`.
3. Rewrite every legacy real equality-sensitive consumer from `≡` to `≃` where mathematically extensional, and prove the old-to-new source interpretation preserving derivatives, finite Haar integration, order, subtraction and normalized expectation.
4. Define actual Bishop/compact-group analytic completions (heat kernel, Bochner identity, matrix Lie group, covariance, differentiation-under-integral, core topology) rather than hiding these as `Set` markers or constructing an independent postulated real.
5. Run the explicit source trust checker; only call a root `--safe` after the ENTIRE importing closure is safe and a pinned Agda 2.9 kernel check succeeds.

At present the new core is postulate free, but **the legacy source and its transitive imports are not globally unpostulated**. Removing an incorrect `--safe` flag repairs the claimed trust *status*, not the mathematical assumptions.

## All 43 Round518 residuals, exact original names

All names below remain source-acceptance obligations. A logical compiler or source-specific intermediate theorem must not be promoted to its physical completion without a real inhabitant.

### A / L1 — original constrained Gaussian, Wilson/FP/Haar one-loop source (7)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `a1WilsonHessianVariation` | source analysis | physical analysis |
| `a1AveragingConstraintVariation` | source analysis | physical analysis |
| `a1GaugeProjectionVariation` | source analysis | physical analysis |
| `a1WQRAssembly` | source analysis | same object weld |
| `a1ConstrainedGaussianMixedCoefficient` | source analysis | physical analysis |
| `a1PhysicalJetFiveChannelSplit` | source analysis | same object weld |
| `a1FourJointReceiptEvaluation` | source analysis | physical analysis |

### A / L2 — history-mark and beta source coordinate (1)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `a2BetaMarkGeneratedHistoryShell` | source attachment | same object weld |

### B — two insertion/Wilson connected shell estimate (2)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `bWilsonTwoMarkExpansion` | source analysis | physical analysis |
| `bWilsonConnectingWeightTail` | source analysis | physical analysis |

### B — OS reconstructed physical-time transfer coordinate (1)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `bSameHamiltonianTransferCoordinate` | source analysis | same object weld |

### D / L4 — curvature, composite fields and nuclear Hilbert continuity (6)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `c1MarkedSourceHilbertModulus` | source analysis | physical analysis |
| `c1CurvatureGaugeLocalSemantics` | source attachment | same object weld |
| `t4GaugeInvariantLocalObservableSemantics` | endpoint semantic | endpoint semantics |
| `t4CurvatureCorrespondenceSemantics` | endpoint semantic | endpoint semantics |
| `t4CurvatureGaugeInvariantSemantics` | endpoint semantic | endpoint semantics |
| `t4CurvatureLocalitySemantics` | endpoint semantic | endpoint semantics |

### D / L5 — physical OPE and AF coefficients (5)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `c2PhysicalRemainderIsCompositeTail` | source attachment | same object weld |
| `c3OneStepAFRGIdentification` | source attachment | physical coefficient identification |
| `t4ShortDistanceAFSemantics` | endpoint semantic | endpoint semantics |
| `t4PhysicalOPECoefficientSemantics` | endpoint semantic | endpoint semantics |
| `t4PhysicalOPERemainderSemantics` | endpoint semantic | endpoint semantics |

### D / L6+L7 — same-family renormalized stress and OS charge (6)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `c4LiteralDensityMetricDerivative` | source analysis | same object weld |
| `c4FiniteStressInsertionIsCMP119Local` | source attachment | same object weld |
| `c4StressCompletionIsCompletedMarkedStress` | source attachment | same object weld |
| `c4CompletedStressIsClayStress` | source attachment | same object weld |
| `c4DensityAnchoredLaneInstantiation` | source attachment | same object weld |
| `t4StressTensorAndOPESemantics` | endpoint semantic | endpoint semantics |

### A3/A4/A5 — continuum, finite RP and OS attachments (13)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `a3ProjectiveEventExpectationConsistency` | source analysis | physical analysis |
| `a3ContinuityAtEmpty` | source analysis | physical analysis |
| `aFiniteEuclideanSameObjectAttachment` | source attachment | same object weld |
| `aFiniteBosonicSameObjectAttachment` | source attachment | same object weld |
| `aFiniteWilsonRPSameObjectAttachment` | source attachment | same object weld |
| `a3StressDensityIsLiteralFiniteMeasure` | source attachment | same object weld |
| `a3SourceOSIsLiteralSchwinger` | source attachment | same object weld |
| `a3CylinderEventIndicatorSemantics` | source attachment | same object weld |
| `a3CylinderExpectationIntegralIdentification` | source attachment | same object weld |
| `a45QuantitativeFiniteExpectationAttachment` | source attachment | same object weld |
| `a4RepresentedRegularityExtensionality` | source attachment | same object weld |
| `a5RepresentedGrowthExtensionality` | source attachment | same object weld |
| `literalCMP119Section2Family` | source bundle | source realization |

### G1 — actual group-dependent physical source (2)

| Exact R518 leaf | Stratum | Work type |
| --- | --- | --- |
| `g1ArbitraryCompactSimpleSourceMap` | source analysis | physical group realization |
| `allGroupCompactSimpleWitness` | source bundle | source realization |

## Additional mandatory gates not exhausted by the 43

- **E1:** full changing-cutoff interacting Wilson measure and projective/OS continuum estimates.
- **D2:** positive full nonvacuum mass gap for same OS Hamiltonian and uniform physical-time decay.
- **N1:** actual non-generalized-free/nontrivial continuum witness, not Gaussian nonlinear-observable cumulant.
- **G1:** physical group-specific construction all compact simple types rather than only Casimir positivity.
- **L1.literal_P0:** actual diagram numerators, Ward identity and quadrature omitted by simply naming A1 WQR.
- **L3.heat:** not separately enumerated among the 43 R518 leaf names.
- **L7.same_OS_charge:** not separately enumerated among the 43 R518 leaf names.
- **legacy_real_trust:** Bishop setoid migration and safe-import closure unresolved.
- **G2_source_witness:** earlier R496 G2 source witnesses not explicitly included in R518's 43; review via later nontriviality compiler.

## Phases and deliverables

- **P0 — kernel/trust:** run `python3 scripts/audit_ym_legacy_real_safe_boundary.py --strict --json` on PR #1444, repair every transitive unsafe import, and obtain Agda 2.9 receipts for both the new safe core and Bishop specialization; do not mark the old carrier unpostulated until the source semantics are ported.
- **P1 — physical L1:** from P33 Wilson higher vertices + original reduced FP + exponential-map Haar derive four actual indexed numerators; calculate the CMP109 transverse mixed second jet and Ward identity; prove cutoff-independent R_local remainder.
- **P2 — marked estimates:** literal uniform CMP116 radius, all three response producers and historical marginal/irrelevant decomposition; rooted shell weighted estimates; no conflation of marks.
- **P3 — E1/D1/C mass gap:** actual original `F,G,FG` moment errors and RG convergence; polymer activities, continuous-time negative-Hessian bound, same-H nonvacuum exponential decay.
- **P4 — continuum local operators:** E1 same-family nuclear curvature, composite OPE remainder/one-step AF mixing and metric-stress first variation from original density.
- **P5 — OS stress charge:** actual Ward right-derivative on the common semigroup core, essential self-adjointness/graph core, and pinned CMP119 identity; no independent Stone group equality assumption.
- **P6 — endpoints:** N1 nontriviality and all compact simple physical group coverage; authoritative terminal proof object with formal scope audited, local Agda 2.9 and trust manifest.

## Reproducible checks

```bash
python3 scripts/check_ym_round83_to_527_merged_maxcut.py --json
# On the original YM #1444 branch or a source-preserving integrated worktree:
python3 scripts/audit_ym_legacy_real_safe_boundary.py --json
python3 scripts/audit_ym_legacy_real_safe_boundary.py --strict --json
# Then run the existing pinned local Agda golden scripts, with trust roots separated.
```

The Round518 manifest has been independently compared against the exact GitHub source for all 43 unique names (15+18+8+2). That is a source inventory check, not a kernel receipt or analytic bound.
