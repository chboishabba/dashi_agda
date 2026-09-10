module DASHI.Physics.Closure.Everything where

-- Authoritative closure / Clay-facing rollup.
-- New NS/YM closure surfaces should be wired here (or into a narrower
-- subfolder Everything) before being promoted into DASHI.Physics.Everything.

import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface

-- Current Navier--Stokes terminal and critical-path surfaces.
import DASHI.Physics.Closure.NSFinalStateReceipt
import DASHI.Physics.Closure.NSFastestClayPathReceipt
import DASHI.Physics.Closure.NSPaper1ClayTargetReceipt
import DASHI.Physics.Closure.NSGlobalH118BoundReceipt
import DASHI.Physics.Closure.NSW4WeakSolutionReceipt

-- Reusable exact NS kernels consumed by the terminal surfaces.
import DASHI.Physics.Closure.NSPeriodicConcreteNorms
import DASHI.Physics.Closure.NSCrossShellSchurBound
import DASHI.Physics.Closure.NSFactorizedSchurFrameGap
import DASHI.Physics.Closure.NSTriadKNCarrierCoverage
import DASHI.Physics.Closure.NSTriadKNBKMContinuation
import DASHI.Physics.Closure.NSTriadKNLuoScalingExact
import DASHI.Physics.Closure.NSTriadKNResonantNullGain

-- Finite Base369 ternary-27 -> Z^3 resonance regression.  This reuses the
-- literal physical triad carrier and keeps raw cutoff resonance distinct from
-- nonzero, conjugacy, phase/helicity, Schur and amplitude layers.
import DASHI.Physics.Closure.Base369Ternary27Z3TriadRegressionExact

-- 2026 almost-orthogonal Gram/Schur x-pollination: realized-data vs
-- structural-operator Schur, angular/helicity/phase producer frontiers,
-- absolute->block->signed fallback hierarchy, zero-safe defect API, the
-- literal R329 nested anti-parallel pointwise gain / radius-calibration seam,
-- exact reduction of global coherence to fixed-output fibres, physical
-- three-class Bony reduction, and critical-cone compiler.
import DASHI.Physics.Closure.NSTriadKNDataOperatorSchurCrossPollination2026Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalGramProducerFrontier2026Exact
import DASHI.Physics.Closure.NSTriadKNGramControlFallbackHierarchy2026Exact
import DASHI.Physics.Closure.NSTriadKNZeroSafeCollinearityDefectInterface2026Exact
import DASHI.Physics.Closure.NSTriadKNAlmostOrthogonalSchurCriticalRouteXPollination2026Exact
import DASHI.Physics.Closure.NSTriadKNLiteralNestedOuterAntiParallelNormRound430Exact
import DASHI.Physics.Closure.NSTriadKNLiteralNestedOuterRadiusDefectRound431Exact
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact
import DASHI.Physics.Closure.NSTriadKNFixedOutputNestedBonyCrossRound433Exact
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact

-- Finite rational Cauchy completion / diagonal endpoint tranche.  This keeps
-- the full positive Cauchy form, literal R397 off-diagonal flux, normalized
-- double-mixed mass, fixed-output energy-square routing, and temporal endpoint
-- orientation on the same physical carrier.  The chain closes the negative
-- terminal-flux endpoint conditional on the explicit Fourier/radius
-- calibrations; Package A remains open at the initial positive-flux and
-- integrated nonlinear-remainder leaves.
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact
import DASHI.Physics.Closure.NSTriadKNFiniteKernelRankOneQuadraticSplitRound444Exact
import DASHI.Physics.Closure.NSTriadKNRationalFiniteCauchyPSDCompilerRound445Exact
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyResolventCompletionRound447Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyOffDiagonalR397WeldRound448Exact
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact
import DASHI.Physics.Closure.NSTriadKNFixedOutputEnergySquareRoutingRound454Exact
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact
import DASHI.Physics.Closure.NSTriadKNCauchyTerminalFluxEndpointRound458Exact
import DASHI.Physics.Closure.NSTriadKNTerminalFluxPaidTemporalReductionRound459Exact
import DASHI.Physics.Closure.NSTriadKNFiniteInitialCoherentEndpointRound460Exact
import DASHI.Physics.Closure.NSTriadKNCauchyInitialAmplitudeEndpointRound461Exact
import DASHI.Physics.Closure.NSTriadKNGlobalNormalizedCompanionMassRound462Exact
import DASHI.Physics.Closure.NSTriadKNGlobalCauchyTerminalEndpointRound463Exact

-- R464-R470 bidi/routing completion.  MHD supplies the reciprocal-radius law;
-- the NS lane keeps only the representation-specific radius-square receipt.
-- Existing rational Bernstein and dyadic support owners feed R234 without a
-- duplicate finite-CS implementation.  R467 proves the literal normalized
-- anti-parallel complement, R468 compiles it into both R177 and R431, and
-- R469/R470 derive the global R109 ED routing from output-local provenance and
-- the already-owned literal output-fibre partition.
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact
import DASHI.Physics.Closure.NSTriadKNRationalInfinityShellBernsteinRound465Exact
import DASHI.Physics.Closure.NSTriadKNDeepFarLowDyadicBernsteinWeldRound466Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalHHAndNestedRadiusCompilerRound468Exact
import DASHI.Physics.Closure.NSTriadKNSelectedPairPhysicalTriadRoutingRound469Exact
import DASHI.Physics.Closure.NSTriadKNOutputIndexedEDProvenanceRound470Exact

-- R471-R481 Lean<->Agda Gram-operator return, terminal minimization, and
-- first-missing proof-search routing.  R471 identifies the weakest uniform
-- Gram-operator consumer.  R477 installs the literal nonseparable Cauchy pair
-- kernel.  R478 removes the unnecessary requirement to prove separate +/-
-- scalar bounds by preferring the total resolved all-coefficient bound.  R479
-- isolates a signed residual allowance producer so paid diagonal structure can
-- be reused without absolute values.  R480 follows the actual R472/R432
-- downstream type one step further: the final physical consumer needs only the
-- selected physical coefficient snapshot, not a theorem for every hypothetical
-- coefficient vector.  R481 applies the repository first-missing discipline:
-- construct the physical same-object snapshot first; only then admit the
-- selected resolved inequality as the live analytic search.  Uniform R478 and
-- split R477 remain sufficient producer routes only.
import DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorPaymentRound472Exact
import DASHI.Physics.Closure.NSTriadKNWeightedPhysicalGramOperatorCarrierRound473Exact
import DASHI.Physics.Closure.NSTriadKNHelicalSignedGramSplitRound474Exact
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact
import DASHI.Physics.Closure.NSTriadKNProjectedVsDirectSignedGramBoundaryRound476Exact
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedDirectConsumerRound478Exact
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedSignedResidualRound479Exact
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedPhysicalSnapshotRound480Exact
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedProofSearchRound481Exact
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedTerminalEverythingRound479Exact

-- R487-R493 return to the canonical direct R423 Clay consumer while restoring
-- the same-object firewall. R487 compiles theorem-bearing fixed-output signed
-- payments plus one cutoff-uniform sum-of-budgets theorem into the scalar R423
-- shape. R488 makes local payments the first producer. R489 records that direct
-- signed payment is the canonical physical route and that Laplace is optional.
-- R490/R491 retain the standard positive-rate Laplace producer lane without
-- making it mandatory. R492 then requires an external theorem identifying the
-- fixed-output scalar aggregate with the literal integrated R420/R439
-- quadratic-companion observable before constructing the Clay-facing R423
-- payment. R493 preserves that historical strict audit.
import DASHI.Physics.Closure.NSTriadKNFixedOutputPaymentsToR423Round487Exact
import DASHI.Physics.Closure.NSTriadKNR423FixedOutputProducerProofSearchRound488Exact
import DASHI.Physics.Closure.NSTriadKNR423LocalPaymentPrerequisiteRound489Exact
import DASHI.Physics.Closure.NSTriadKNPositiveRateLaplaceAuthorityRound490Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyLaplaceWeldRound491Exact
import DASHI.Physics.Closure.NSTriadKNStrictFixedOutputCompanionToR423Round492Exact
import DASHI.Physics.Closure.NSTriadKNStrictR423ProofSearchRound493Exact

-- R494-R505 sharpen the live route onto the literal R406 off-diagonal carrier.
-- R494 fixes the factor-two R299/R439 normalization; R495 records optional
-- integration transport. R496-R500 construct the exact nonseparable rational
-- resolvent signed cross pair->fibre->global->trajectory->integrated. R502
-- prevents conflation of that off-diagonal object with R439's full square form.
-- R503 targets the exact R415 consumer instead, R504 exposes the two independent
-- Clay-facing analytic leaves, and R505 aggregates the whole direct terminal
-- cone for focused validation.
import DASHI.Physics.Closure.NSTriadKNLiteralR406DirectTerminalEverythingRound505Exact

-- TOE integration: native SSP/369 symmetry action, equivariant two-sheet
-- reduction, residual-bearing 9 -> 6 reopening, and NS 3 x 3 nonary chart.
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Coupled-trajectory/Feynman/Kelvin cross-pollination: finite histories,
-- path fibres, stationary coherence classification, wavelength/source-scale
-- conditioning, context-dependent weighting, TSFV invariant boundary, and
-- source-bounded experimental support.
import DASHI.Physics.Closure.FeynmanKelvinTrajectoryCrossPollinationExact
import DASHI.Physics.Closure.ApertureWakeModeSelectionBridgeExact
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact
import DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact
import DASHI.Physics.Closure.SinglePhotonRecoilRelationalObserverBridgeExact
import DASHI.Physics.Closure.TSFVLocalActionCandidateAuditExact
import DASHI.Physics.Closure.TSFVPairActionCandidateAuditExact
import DASHI.Physics.Closure.TSFVNonseparableTransitionKernelExact
import DASHI.Physics.Closure.TSFVBidirectionalActionRealizationObligationExact
import DASHI.Physics.Closure.TSFVActionPhaseWeightSeparationExact

-- Counterfactual parameter-space / multiverse-attractor cross-pollination.
-- TSFV contributes history/projection non-factorability only; it is not promoted
-- into a multiverse or anthropic-selection theorem.
import DASHI.Physics.Closure.TSFVMultiverseViabilityCrossPollinationExact
import DASHI.Physics.Closure.MultiverseAttractorDiscriminatorBidiExact
