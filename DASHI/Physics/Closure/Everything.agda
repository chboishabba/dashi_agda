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

-- R471-R477 Lean<->Agda Gram-operator return.  The weakest fixed-output
-- consumer is the signed l2->l2 Gram quadratic-form bound; absolute Schur,
-- block Schur, and operator-Schur are producers rather than mandatory
-- intermediates.  R473/R474/R475 reuse the literal R180/R383 signed Gram and
-- the existing helical +/- decomposition.  R476 keeps the fully projected
-- outer-cell lane distinct from R440's unprojected direct signed companion.
-- R477 installs the nonseparable Cauchy pair kernel explicitly, so the live
-- analytic frontier is two scalar same-helicity resolved-form bounds.
import DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact
import DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorPaymentRound472Exact
import DASHI.Physics.Closure.NSTriadKNWeightedPhysicalGramOperatorCarrierRound473Exact
import DASHI.Physics.Closure.NSTriadKNHelicalSignedGramSplitRound474Exact
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact
import DASHI.Physics.Closure.NSTriadKNProjectedVsDirectSignedGramBoundaryRound476Exact
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact

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