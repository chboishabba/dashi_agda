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

-- R471-R477 Lean<->Agda Gram-operator return.  The weakest fixed-output
-- consumer is the signed l2->l2 Gram quadratic-form bound; Schur variants are
-- producers, not mandatory intermediates.  The existing R180/R383 signed Gram
-- and native helical +/- decomposition are reused directly.  R476 separates
-- the fully projected outer-cell lane from R440's unprojected signed companion,
-- and R477 installs the nonseparable Cauchy pair kernel explicitly.
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