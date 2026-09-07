{-# OPTIONS --safe #-}
module DASHI.Core.ClayProofDebtFrontierAtlasExact where

------------------------------------------------------------------------
-- CLAY / SCIENCE PROOF-DEBT FRONTIER ATLAS
--
-- This module applies ProofDebtRouterExact to the currently exposed terminal
-- coordinates in the active RH / NS / YM proof-search lanes.  It is deliberately
-- conservative: a theorem is moved out of mathematical debt only when the repo
-- already distinguishes it as established/standard and the surviving defect is
-- statement, carrier, representation, or certification alignment.
--
-- Branch snapshots audited for this atlas (2026-09-08 AEST):
--   RH #824 agent/rh-direct-combined-off-cut
--   NS #825 agent/ns-r423-fixed-output-direct-compiler
--   YM #821 agent/ym-current-terminal-cutset-20260908
--
-- This atlas does NOT inhabit any Clay theorem and does not import branch-only
-- modules.  It is a scheduler/epistemic classification surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import DASHI.Core.ProofDebtRouterExact


data ClayLane : Set where
  riemannLane navierStokesLane yangMillsLane : ClayLane

data ClayCoordinate : Set where
  -- RH
  rhFinalNearLiteralPhaseRealisation : ClayCoordinate
  rhUniformHighJointComplementMargin : ClayCoordinate
  rhLowPublishedHeightCarrierTransport : ClayCoordinate
  rhCriticalLinePredicateRefinement : ClayCoordinate

  -- NS
  nsUniformDyadicHOneHalfEquivalence : ClayCoordinate
  nsUniformDyadicHThreeHalfEquivalence : ClayCoordinate
  nsLiteralR406SignedCrossEstimate : ClayCoordinate
  nsExternalCrossTriadSignedForcing : ClayCoordinate

  -- YM
  ymSelectedExpectationProbabilitySemantics : ClayCoordinate
  ymStandardOSReconstruction : ClayCoordinate
  ymSelectedPhysicalCoerciveCompactContainment : ClayCoordinate
  ymContinuumClustering : ClayCoordinate

  -- Cross-lane validation
  exactHeadAgdaValidation : ClayCoordinate

lane : ClayCoordinate → ClayLane
lane rhFinalNearLiteralPhaseRealisation = riemannLane
lane rhUniformHighJointComplementMargin = riemannLane
lane rhLowPublishedHeightCarrierTransport = riemannLane
lane rhCriticalLinePredicateRefinement = riemannLane
lane nsUniformDyadicHOneHalfEquivalence = navierStokesLane
lane nsUniformDyadicHThreeHalfEquivalence = navierStokesLane
lane nsLiteralR406SignedCrossEstimate = navierStokesLane
lane nsExternalCrossTriadSignedForcing = navierStokesLane
lane ymSelectedExpectationProbabilitySemantics = yangMillsLane
lane ymStandardOSReconstruction = yangMillsLane
lane ymSelectedPhysicalCoerciveCompactContainment = yangMillsLane
lane ymContinuumClustering = yangMillsLane
lane exactHeadAgdaValidation = yangMillsLane

------------------------------------------------------------------------
-- Canonical routed status for each currently distinguished coordinate.
------------------------------------------------------------------------

coordinateRoute : ClayCoordinate → ProofDebtRoutingReceipt

-- RH observer realization is a local representation/same-object weld, not a
-- new theorem about zeros.  Until the literal and abstract statements align it
-- is transcription/representation debt.
coordinateRoute rhFinalNearLiteralPhaseRealisation =
  proof-debt-routing-receipt
    deductiveTheorem derivedInRepo transcribedUnaligned proofDeferred
    localAgda transcriptionDebt refl

-- This is the actual high-ordinate theorem family whose uniform inhabitance
-- would drive the novel RH contradiction route.
coordinateRoute rhUniformHighJointComplementMargin =
  proof-debt-routing-receipt
    deductiveTheorem novelOpen transcribedUnaligned proofDeferred
    externalLean mathematicalDebt refl

-- Platt--Trudgian's rigorous verified-height theorem is established.  DASHI's
-- live defect is transporting that published statement to the exact completed-
-- zeta carrier / Low partition used by the consumer.
coordinateRoute rhLowPublishedHeightCarrierTransport =
  proof-debt-routing-receipt
    deductiveTheorem sourceEstablished transcribedUnaligned proofDeferred
    localAgda transcriptionDebt refl

-- The current critical-line predicate refinement is a local carrier/logical
-- identification seam.  It is not itself the analytic RH theorem.
coordinateRoute rhCriticalLinePredicateRefinement =
  proof-debt-routing-receipt
    deductiveTheorem derivedInRepo transcribedUnaligned proofDeferred
    localAgda transcriptionDebt refl

-- R517 explicitly identifies these as standard harmonic-analysis equivalences,
-- but the exact source theorem and literal Galerkin/dyadic carrier alignment are
-- not yet pinned.  Therefore they are source-alignment debt, not a new NS
-- cancellation theorem and not yet certification-only debt.
coordinateRoute nsUniformDyadicHOneHalfEquivalence =
  proof-debt-routing-receipt
    deductiveTheorem sourceEstablished transcribedUnaligned proofDeferred
    externalLean transcriptionDebt refl

coordinateRoute nsUniformDyadicHThreeHalfEquivalence =
  proof-debt-routing-receipt
    deductiveTheorem sourceEstablished transcribedUnaligned proofDeferred
    externalLean transcriptionDebt refl

-- These remain the model-specific nonlinear analytic leaves.
coordinateRoute nsLiteralR406SignedCrossEstimate =
  proof-debt-routing-receipt
    deductiveTheorem novelOpen transcribedUnaligned proofDeferred
    externalLean mathematicalDebt refl

coordinateRoute nsExternalCrossTriadSignedForcing =
  proof-debt-routing-receipt
    deductiveTheorem novelOpen transcribedUnaligned proofDeferred
    externalLean mathematicalDebt refl

-- Probability/expectation semantics on the already-selected literal measure
-- carrier is a representation/meaning weld, not a new YM existence theorem.
coordinateRoute ymSelectedExpectationProbabilitySemantics =
  proof-debt-routing-receipt
    deductiveTheorem derivedInRepo transcribedUnaligned proofDeferred
    localAgda transcriptionDebt refl

-- Osterwalder--Schrader reconstruction is established mathematics.  What must
-- still be checked is that the exact local Schwinger-system hypotheses and
-- conclusion consumed by DASHI match the source theorem.
coordinateRoute ymStandardOSReconstruction =
  proof-debt-routing-receipt
    deductiveTheorem sourceEstablished transcribedUnaligned proofDeferred
    externalLean transcriptionDebt refl

-- These remain model-specific until an exact source theorem is shown to apply
-- to DASHI's selected physical carrier.  "Looks standard" is not enough.
coordinateRoute ymSelectedPhysicalCoerciveCompactContainment =
  proof-debt-routing-receipt
    deductiveTheorem novelOpen transcribedUnaligned proofDeferred
    externalLean mathematicalDebt refl

coordinateRoute ymContinuumClustering =
  proof-debt-routing-receipt
    deductiveTheorem novelOpen transcribedUnaligned proofDeferred
    externalLean mathematicalDebt refl

-- Once theorem-bearing local code exists, lack of an exact-head typecheck is
-- certification debt.  It must never be re-described as mathematical openness.
coordinateRoute exactHeadAgdaValidation =
  proof-debt-routing-receipt
    deductiveTheorem derivedInRepo sourceAligned uncertified
    localAgda certificationDebt refl

------------------------------------------------------------------------
-- Canonical four-way frontier vocabulary requested by the scheduler.
------------------------------------------------------------------------

data CanonicalCutClass : Set where
  mathematicallyOpen
  sourceAlignmentOpen
  externalCertificationOpen
  localAgdaCertificationOpen
  closed : CanonicalCutClass

cutClass : ClayCoordinate → CanonicalCutClass
cutClass rhFinalNearLiteralPhaseRealisation = sourceAlignmentOpen
cutClass rhUniformHighJointComplementMargin = mathematicallyOpen
cutClass rhLowPublishedHeightCarrierTransport = sourceAlignmentOpen
cutClass rhCriticalLinePredicateRefinement = sourceAlignmentOpen
cutClass nsUniformDyadicHOneHalfEquivalence = sourceAlignmentOpen
cutClass nsUniformDyadicHThreeHalfEquivalence = sourceAlignmentOpen
cutClass nsLiteralR406SignedCrossEstimate = mathematicallyOpen
cutClass nsExternalCrossTriadSignedForcing = mathematicallyOpen
cutClass ymSelectedExpectationProbabilitySemantics = sourceAlignmentOpen
cutClass ymStandardOSReconstruction = sourceAlignmentOpen
cutClass ymSelectedPhysicalCoerciveCompactContainment = mathematicallyOpen
cutClass ymContinuumClustering = mathematicallyOpen
cutClass exactHeadAgdaValidation = localAgdaCertificationOpen

-- Regression pins: these coordinates must not drift back into the wrong queue.
rhLowIsNotMathematicalDebt :
  routedDebt (coordinateRoute rhLowPublishedHeightCarrierTransport) ≡ transcriptionDebt
rhLowIsNotMathematicalDebt = refl

rhHighRemainsMathematical :
  routedDebt (coordinateRoute rhUniformHighJointComplementMargin) ≡ mathematicalDebt
rhHighRemainsMathematical = refl

nsDyadicEquivalenceIsAlignmentDebt :
  routedDebt (coordinateRoute nsUniformDyadicHOneHalfEquivalence) ≡ transcriptionDebt
nsDyadicEquivalenceIsAlignmentDebt = refl

nsR406EstimateRemainsMathematical :
  routedDebt (coordinateRoute nsLiteralR406SignedCrossEstimate) ≡ mathematicalDebt
nsR406EstimateRemainsMathematical = refl

ymOSReconstructionIsAlignmentDebt :
  routedDebt (coordinateRoute ymStandardOSReconstruction) ≡ transcriptionDebt
ymOSReconstructionIsAlignmentDebt = refl

ymClusteringRemainsMathematical :
  routedDebt (coordinateRoute ymContinuumClustering) ≡ mathematicalDebt
ymClusteringRemainsMathematical = refl

exactHeadValidationIsCertificationDebt :
  routedDebt (coordinateRoute exactHeadAgdaValidation) ≡ certificationDebt
exactHeadValidationIsCertificationDebt = refl
