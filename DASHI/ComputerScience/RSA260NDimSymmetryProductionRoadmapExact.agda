module DASHI.ComputerScience.RSA260NDimSymmetryProductionRoadmapExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production
import DASHI.ComputerScience.RSA260GraphRefinementNDimSymmetryExact as NDimSym
import DASHI.ComputerScience.RSA260SymmetryCensusOrbitQuotientBidiExact as Bidi

------------------------------------------------------------------------
-- CONSOLIDATED RSA-260 ROADMAP AFTER N-DIM / SYMMETRY CROSS-POLLINATION
--
-- NDim is used as a discriminator space before quotienting, not as a claim
-- that higher dimension itself reduces work.  Production bytes remain the
-- first conclusion-paying residual.  Once available, structural refinement is
-- now the first replay-preparation pass before deciding whether full-width CPU
-- execution is necessary.
------------------------------------------------------------------------

productionBoundary : Production.RSA260ProductionSubstitutionBoundary
productionBoundary = Production.currentRSA260ProductionSubstitutionBoundary

ndimBoundary : NDimSym.RSA260NDimRoadmapBoundary
ndimBoundary = NDimSym.currentRSA260NDimRoadmapBoundary

symmetryBoundary : Bidi.RSA260SymmetryExecutionRoadmapBoundary
symmetryBoundary = Bidi.currentRSA260SymmetryExecutionRoadmapBoundary

------------------------------------------------------------------------
-- Ordered execution/acquisition route.
------------------------------------------------------------------------

data ConsolidatedRSA260Residual : Set where
  acquireProductionLAInput : ConsolidatedRSA260Residual
  verifyLosslessArtifactManifest : ConsolidatedRSA260Residual
  refineProductionGraphAcrossDeclaredAxes : ConsolidatedRSA260Residual
  constructAndTestCandidateAutomorphisms : ConsolidatedRSA260Residual
  chooseFullOrQuotientCPUReplay : ConsolidatedRSA260Residual
  verifyLiftedProductionKernel : ConsolidatedRSA260Residual
  reproduceProductionCUDA : ConsolidatedRSA260Residual
  reproduceProductionNCCL : ConsolidatedRSA260Residual
  reproduceRemainingGNFSStages : ConsolidatedRSA260Residual
  closeEndToEndRSA260Reproduction : ConsolidatedRSA260Residual

firstUnpaidConsolidatedResidual : ConsolidatedRSA260Residual
firstUnpaidConsolidatedResidual = acquireProductionLAInput

record ConsolidatedRSA260RoadmapBoundary : Set where
  constructor consolidated-rsa260-roadmap-boundary
  field
    syntheticBlockWiedemannPathComplete : Bool
    syntheticSymmetryNegativeCasePaid : Bool
    syntheticSymmetryPositiveQuotientCasePaid : Bool
    graphDerivedOrbitRefinementPaid : Bool
    ndimStructuralAxisInterpretationPaid : Bool
    productionShapeAnchorsPaid : Bool
    productionBytesPaid : Bool
    productionManifestPaid : Bool
    productionGraphRefinementPaid : Bool
    productionAutomorphismPaid : Bool
    productionQuotientDecisionPaid : Bool
    productionCPUReplayPaid : Bool
    productionLiftVerificationPaid : Bool
    productionCUDAParityPaid : Bool
    productionNCCLParityPaid : Bool
    fullRSA260ReproductionPaid : Bool
open ConsolidatedRSA260RoadmapBoundary public

currentConsolidatedRSA260RoadmapBoundary : ConsolidatedRSA260RoadmapBoundary
currentConsolidatedRSA260RoadmapBoundary =
  consolidated-rsa260-roadmap-boundary
    true true true true true true
    false false false false false false false false false false

------------------------------------------------------------------------
-- Decision rule after production bytes arrive.
--
-- Refinement may return a discrete partition. In that case there is no
-- symmetry reduction to take and the roadmap falls through to full CPU replay.
-- If a candidate action survives exact operator/consumer gates, quotient replay
-- may precede the full-width replay, but the lifted result must still verify
-- upstairs.
------------------------------------------------------------------------

data ReplayRoute : Set where
  fullWidthReplay : ReplayRoute
  symmetryQuotientReplay : ReplayRoute

record ReplayDecisionReceipt : Set where
  constructor replay-decision-receipt
  field
    refinementCompleted : Bool
    nontrivialCandidateFound : Bool
    operatorEquivarianceVerified : Bool
    consumerCovarianceVerified : Bool
    exactLiftAvailable : Bool
    chosenRoute : ReplayRoute
open ReplayDecisionReceipt public

canonicalNoProductionDecisionYet : ReplayDecisionReceipt
canonicalNoProductionDecisionYet =
  replay-decision-receipt false false false false false fullWidthReplay

------------------------------------------------------------------------
-- Roadmap theorem-in-words encoded as firewalls.
------------------------------------------------------------------------

data MoreDimensionsImpliesReduction : Set where
data RefinementImpliesAutomorphism : Set where
data AutomorphismImpliesSpeedup : Set where
data QuotientReplayEliminatesUpstairsCheck : Set where

dimensionAloneDoesNotReduce : MoreDimensionsImpliesReduction → ⊥
dimensionAloneDoesNotReduce ()

refinementDoesNotCreateAutomorphism : RefinementImpliesAutomorphism → ⊥
refinementDoesNotCreateAutomorphism ()

automorphismDoesNotGuaranteeSpeedup : AutomorphismImpliesSpeedup → ⊥
automorphismDoesNotGuaranteeSpeedup ()

quotientStillRequiresUpstairsVerification : QuotientReplayEliminatesUpstairsCheck → ⊥
quotientStillRequiresUpstairsVerification ()
