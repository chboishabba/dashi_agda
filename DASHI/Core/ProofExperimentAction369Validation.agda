module DASHI.Core.ProofExperimentAction369Validation where

open import DASHI.Core.Prelude

import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Core.ProofExperimentAction369IntegrationExact as Integration
import DASHI.Moonshine.Base369OODAProofExperimentObserverExact as O369
import DASHI.Moonshine.Monster196830RegularBulkResidualControlPatternExact as Bulk

------------------------------------------------------------------------
-- Regression witnesses for the integrated control tranche.
------------------------------------------------------------------------

proofSearchDoesNotBecomePhysicalExecution :
  Loop.proofSearchIsPhysicalExecution Loop.canonicalProofExperimentActionLoopBoundary
  ≡ false
proofSearchDoesNotBecomePhysicalExecution =
  Loop.proofSearchIsPhysicalExecutionIsFalse
    Loop.canonicalProofExperimentActionLoopBoundary

observationDoesNotAuthoriseAction :
  Loop.observationAutomaticallyAuthorisesAction
    Loop.canonicalProofExperimentActionLoopBoundary
  ≡ false
observationDoesNotAuthoriseAction =
  Loop.observationAutomaticallyAuthorisesActionIsFalse
    Loop.canonicalProofExperimentActionLoopBoundary

consumerClosureNeedNotIdentifyWholeHypothesis :
  Loop.consumerClosureRequiresFullHypothesisIdentity
    Loop.canonicalProofExperimentActionLoopBoundary
  ≡ false
consumerClosureNeedNotIdentifyWholeHypothesis =
  Loop.consumerClosureRequiresFullHypothesisIdentityIsFalse
    Loop.canonicalProofExperimentActionLoopBoundary

observeMapsToObservedRole :
  O369.phaseRole Loop.observePhase ≡ O369.observedRole
observeMapsToObservedRole = refl

actMapsToExecutedRole :
  O369.phaseRole Loop.actPhase ≡ O369.executedRole
actMapsToExecutedRole = refl

sectorCannotAuthorisePhysicalAction :
  O369.phaseSectorAuthorisesPhysicalAction O369.canonicalBase369OODAObserverBoundary
  ≡ false
sectorCannotAuthorisePhysicalAction =
  O369.phaseSectorAuthorisesPhysicalActionIsFalse
    O369.canonicalBase369OODAObserverBoundary

regularBulkIs196830 : Bulk.regularBulkDimension ≡ 196830
regularBulkIs196830 = Bulk.regularBulkDimensionIs196830

fullReferenceIs196883 : Bulk.fullReferenceDimension ≡ 196883
fullReferenceIs196883 = Bulk.fullReferenceDimensionIs196883

bulkPlusResidualReferenceExact :
  Bulk.regularBulkDimension + Bulk.reducedResidualDimension
  ≡ Bulk.fullReferenceDimension
bulkPlusResidualReferenceExact = Bulk.regularPlusResidualIsFullReference

arithmeticDoesNotDetermineRuntimeCardinality :
  Integration.bulkResidualArithmeticDeterminesRuntimeCardinality
    Integration.canonicalIntegratedCyberneticBoundary
  ≡ false
arithmeticDoesNotDetermineRuntimeCardinality =
  Integration.bulkResidualArithmeticDeterminesRuntimeCardinalityIsFalse
    Integration.canonicalIntegratedCyberneticBoundary

physicalSuccessDoesNotPromoteLongHorizonBenefit :
  Integration.physicalSuccessImpliesLongHorizonBenefit
    Integration.canonicalIntegratedCyberneticBoundary
  ≡ false
physicalSuccessDoesNotPromoteLongHorizonBenefit =
  Integration.physicalSuccessImpliesLongHorizonBenefitIsFalse
    Integration.canonicalIntegratedCyberneticBoundary
