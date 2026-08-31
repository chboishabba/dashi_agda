module DASHI.Culture.JohnAnthonyBrownEvidenceMoveConeDynamicsExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: STAGE-QUALIFIED EVIDENCE MOVE CONE
--
-- The adaptive evidence-search stage controls which next moves are admitted.
-- This is the paper/research analogue of the Base369 path-indexed operator cone:
-- a move can become newly useful/admissible after a prior evidence coordinate is
-- provisionally resolved.  The analogy is structural only.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownAdaptiveEvidenceSearchExact as Search

------------------------------------------------------------------------
-- 1. Proof-relevant admission by search stage.
------------------------------------------------------------------------

data EvidenceMoveAdmitted : Search.EvidenceSearchStage → Search.EvidenceMove → Set where
  initialExposure :
    EvidenceMoveAdmitted Search.initialStage
      Search.validateCoerciveExposureInstrument
  initialPopulationRecovery :
    EvidenceMoveAdmitted Search.initialStage
      Search.recoverCatholicPopulationAssociation

  afterExposureOutcomes :
    EvidenceMoveAdmitted Search.exposureMeasureProvisionallyResolved
      Search.validateOutcomeVectorMeasures
  afterExposureConfounding :
    EvidenceMoveAdmitted Search.exposureMeasureProvisionallyResolved
      Search.strengthenConfoundingModel
  afterExposureBetrayal :
    EvidenceMoveAdmitted Search.exposureMeasureProvisionallyResolved
      Search.validateInstitutionalBetrayalMeasure

  afterOutcomesConfounding :
    EvidenceMoveAdmitted Search.outcomeMeasuresProvisionallyResolved
      Search.strengthenConfoundingModel
  afterOutcomesModeration :
    EvidenceMoveAdmitted Search.outcomeMeasuresProvisionallyResolved
      Search.validateModerationMeasures

  afterConfoundingPopulation :
    EvidenceMoveAdmitted Search.confoundingModelProvisionallyResolved
      Search.recoverCatholicPopulationAssociation
  afterConfoundingReplication :
    EvidenceMoveAdmitted Search.confoundingModelProvisionallyResolved
      Search.runTargetPopulationReplication

------------------------------------------------------------------------
-- 2. The canonical next move is admitted at every declared stage.
------------------------------------------------------------------------

canonicalNextMoveAdmitted :
  (stage : Search.EvidenceSearchStage) →
  EvidenceMoveAdmitted stage (Search.nextEvidenceMove stage)
canonicalNextMoveAdmitted Search.initialStage = initialExposure
canonicalNextMoveAdmitted Search.exposureMeasureProvisionallyResolved = afterExposureOutcomes
canonicalNextMoveAdmitted Search.outcomeMeasuresProvisionallyResolved = afterOutcomesConfounding
canonicalNextMoveAdmitted Search.confoundingModelProvisionallyResolved = afterConfoundingPopulation

------------------------------------------------------------------------
-- 3. Stage matters: some moves are not admitted in the initial cone.
------------------------------------------------------------------------

confoundingNotInitial :
  EvidenceMoveAdmitted Search.initialStage Search.strengthenConfoundingModel → ⊥
confoundingNotInitial ()

replicationNotInitial :
  EvidenceMoveAdmitted Search.initialStage Search.runTargetPopulationReplication → ⊥
replicationNotInitial ()

replicationAdmittedLater :
  EvidenceMoveAdmitted Search.confoundingModelProvisionallyResolved
    Search.runTargetPopulationReplication
replicationAdmittedLater = afterConfoundingReplication

------------------------------------------------------------------------
-- 4. Structural analogy boundary to Base369 admissibility dynamics.
------------------------------------------------------------------------

data EvidenceMoveConeIsLiteralBase369OperatorCone : Set where

data EvidenceStageTransitionIsPhysicalHolonomy : Set where

paperEvidenceConeIsNotBase369OperatorCone :
  EvidenceMoveConeIsLiteralBase369OperatorCone → ⊥
paperEvidenceConeIsNotBase369OperatorCone ()

evidenceStageIsNotPhysicalHolonomy :
  EvidenceStageTransitionIsPhysicalHolonomy → ⊥
evidenceStageIsNotPhysicalHolonomy ()

record EvidenceMoveConeDynamicsBoundary : Set where
  constructor evidence-move-cone-dynamics-boundary
  field
    evidenceMoveConeIsStageQualified : Bool
    nextMoveHasAdmissionWitness : Bool
    laterStageMayAdmitPreviouslyUnavailableMove : Bool
    initialRankingIsTimelessGlobalOrder : Bool
    paperEvidenceConeEqualsBase369OperatorCone : Bool
    researchUpdateEqualsPhysicalHolonomy : Bool

canonicalEvidenceMoveConeDynamicsBoundary : EvidenceMoveConeDynamicsBoundary
canonicalEvidenceMoveConeDynamicsBoundary =
  evidence-move-cone-dynamics-boundary true true true false false false
