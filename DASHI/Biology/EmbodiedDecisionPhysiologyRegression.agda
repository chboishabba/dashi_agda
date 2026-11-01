module DASHI.Biology.EmbodiedDecisionPhysiologyRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.EmbodiedInteroceptionSourceRegistry as Sources
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Body
import DASHI.Biology.IntrospectiveEmbodiedHyperformalismObservationExact as Visual
import DASHI.Cognition.PNF.NeuromodulatedCommitmentThresholdExact as Threshold
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence

record EmbodiedDecisionPhysiologyRegression : Set where
  field
    nineCalibratingSources : Sources.canonicalEmbodiedSourceCount ≡ 9

    cortisolCoordinateDoesNotRecoverBody :
      Body.regulatedBody ≡ Body.mobilisedBody → ⊥

    optionConeStrictlyContracts :
      Body.Available Body.contractedCone Body.flexiblePlanning → ⊥

    sameAfferencePriorChangesFeeling :
      Body.inferFeltState Body.safetyPrior Body.arousalAfference
      ≡ Body.inferFeltState Body.threatPrior Body.arousalAfference → ⊥

    threatPriorCanMaintainContractedLoop :
      Body.closedLoop Body.threatPrior Body.contractedCone ≡ Body.contractedCone

    safetyPriorCanReopenSameContractedInput :
      Body.closedLoop Body.safetyPrior Body.contractedCone ≡ Body.reopenedCone

    sameEvidenceThresholdPolicyChangesCommitment :
      Threshold.thresholdUnder Threshold.lowerThreshold Evidence.e1
      ≡ Threshold.thresholdUnder Threshold.elevatedThreshold Evidence.e1 → ⊥

    sameCommitmentDoesNotFixConfidence :
      Confidence.committedLowConfidence ≡ Confidence.committedHighConfidence → ⊥

    cvRecoveredFourSupervoxels : Visual.observedSupervoxelCount ≡ 4
    cvRecoveredNineFibres : Visual.observedTotalFibreCount ≡ 9
    cvRecoveredBroadContractedAsymmetry :
      Visual.observedFibreCount Visual.recoveredS0
      ≡ Visual.observedFibreCount Visual.recoveredS1 → ⊥
    cvReceiptDoesNotPromoteBiologicalMeaning :
      Visual.IntrospectiveObservationBoundary.pixelTopologyDeterminesBiologicalMechanism
        Visual.canonicalIntrospectiveObservationBoundary ≡ false

open EmbodiedDecisionPhysiologyRegression public

canonicalEmbodiedDecisionPhysiologyRegression : EmbodiedDecisionPhysiologyRegression
canonicalEmbodiedDecisionPhysiologyRegression = record
  { nineCalibratingSources = refl
  ; cortisolCoordinateDoesNotRecoverBody = Body.cortisolDoesNotDetermineBodyState
  ; optionConeStrictlyContracts = λ ()
  ; sameAfferencePriorChangesFeeling = Body.sameAfferenceDifferentPriorCanChangeFeeling
  ; threatPriorCanMaintainContractedLoop = Body.threatPriorContractedConeIsSelfMaintainingWitness
  ; safetyPriorCanReopenSameContractedInput = Body.safetyPriorContractedConeCanReopenWitness
  ; sameEvidenceThresholdPolicyChangesCommitment = Threshold.sameEvidenceDifferentThresholdChangesCommitment
  ; sameCommitmentDoesNotFixConfidence = Confidence.commitmentDoesNotDetermineConfidence
  ; cvRecoveredFourSupervoxels = Visual.opencvRecoveredFourSupervoxels
  ; cvRecoveredNineFibres = Visual.opencvRecoveredNineFibres
  ; cvRecoveredBroadContractedAsymmetry = Visual.broadAndContractedOccupancyDiffer
  ; cvReceiptDoesNotPromoteBiologicalMeaning =
      Visual.IntrospectiveObservationBoundary.pixelTopologyDeterminesBiologicalMechanismIsFalse
        Visual.canonicalIntrospectiveObservationBoundary
  }
