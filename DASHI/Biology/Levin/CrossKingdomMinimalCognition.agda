module DASHI.Biology.Levin.CrossKingdomMinimalCognition where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.FungalCollectiveIntelligenceCore as Fungal
import DASHI.Biology.Levin.PhysarumMechanochemicalDecisionBoundary as Physarum
import DASHI.Biology.Levin.ColonyCollectiveDecisionBoundary as Colony
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.DurableIntegratedState as Durable
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy

record MinimalCognitionProfile : Set where
  field
    sensingSpecified : Bool
    stateValuationSpecified : Bool
    memoryOrHistoryDependenceSpecified : Bool
    actionSetSpecified : Bool
    actionSelectionMeasured : Bool
    perturbationRecoveryMeasured : Bool
    transferAcrossContextsMeasured : Bool
    energeticCostMeasured : Bool
    scaleSpecified : Bool
    problemSpaceSpecified : Bool

record CrossKingdomMinimalCognitionBoundary : Set where
  field
    fungalCore : Fungal.FungalCollectiveIntelligenceCore
    physarumBoundary : Physarum.PhysarumMechanochemicalDecisionBoundary
    colonyBoundary : Colony.ColonyCollectiveDecisionBoundary
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    durableStateBoundary : Durable.DurableIntegratedStateBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    nervousSystemNotRequiredByDefinition : Bool
    adaptiveResponseNotCognitionByDefinition : Bool
    memoryActionAndValuationSeparated : Bool
    commonCriteriaDoNotEraseSubstrateDifferences : Bool
    competenceComparedWithinTaskFamilies : Bool
    crossKingdomRankingNotSingleScalar : Bool
    minimalCognitionNotConsciousness : Bool
    interpretation : String

canonicalCrossKingdomMinimalCognitionBoundary : CrossKingdomMinimalCognitionBoundary
canonicalCrossKingdomMinimalCognitionBoundary = record
  { fungalCore = Fungal.canonicalFungalCollectiveIntelligenceCore
  ; physarumBoundary = Physarum.canonicalPhysarumMechanochemicalDecisionBoundary
  ; colonyBoundary = Colony.canonicalColonyCollectiveDecisionBoundary
  ; problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; durableStateBoundary = Durable.canonicalDurableIntegratedStateBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; nervousSystemNotRequiredByDefinition = true
  ; adaptiveResponseNotCognitionByDefinition = true
  ; memoryActionAndValuationSeparated = true
  ; commonCriteriaDoNotEraseSubstrateDifferences = true
  ; competenceComparedWithinTaskFamilies = true
  ; crossKingdomRankingNotSingleScalar = true
  ; minimalCognitionNotConsciousness = true
  ; interpretation = "Fungi, slime moulds and social colonies are compared through explicit sensing, valuation, memory, action selection, recovery, transfer, energetic cost, scale and problem space rather than through possession of neurons or a single intelligence score"
  }
