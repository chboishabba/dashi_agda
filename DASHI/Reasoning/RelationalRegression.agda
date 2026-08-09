module DASHI.Reasoning.RelationalRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_)

import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as TraumaPNF
import DASHI.Reasoning.RelationalStateCore as Core
import DASHI.Reasoning.RelationalSharedStateUpdate as Shared
import DASHI.Reasoning.ConditionalResponseTree as Response
import DASHI.Reasoning.DefensiveReversalRepair as Repair
import DASHI.Reasoning.IntergenerationalNameIntrusion as Slip
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference
import DASHI.Reasoning.RelationalProcessMemoryHyperfabric as Process
import DASHI.Reasoning.DevelopmentalAttunementPNFBridge as Developmental
import DASHI.Reasoning.DevelopmentalExplanationWithdrawalExact as DevelopmentalPolicy
import DASHI.Reasoning.RelationalFormalismSourceAtlas as Sources

parent : Core.Participant
parent = Core.participant "parent" Core.parentRole

child : Core.Participant
child = Core.participant "child" Core.childRole

siblingTemplate : Core.Participant
siblingTemplate = Core.participant "historical sibling" Core.siblingRole

boundedHelpNode : Response.PropositionNode
boundedHelpNode = Response.propositionNode
  "bounded-help"
  (Response.urgentContext
    ∷ Response.sufficientCapacity
    ∷ Response.boundedInstance
    ∷ [])
  Response.help
  Response.considerModality
  "current episode"
  "one bounded instance"
  []
  ("final commitment unresolved" ∷ [])
  "root"

boundedHelpDecision : Response.DecisionToken
boundedHelpDecision = Response.decisionToken
  "decision-0"
  (Response.urgentContext ∷ Response.sufficientCapacity ∷ [])
  ("help" ∷ "decline" ∷ "defer" ∷ [])
  "t0"
  "td"
  zero

openConsiderResponse : Response.ActualResponse
openConsiderResponse = Response.actualResponse
  child
  boundedHelpNode
  boundedHelpDecision
  "t0"
  Core.affirmStance
  Core.openZero
  Core.consideringOption
  Core.noPreference
  Core.noObligation
  (Core.capacityState 2 1 "capacity currently sufficient")
  true
  true
  true
  "explicit assent only to considering the bounded node"

correctedFamilyNameSlip : Slip.CorrectedNameIntrusion
correctedFamilyNameSlip = Slip.correctedNameIntrusion
  parent
  child
  siblingTemplate
  (Slip.nameCandidate "child name" Core.childRole 3 2 1)
  (Slip.nameCandidate "sibling name" Core.siblingRole 2 3 1)
  "si-"
  "child name"
  Slip.articulation
  Slip.familyAssociationIntrusion
  true
  true
  true
  false
  "partial competing name followed by immediate correction"

validatedFamilyNameSlip :
  Slip.ValidatedCorrectedNameIntrusion correctedFamilyNameSlip
validatedFamilyNameSlip = Slip.validatedCorrectedNameIntrusion
  refl
  refl
  (λ ())
  (λ ())
  (λ ())
  refl
  refl
  "immediate correction, non-composite use and distinct typed roles proved"

slipIsNotCompositeLabel :
  Slip.deliberateCompositeLabelUsed correctedFamilyNameSlip ≡ false
slipIsNotCompositeLabel =
  Slip.nonCompositeProof validatedFamilyNameSlip

slipIsImmediatelyCorrected :
  Slip.immediatelySelfCorrected correctedFamilyNameSlip ≡ true
slipIsImmediatelyCorrected =
  Slip.immediateCorrectionProof validatedFamilyNameSlip

considerNodeIsNotCommitNode :
  Response.modality boundedHelpNode ≡ Response.considerModality
considerNodeIsNotCommitNode = refl

sourceCountRegression :
  Sources.canonicalRelationalSourceCount ≡ 15
sourceCountRegression = refl

processBoundaryRejectsMoreIsAlwaysBetter :
  Process.moreBranchesAlwaysImproveOutcome
    Process.canonicalProcessMemoryAuthorityBoundary
  ≡ false
processBoundaryRejectsMoreIsAlwaysBetter = refl

processBoundaryRequiresQuantitativeReceipt :
  Process.quantitativePromotionRequiresReceipt
    Process.canonicalProcessMemoryAuthorityBoundary
  ≡ true
processBoundaryRequiresQuantitativeReceipt = refl

processBoundaryRejectsForeignMetricsOrWaves :
  Process.quantitativeFamilyAllowsForeignMetricsOrWaves
    Process.canonicalProcessMemoryAuthorityBoundary
  ≡ false
processBoundaryRejectsForeignMetricsOrWaves = refl

processBoundaryRejectsUniversalIncidence :
  Process.arbitraryParticipantIncidentToEveryBranch
    Process.canonicalProcessMemoryAuthorityBoundary
  ≡ false
processBoundaryRejectsUniversalIncidence = refl

repairPreservesBothQuestions :
  Repair.preserveBothQuestions Repair.canonicalRepairSequence ≡ true
repairPreservesBothQuestions = refl

sharedStateRequiresAllegationParticulars :
  Shared.allegationsRequireParticulars Shared.canonicalSharedStateInvariants ≡ true
sharedStateRequiresAllegationParticulars = refl

sharedStateRequiresTransitionForUptake :
  Shared.uptakeRequiresContributionTransition
    Shared.canonicalSharedStateInvariants
  ≡ true
sharedStateRequiresTransitionForUptake = refl

------------------------------------------------------------------------
-- Exact developmental-attunement regressions.
------------------------------------------------------------------------

developmentalAttentionQuantityAgrees :
  Developmental.attentionMass Developmental.stableTrace
  ≡ Developmental.attentionMass Developmental.fragmentedTrace
developmentalAttentionQuantityAgrees =
  Developmental.sameAttention
    Developmental.canonicalFragmentationWitness

developmentalUptakeQuantityAgrees :
  Developmental.uptakeMass Developmental.stableTrace
  ≡ Developmental.uptakeMass Developmental.fragmentedTrace
developmentalUptakeQuantityAgrees =
  Developmental.sameUptakeQuantity
    Developmental.canonicalFragmentationWitness

developmentalFragmentedTraceHasTwoAdditionalSwitches :
  Developmental.switchCount Developmental.fragmentedTrace
  ≡ suc (suc (Developmental.switchCount Developmental.stableTrace))
developmentalFragmentedTraceHasTwoAdditionalSwitches =
  Developmental.twoAdditionalSwitches
    Developmental.canonicalFragmentationWitness

developmentalFragmentedTraceHasTwoAdditionalBurdenUnits :
  Developmental.traceTotalBurden Developmental.fragmentedTrace
  ≡ suc (suc (Developmental.traceTotalBurden Developmental.stableTrace))
developmentalFragmentedTraceHasTwoAdditionalBurdenUnits =
  Developmental.twoAdditionalTotalBurden
    Developmental.canonicalFragmentationWitness

developmentalTraumaPNFReuseIsCanonical :
  Developmental.traumaMemoryHypervoxelBoundary
    Developmental.canonicalExistingTraumaPNFHyperformalismReuse
  ≡ TraumaPNF.canonicalTraumaMemoryHypervoxelAuthorityBoundary
developmentalTraumaPNFReuseIsCanonical =
  Developmental.traumaMemoryHypervoxelBoundaryIsCanonical
    Developmental.canonicalExistingTraumaPNFHyperformalismReuse

developmentalFiniteTraceDoesNotDiagnose :
  Developmental.oneFiniteTraceEstablishesStableCharacter
    Developmental.canonicalDevelopmentalAttunementAuthorityBoundary
  ≡ false
developmentalFiniteTraceDoesNotDiagnose = refl

------------------------------------------------------------------------
-- Explanation and withdrawal regressions.
------------------------------------------------------------------------

explanationCannotConstructImpactErasure :
  DevelopmentalPolicy.ExplanationErasesImpact → ⊥
explanationCannotConstructImpactErasure =
  DevelopmentalPolicy.explanationErasesImpactImpossible

explanationCannotConstructRepairErasure :
  DevelopmentalPolicy.ExplanationErasesRepair → ⊥
explanationCannotConstructRepairErasure =
  DevelopmentalPolicy.explanationErasesRepairImpossible

attunedContinuationPreferredRegression :
  Selection.StrictlyPreferred
    DevelopmentalPolicy.attunedContinuePortfolio
    DevelopmentalPolicy.protectiveWithdrawalPortfolio
attunedContinuationPreferredRegression =
  DevelopmentalPolicy.attunedContinuationBeatsWithdrawal

protectiveWithdrawalPreferredUnderRepeatedDisplacementRegression :
  Selection.StrictlyPreferred
    DevelopmentalPolicy.protectiveWithdrawalPortfolio
    DevelopmentalPolicy.repeatedDisplacementContinuePortfolio
protectiveWithdrawalPreferredUnderRepeatedDisplacementRegression =
  DevelopmentalPolicy.withdrawalBeatsRepeatedDisplacementContinuation

withdrawalIsNotGloballyPromoted :
  DevelopmentalPolicy.withdrawalIsAlwaysOptimal
    DevelopmentalPolicy.canonicalExplanationWithdrawalAuthorityBoundary
  ≡ false
withdrawalIsNotGloballyPromoted = refl

------------------------------------------------------------------------
-- Exact attractor-selection regressions.
------------------------------------------------------------------------

constructivePortfolioBeatsNoise :
  Selection.StrictlyPreferred
    Selection.constructivePortfolio
    Selection.noisePortfolio
constructivePortfolioBeatsNoise = Selection.constructiveBeatsNoise

singleAlignedBeatsDestructivePair :
  Selection.StrictlyPreferred
    Selection.portfolioA
    Selection.destructivePortfolio
singleAlignedBeatsDestructivePair = Selection.aBeatsDestructivePair

explorationCanBeatNoBranch :
  Selection.StrictlyPreferred
    Selection.explorationPortfolio
    Selection.emptyPortfolio
explorationCanBeatNoBranch = Selection.explorationBeatsEmpty

optionNoiseNominalRegression :
  Selection.nominalOptionCount Selection.optionNoisePortfolio ≡ 3
optionNoiseNominalRegression = refl

optionNoiseEffectiveRegression :
  Selection.effectiveOptionCount Selection.optionNoisePortfolio ≡ 1
optionNoiseEffectiveRegression = refl

trapUtilityDoesNotImplyAttractorAlignment :
  Selection.driftDirection
    (Selection.expectedDrift Selection.trapBranch)
  ≡ Selection.awayFromAttractor
trapUtilityDoesNotImplyAttractorAlignment = refl

validatedPortfolioPairsExcludeDiagonalAndDuplicates :
  Selection.arbitraryOrDuplicatePairEntriesAffectValue
    Selection.canonicalAttractorSelectionAuthorityBoundary
  ≡ false
validatedPortfolioPairsExcludeDiagonalAndDuplicates = refl

------------------------------------------------------------------------
-- Exact double-/n-slit regressions.
------------------------------------------------------------------------

doubleInPhaseRegression :
  Interference.coherentIntensity
    (Interference.phase0 ∷ Interference.phase0 ∷ [])
  ≡ + 4
doubleInPhaseRegression = refl

doubleOppositeRegression :
  Interference.coherentIntensity
    (Interference.phase0 ∷ Interference.phase2 ∷ [])
  ≡ + 0
doubleOppositeRegression = refl

threeInPhaseRegression :
  Interference.coherentIntensity
    (Interference.phase0 ∷ Interference.phase0 ∷ Interference.phase0 ∷ [])
  ≡ + 9
threeInPhaseRegression = refl

nSlitPairwiseDecompositionRegression :
  (waves : List Interference.BranchWave) →
  Interference.coherentIntensity waves
  ≡
  Interference.diagonalIntensity waves
  +ℤ
  Interference.allPairwiseInterference waves
nSlitPairwiseDecompositionRegression =
  Interference.exactNSlitLaw

thirdOrderResidualRegression :
  (left middle right : Interference.BranchWave) →
  Interference.thirdOrderResidual left middle right ≡ + 0
thirdOrderResidualRegression =
  Interference.thirdOrderResidualZero

waveBridgeClassifiesInPhaseAsReinforcing :
  Selection.interactionDirection
    (Interference.optimizerInteraction
      Interference.inPhaseInteractionCertificate)
  ≡ Selection.reinforcing
waveBridgeClassifiesInPhaseAsReinforcing = refl

waveBridgeClassifiesOppositionAsInterfering :
  Selection.interactionDirection
    (Interference.optimizerInteraction
      Interference.oppositeInteractionCertificate)
  ≡ Selection.interfering
waveBridgeClassifiesOppositionAsInterfering = refl

waveBridgeClassifiesQuadratureAsIndependent :
  Selection.interactionDirection
    (Interference.optimizerInteraction
      Interference.quadratureInteractionCertificate)
  ≡ Selection.independent
waveBridgeClassifiesQuadratureAsIndependent = refl
