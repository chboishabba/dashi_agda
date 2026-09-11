module DASHI.Reasoning.FibreRoutingCompressionLadderExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.FibreRoutingDistillationCompressionCrossPollinationExact as Distill
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerRelativeMinimalFidelityExact as Minimal
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.ExpectedFibreReductionCostExact as ReductionCost
import DASHI.Core.NDimParetoHyperfabricExact as NDim

------------------------------------------------------------------------
-- CONSUMER-RELATIVE FIBRE COMPRESSION LADDER
--
-- This owner turns distillation / pruning / quantization / low-rank / expert
-- merging / sparse routing into candidate compression moves over one declared
-- consumer problem. A step is not accepted because it is smaller. It is
-- accepted only inside the admissible + consumer-adequate stratum.
------------------------------------------------------------------------

data CompressionStage : Set where
  fullTeacherStage : CompressionStage
  distilledStudentStage : CompressionStage
  distilledPlusRelationStage : CompressionStage

stageReference : CompressionStage → String
stageReference fullTeacherStage = "full teacher / source carrier"
stageReference distilledStudentStage = "distilled student carrier"
stageReference distilledPlusRelationStage = "distilled student + missing relation fibre"

stageDescriptionLength : CompressionStage → Nat
stageDescriptionLength fullTeacherStage = 3
stageDescriptionLength distilledStudentStage = 1
stageDescriptionLength distilledPlusRelationStage = 2

stageAdmissible : CompressionStage → Set
stageAdmissible stage = ⊤

identityTeacherProjection : Distill.TeacherState → Distill.TeacherState
identityTeacherProjection state = state

fullTeacherAdequateForRichRelation :
  Query.AdequateFor
    identityTeacherProjection
    Distill.distillationSemantics
    Distill.richRelationQuery
fullTeacherAdequateForRichRelation =
  Query.factorsForQuery
    (λ state → Distill.richAnswer (Distill.richTeacherConsumer state))
    (λ state → refl)

stageRichAdequate : CompressionStage → Set₁
stageRichAdequate fullTeacherStage =
  Query.AdequateFor
    identityTeacherProjection
    Distill.distillationSemantics
    Distill.richRelationQuery
stageRichAdequate distilledStudentStage =
  Query.AdequateFor
    Distill.studentProjection
    Distill.distillationSemantics
    Distill.richRelationQuery
stageRichAdequate distilledPlusRelationStage =
  Query.AdequateFor
    Distill.studentPlusRichFibre
    Distill.distillationSemantics
    Distill.richRelationQuery

data StageRefines : CompressionStage → CompressionStage → Set where
  teacherReflexive : StageRefines fullTeacherStage fullTeacherStage
  studentReflexive : StageRefines distilledStudentStage distilledStudentStage
  repairedReflexive : StageRefines distilledPlusRelationStage distilledPlusRelationStage
  studentToRepaired : StageRefines distilledStudentStage distilledPlusRelationStage

richCompressionProblem : MDL.ConsumerMDLProblem
richCompressionProblem =
  MDL.consumerMDLProblem
    CompressionStage
    stageAdmissible
    stageRichAdequate
    stageDescriptionLength
    StageRefines
    stageReference
    "finite illustrative stage code length; compression is ranked only after adequacy"
    "rich teacher relation consumer"

fullTeacherEligible : MDL.Eligible richCompressionProblem fullTeacherStage
fullTeacherEligible = tt , fullTeacherAdequateForRichRelation

repairedStudentEligible :
  MDL.Eligible richCompressionProblem distilledPlusRelationStage
repairedStudentEligible =
  tt , Distill.joinedStudentAdequateForRichRelation

distilledStudentNotEligibleForRichConsumer :
  MDL.Eligible richCompressionProblem distilledStudentStage → ⊥
distilledStudentNotEligibleForRichConsumer eligible =
  Distill.studentCannotAnswerRichRelationQuery (proj₂ eligible)

-- ConsumerCounterexample's witness universe is Set, so retain the rich query
-- defect as the insufficiency theorem and use a small first-order token as the
-- counterexample carrier rather than trying to store the Set₁ defect itself.
data StudentRichFailureWitness : Set where
  studentRichFailureWitness : StudentRichFailureWitness

studentRichCounterexample :
  MDL.ConsumerCounterexample richCompressionProblem distilledStudentStage
studentRichCounterexample =
  MDL.consumerCounterexample
    StudentRichFailureWitness
    studentRichFailureWitness
    Distill.studentCannotAnswerRichRelationQuery
    "teacherStateA and teacherStateB collapse to the same distilled state"
    "the rich relation consumer distinguishes the collapsed teacher states; exact defect retained in Distill.studentRichRelationDefect"

studentRelationRepair :
  MDL.LocalRefinementRepair
    richCompressionProblem
    distilledStudentStage
    distilledPlusRelationStage
studentRelationRepair =
  MDL.localRefinementRepair
    studentRichCounterexample
    studentToRepaired
    tt
    Distill.joinedStudentAdequateForRichRelation
    "reattach only the missing teacher-relation fibre and re-test the declared consumer"

repairRestoresEligibility :
  MDL.Eligible richCompressionProblem distilledPlusRelationStage
repairRestoresEligibility = MDL.repairProvidesEligibleRefinement studentRelationRepair

------------------------------------------------------------------------
-- Compression technique transition surface.
------------------------------------------------------------------------

record CompressionTransition (from to : CompressionStage) : Set where
  constructor compressionTransition
  field
    technique : Distill.CompressionTechnique
    declaredRefinement : StageRefines from to
    consumerAdequacyRecheckRequired : Bool
    transitionReference : String

open CompressionTransition public

studentRepairTransition :
  CompressionTransition distilledStudentStage distilledPlusRelationStage
studentRepairTransition =
  compressionTransition
    Distill.adapterBottleneck
    studentToRepaired
    true
    "local missing-fibre repair; not a claim that adapters are uniquely optimal"

------------------------------------------------------------------------
-- Multi-axis deployment cost surface.
------------------------------------------------------------------------

data CompressionCostAxis : Set where
  descriptionAxis : CompressionCostAxis
  activeFibreAxis : CompressionCostAxis
  deploymentAxis : CompressionCostAxis
  precisionAxis : CompressionCostAxis

compressionCost : CompressionCostAxis → CompressionStage → Nat
compressionCost descriptionAxis fullTeacherStage = 3
compressionCost descriptionAxis distilledStudentStage = 1
compressionCost descriptionAxis distilledPlusRelationStage = 2
compressionCost activeFibreAxis fullTeacherStage = 3
compressionCost activeFibreAxis distilledStudentStage = 1
compressionCost activeFibreAxis distilledPlusRelationStage = 2
compressionCost deploymentAxis fullTeacherStage = 3
compressionCost deploymentAxis distilledStudentStage = 1
compressionCost deploymentAxis distilledPlusRelationStage = 2
compressionCost precisionAxis fullTeacherStage = 2
compressionCost precisionAxis distilledStudentStage = 1
compressionCost precisionAxis distilledPlusRelationStage = 1

compressionAxisReference : CompressionCostAxis → String
compressionAxisReference descriptionAxis = "declared representation description length"
compressionAxisReference activeFibreAxis = "active/retained fibre count proxy"
compressionAxisReference deploymentAxis = "deployment resource proxy"
compressionAxisReference precisionAxis = "numeric precision/storage proxy"

compressionCostHyperfabric : MDL.CostHyperfabric richCompressionProblem
compressionCostHyperfabric =
  MDL.costHyperfabric CompressionCostAxis compressionCost compressionAxisReference

compressionParetoView : NDim.NDimParetoView compressionCostHyperfabric
compressionParetoView =
  NDim.ndimParetoView
    4
    "four explicitly declared compression/deployment cost axes"
    compressionAxisReference
    true
    "no scalarized objective required"

------------------------------------------------------------------------
-- Existing repo-native reduction/fidelity anchors.
------------------------------------------------------------------------

minimalFidelityRemainsConsumerRelative :
  Minimal.minimalityIsConsumerAndPortfolioRelative
    Minimal.canonicalMinimalFidelityBoundary ≡ true
minimalFidelityRemainsConsumerRelative = refl

lowestCostDoesNotAutomaticallySuffice :
  Minimal.lowestCostCandidateAutomaticallySufficient
    Minimal.canonicalMinimalFidelityBoundary ≡ false
lowestCostDoesNotAutomaticallySuffice =
  Minimal.lowestCostCandidateAutomaticallySufficientIsFalse
    Minimal.canonicalMinimalFidelityBoundary

approximateCompressionNeedsConsumerMargin :
  Approx.approximateROMNeedsCertifiedConsumerMargin
    Approx.canonicalConsumerApproximateFidelityBoundary ≡ true
approximateCompressionNeedsConsumerMargin =
  Approx.approximateROMNeedsCertifiedConsumerMarginIsTrue
    Approx.canonicalConsumerApproximateFidelityBoundary

approximateSafetyDoesNotIdentifyMechanism :
  Approx.approximateDecisionSafetyImpliesMechanisticRealization
    Approx.canonicalConsumerApproximateFidelityBoundary ≡ false
approximateSafetyDoesNotIdentifyMechanism =
  Approx.approximateDecisionSafetyImpliesMechanisticRealizationIsFalse
    Approx.canonicalConsumerApproximateFidelityBoundary

reductionCostNeedsSeparateAdmissibility :
  ReductionCost.admissibilityMustBeCheckedSeparately
    ReductionCost.canonicalExpectedFibreReductionCostBoundary ≡ true
reductionCostNeedsSeparateAdmissibility =
  ReductionCost.admissibilityMustBeCheckedSeparatelyIsTrue
    ReductionCost.canonicalExpectedFibreReductionCostBoundary

------------------------------------------------------------------------
-- Cross-domain reading for the Fly / MoE / grokking programme.
------------------------------------------------------------------------

data ProgrammeCompressionReading : Set where
  flyCarrierCompression : ProgrammeCompressionReading
  moeExpertCompression : ProgrammeCompressionReading
  grokkingRepresentationCompression : ProgrammeCompressionReading
  distilledDeploymentCompression : ProgrammeCompressionReading

readingReference : ProgrammeCompressionReading → String
readingReference flyCarrierCompression =
  "retain the smallest structural/functional fibre carrier that preserves held-out structure/function consumers"
readingReference moeExpertCompression =
  "prune/merge/sparsify experts only after the routed consumer remains adequate"
readingReference grokkingRepresentationCompression =
  "test whether late generalizing representations become more compressible without losing held-out/future consumers"
readingReference distilledDeploymentCompression =
  "transport only declared teacher consumers into a smaller student; mechanism identity remains separate"

record FibreCompressionLadderBoundary : Set where
  constructor fibreCompressionLadderBoundary
  field
    everyCompressionStepNeedsConsumerRecheck : Bool
    shorterInadequateStageMayBeatEligibleStageByRawCost : Bool
    rawCostMayOverrideConsumerInadequacy : Bool
    localLostFibreMayRepairCompressedCarrier : Bool
    localRepairProvesUniversalSufficiency : Bool
    approximateFidelityMayUseConsumerMargin : Bool
    approximateDecisionSafetyImpliesMechanismIdentity : Bool
    compressionAxesMayRemainParetoRatherThanScalarized : Bool
    grokkingMayBeTestedAsEmergentCompressibility : Bool
    flyCompressionMayBeTestedOnHeldOutCarrier : Bool

canonicalFibreCompressionLadderBoundary : FibreCompressionLadderBoundary
canonicalFibreCompressionLadderBoundary =
  fibreCompressionLadderBoundary
    true
    true
    false
    true
    false
    true
    false
    true
    true
    true
