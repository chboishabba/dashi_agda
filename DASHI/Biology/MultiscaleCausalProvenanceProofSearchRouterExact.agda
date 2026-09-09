module DASHI.Biology.MultiscaleCausalProvenanceProofSearchRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact as Loop
import DASHI.Interop.DialecticalMaterialSourceDiligenceReopeningExact as MaterialSource
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective

------------------------------------------------------------------------
-- MULTISCALE CAUSAL / PROVENANCE ROUTER
--
-- The history-bearing biology cone carries molecular, hereditary,
-- developmental, neural, cognitive, learning, memory/path, environmental and
-- cultural/institutional coordinates.  Co-presence or temporal order between
-- two such coordinates is not a causal theorem.  A cross-level causal claim
-- needs a declared intervention/measurement design or source-backed
-- identification receipt, nuisance/confounder treatment, provenance, and
-- (when used to repair a formal consumer) binding to the same live residual.
------------------------------------------------------------------------

data BiologicalCausalLevel : Set where
  molecularLevel : BiologicalCausalLevel
  hereditaryLevel : BiologicalCausalLevel
  developmentalLevel : BiologicalCausalLevel
  neuralLevel : BiologicalCausalLevel
  thoughtContentLevel : BiologicalCausalLevel
  learningLevel : BiologicalCausalLevel
  memoryPathLevel : BiologicalCausalLevel
  environmentalLevel : BiologicalCausalLevel
  culturalInstitutionalLevel : BiologicalCausalLevel

record CrossLevelCausalClaim (Value : Set) : Set where
  constructor cross-level-causal-claim
  field
    sourceLevel targetLevel : BiologicalCausalLevel
    sourceValue targetValue : Value
    claimReference : String
    sourceProvenanceReference : String
    targetProvenanceReference : String

open CrossLevelCausalClaim public

data CausalTargetRole : Experiment.CoordinateRole → Set where
  measuredTarget : CausalTargetRole Experiment.measuredObservable
  derivedTarget : CausalTargetRole Experiment.derivedDiscriminator

record CrossLevelCausalDesign
    {Value : Set}
    (claim : CrossLevelCausalClaim Value) : Set₁ where
  constructor cross-level-causal-design
  field
    World Control Dimension : Set
    design : Experiment.ExperimentalCoordinateDesign World Control Value Dimension
    sourceCoordinate targetCoordinate : Experiment.Coordinate design
    sourceIsControlled :
      Experiment.role design sourceCoordinate ≡ Experiment.controlledInput
    targetRole : CausalTargetRole (Experiment.role design targetCoordinate)
    baselineWorld : World
    intervention : Control
    sourceBefore :
      Experiment.read design sourceCoordinate baselineWorld ≡ sourceValue claim
    sourceAfter :
      Experiment.read design sourceCoordinate
        (Experiment.applyControl design intervention baselineWorld)
      ≡ sourceValue claim → ⊥
    targetAfter :
      Experiment.read design targetCoordinate
        (Experiment.applyControl design intervention baselineWorld)
      ≡ targetValue claim
    Confounder : Set
    nuisanceCoordinate : Confounder → Experiment.Coordinate design
    nuisanceIsTyped :
      (c : Confounder) →
      Experiment.role design (nuisanceCoordinate c)
      ≡ Experiment.nuisanceCoordinate
    IdentificationAssumption : Set
    identificationReceipt : IdentificationAssumption
    interventionReference nuisanceReference identificationReference measurementReference : String

open CrossLevelCausalDesign public

record CrossLevelCausalAttribution
    {Value : Set}
    (claim : CrossLevelCausalClaim Value)
    (causalDesign : CrossLevelCausalDesign claim) : Set₁ where
  constructor cross-level-causal-attribution
  field
    CausalEffect : CrossLevelCausalClaim Value → Set
    effectWitness : CausalEffect claim
    chronologyReference lineageOrSubjectReference attributionReference : String

open CrossLevelCausalAttribution public

record CausalExperimentProofSearchBinding
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer)
    {Value : Set}
    {claim : CrossLevelCausalClaim Value}
    {causalDesign : CrossLevelCausalDesign claim}
    (attribution : CrossLevelCausalAttribution claim causalDesign) : Set₂ where
  constructor causal-experiment-proof-search-binding
  field
    experimentBinding : Introspective.ConsumerDefectExperimentBinding liveResidual
    causalExperimentIsScheduledExperiment :
      interventionReference causalDesign
      ≡ Loop.experimentReference (Introspective.demand experimentBinding)
    consumerUseReference : String

open CausalExperimentProofSearchBinding public

causalExperimentPaysLiveResidual :
  ∀ {system schedule consumer liveResidual Value claim causalDesign attribution} →
  (binding :
    CausalExperimentProofSearchBinding
      {system} {schedule} {consumer} liveResidual
      {Value} {claim} {causalDesign} attribution) →
  Loop.residual (Introspective.demand (experimentBinding binding)) ≡ liveResidual
causalExperimentPaysLiveResidual binding =
  Introspective.demandResidualMatchesLiveResidual (experimentBinding binding)

record CausalSourceProofSearchBinding
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (alignment : Introspective.SourceRouteAlignment schedule)
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer)
    {Value : Set}
    (claim : CrossLevelCausalClaim Value) : Set₁ where
  constructor causal-source-proof-search-binding
  field
    sourceDemand : Introspective.ConsumerDefectSourceDemand alignment liveResidual
    SourceSupportsClaim : CrossLevelCausalClaim Value → Set
    sourceSupport : SourceSupportsClaim claim
    sourceIdentificationReference consumerUseReference : String

open CausalSourceProofSearchBinding public

causalSourcePaysScheduledGap :
  ∀ {system schedule consumer alignment liveResidual Value claim} →
  (binding :
    CausalSourceProofSearchBinding
      {system} {schedule} {consumer}
      alignment liveResidual {Value} claim) →
  MaterialSource.firstMissingSourceCoordinate
    (Introspective.reopening (sourceDemand binding))
  ≡
  Introspective.sourceGapFor alignment
    (Scheduler.missingCoordinate liveResidual)
causalSourcePaysScheduledGap binding =
  Introspective.sourceRoutePaysScheduledGap (sourceDemand binding)

record CausalAttributionToConsumerClosure
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer)
    {Value : Set}
    {claim : CrossLevelCausalClaim Value}
    {causalDesign : CrossLevelCausalDesign claim}
    {attribution : CrossLevelCausalAttribution claim causalDesign}
    (binding : CausalExperimentProofSearchBinding liveResidual attribution) : Set₂ where
  constructor causal-attribution-to-consumer-closure
  field
    refinedReceipt : Fibre.ConsumerRefinementReceipt system consumer
    refinementReference : String

open CausalAttributionToConsumerClosure public

data CorrelationMeansCausationPermission : Set where

data TemporalOrderMeansCausationPermission : Set where

data DNAConsumerDifferenceMeansMemoryCausePermission : Set where

data TraumaHistoryMeansNeuralCausePermission : Set where

data LearningMeansHeritableChangePermission : Set where

data CulturalPatternMeansBiologicalEssencePermission : Set where

data CausalAttributionAutomaticallyClosesConsumerPermission : Set where

data ExperimentAdmissionCreatesInterventionAuthorityPermission : Set where

data SourceAcquisitionAutomaticallyProvesCausationPermission : Set where

correlationDoesNotByItselfIdentifyCause : CorrelationMeansCausationPermission → ⊥
correlationDoesNotByItselfIdentifyCause ()
temporalOrderDoesNotByItselfIdentifyCause : TemporalOrderMeansCausationPermission → ⊥
temporalOrderDoesNotByItselfIdentifyCause ()
dnaDifferenceDoesNotByItselfCauseMemoryDifference : DNAConsumerDifferenceMeansMemoryCausePermission → ⊥
dnaDifferenceDoesNotByItselfCauseMemoryDifference ()
traumaHistoryDoesNotByItselfIdentifyNeuralCause : TraumaHistoryMeansNeuralCausePermission → ⊥
traumaHistoryDoesNotByItselfIdentifyNeuralCause ()
learningDoesNotByItselfIdentifyHeritableChange : LearningMeansHeritableChangePermission → ⊥
learningDoesNotByItselfIdentifyHeritableChange ()
culturalPatternDoesNotBecomeBiologicalEssence : CulturalPatternMeansBiologicalEssencePermission → ⊥
culturalPatternDoesNotBecomeBiologicalEssence ()
causalAttributionDoesNotAutomaticallyCloseConsumer : CausalAttributionAutomaticallyClosesConsumerPermission → ⊥
causalAttributionDoesNotAutomaticallyCloseConsumer ()
experimentAdmissionDoesNotCreateInterventionAuthority : ExperimentAdmissionCreatesInterventionAuthorityPermission → ⊥
experimentAdmissionDoesNotCreateInterventionAuthority ()
sourceAcquisitionDoesNotAutomaticallyProveCausation : SourceAcquisitionAutomaticallyProvesCausationPermission → ⊥
sourceAcquisitionDoesNotAutomaticallyProveCausation ()

record MultiscaleCausalProvenanceBoundary : Set where
  constructor multiscale-causal-provenance-boundary
  field
    crossLevelClaimMustNameSourceAndTargetLevels : Bool
    causalExperimentRequiresControlledSourceCoordinate : Bool
    targetMustBeMeasuredOrDerived : Bool
    nuisanceCoordinatesRemainExplicit : Bool
    causalIdentificationRequiresApplicationReceipt : Bool
    proofSearchMustBindSameLiveResidual : Bool
    sourceAndExperimentRoutesRemainDistinct : Bool
    causalAttributionAutomaticallyClosesConsumer : Bool
    correlationAutomaticallyMeansCausation : Bool
    sourceAcquisitionAutomaticallyProvesCausation : Bool
    culturalPatternAutomaticallyBecomesBiologicalEssence : Bool

canonicalMultiscaleCausalProvenanceBoundary : MultiscaleCausalProvenanceBoundary
canonicalMultiscaleCausalProvenanceBoundary =
  multiscale-causal-provenance-boundary
    true true true true true true true false false false false
