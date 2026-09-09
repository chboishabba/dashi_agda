module DASHI.Biology.MultiscaleCausalProvenanceProofSearchRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact as Loop
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective

------------------------------------------------------------------------
-- MULTISCALE CAUSAL / PROVENANCE ROUTER
--
-- The history-bearing biology cone carries molecular, hereditary,
-- developmental, neural, cognitive, learning, memory/path, environmental and
-- cultural/institutional coordinates.  Co-presence or temporal order between
-- two such coordinates is not a causal theorem.  A cross-level causal claim
-- needs a declared intervention/measurement design, nuisance/confounder
-- treatment, an application-supplied identification receipt, provenance, and
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

------------------------------------------------------------------------
-- A target coordinate may be directly measured or a provenance-bearing
-- derived discriminator.  No other role is silently promoted to outcome.
------------------------------------------------------------------------

data CausalTargetRole : Experiment.CoordinateRole → Set where
  measuredTarget : CausalTargetRole Experiment.measuredObservable
  derivedTarget : CausalTargetRole Experiment.derivedDiscriminator

------------------------------------------------------------------------
-- Experimental design for one causal attribution.
--
-- `IdentificationAssumption` is intentionally application supplied.  This
-- module does not pretend that source manipulation plus outcome change alone
-- proves an identified causal effect; randomisation, adjustment, exclusion,
-- mechanistic identification, natural-experiment assumptions, etc. belong in
-- the concrete application receipt.
------------------------------------------------------------------------

record CrossLevelCausalDesign
    {Value : Set}
    (claim : CrossLevelCausalClaim Value) : Set₁ where
  constructor cross-level-causal-design
  field
    World Control Dimension : Set

    design :
      Experiment.ExperimentalCoordinateDesign World Control Value Dimension

    sourceCoordinate targetCoordinate : Experiment.Coordinate design

    sourceIsControlled :
      Experiment.role design sourceCoordinate ≡ Experiment.controlledInput

    targetRole :
      CausalTargetRole (Experiment.role design targetCoordinate)

    baselineWorld : World
    intervention : Control

    sourceBefore :
      Experiment.read design sourceCoordinate baselineWorld
      ≡ sourceValue claim

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

    interventionReference : String
    nuisanceReference : String
    identificationReference : String
    measurementReference : String

open CrossLevelCausalDesign public

------------------------------------------------------------------------
-- Causal attribution is stronger than design syntax.  The application states
-- the causal-effect proposition it is entitled to conclude from the declared
-- identification regime and supplies a witness of that proposition.
------------------------------------------------------------------------

record CrossLevelCausalAttribution
    {Value : Set}
    (claim : CrossLevelCausalClaim Value)
    (causalDesign : CrossLevelCausalDesign claim) : Set₁ where
  constructor cross-level-causal-attribution
  field
    CausalEffect : CrossLevelCausalClaim Value → Set
    effectWitness : CausalEffect claim

    chronologyReference : String
    lineageOrSubjectReference : String
    attributionReference : String

open CrossLevelCausalAttribution public

------------------------------------------------------------------------
-- Proof-search binding.
--
-- The existing introspective loop already requires the experiment demand to
-- address the concrete non-factorability witness and to bind the same live
-- residual.  This wrapper makes a causal attribution usable for that route only
-- when the experiment reference is the same experiment already scheduled for
-- the live defect.
------------------------------------------------------------------------

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
    experimentBinding :
      Introspective.ConsumerDefectExperimentBinding liveResidual

    causalExperimentIsScheduledExperiment :
      interventionReference causalDesign
      ≡ Loop.experimentReference
          (Introspective.demand experimentBinding)

    consumerUseReference : String

open CausalExperimentProofSearchBinding public

causalExperimentPaysLiveResidual :
  ∀ {system schedule consumer liveResidual Value claim causalDesign attribution} →
  (binding :
    CausalExperimentProofSearchBinding
      {system} {schedule} {consumer} liveResidual
      {Value} {claim} {causalDesign} attribution) →
  Loop.residual
    (Introspective.demand (experimentBinding binding))
  ≡ liveResidual
causalExperimentPaysLiveResidual binding =
  Introspective.demandResidualMatchesLiveResidual
    (experimentBinding binding)

------------------------------------------------------------------------
-- Consumer closure remains downstream.  A causal effect can repair the live
-- causal coordinate but does not automatically prove that the target consumer
-- descends through the refined observer.
------------------------------------------------------------------------

record CausalAttributionToConsumerClosure
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer)
    {Value : Set}
    {claim : CrossLevelCausalClaim Value}
    {causalDesign : CrossLevelCausalDesign claim}
    {attribution : CrossLevelCausalAttribution claim causalDesign}
    (binding :
      CausalExperimentProofSearchBinding liveResidual attribution) : Set₂ where
  constructor causal-attribution-to-consumer-closure
  field
    refinedReceipt : Fibre.ConsumerRefinementReceipt system consumer
    refinementReference : String

open CausalAttributionToConsumerClosure public

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data CorrelationMeansCausationPermission : Set where

data TemporalOrderMeansCausationPermission : Set where

data DNAConsumerDifferenceMeansMemoryCausePermission : Set where

data TraumaHistoryMeansNeuralCausePermission : Set where

data LearningMeansHeritableChangePermission : Set where

data CulturalPatternMeansBiologicalEssencePermission : Set where

data CausalAttributionAutomaticallyClosesConsumerPermission : Set where

data ExperimentAdmissionCreatesInterventionAuthorityPermission : Set where

correlationDoesNotByItselfIdentifyCause :
  CorrelationMeansCausationPermission → ⊥
correlationDoesNotByItselfIdentifyCause ()

temporalOrderDoesNotByItselfIdentifyCause :
  TemporalOrderMeansCausationPermission → ⊥
temporalOrderDoesNotByItselfIdentifyCause ()

dnaDifferenceDoesNotByItselfCauseMemoryDifference :
  DNAConsumerDifferenceMeansMemoryCausePermission → ⊥
dnaDifferenceDoesNotByItselfCauseMemoryDifference ()

traumaHistoryDoesNotByItselfIdentifyNeuralCause :
  TraumaHistoryMeansNeuralCausePermission → ⊥
traumaHistoryDoesNotByItselfIdentifyNeuralCause ()

learningDoesNotByItselfIdentifyHeritableChange :
  LearningMeansHeritableChangePermission → ⊥
learningDoesNotByItselfIdentifyHeritableChange ()

culturalPatternDoesNotBecomeBiologicalEssence :
  CulturalPatternMeansBiologicalEssencePermission → ⊥
culturalPatternDoesNotBecomeBiologicalEssence ()

causalAttributionDoesNotAutomaticallyCloseConsumer :
  CausalAttributionAutomaticallyClosesConsumerPermission → ⊥
causalAttributionDoesNotAutomaticallyCloseConsumer ()

experimentAdmissionDoesNotCreateInterventionAuthority :
  ExperimentAdmissionCreatesInterventionAuthorityPermission → ⊥
experimentAdmissionDoesNotCreateInterventionAuthority ()

record MultiscaleCausalProvenanceBoundary : Set where
  constructor multiscale-causal-provenance-boundary
  field
    crossLevelClaimMustNameSourceAndTargetLevels : Bool
    causalExperimentRequiresControlledSourceCoordinate : Bool
    targetMustBeMeasuredOrDerived : Bool
    nuisanceCoordinatesRemainExplicit : Bool
    causalIdentificationRequiresApplicationReceipt : Bool
    proofSearchMustBindSameLiveResidual : Bool
    causalAttributionAutomaticallyClosesConsumer : Bool
    correlationAutomaticallyMeansCausation : Bool
    culturalPatternAutomaticallyBecomesBiologicalEssence : Bool

canonicalMultiscaleCausalProvenanceBoundary :
  MultiscaleCausalProvenanceBoundary
canonicalMultiscaleCausalProvenanceBoundary =
  multiscale-causal-provenance-boundary
    true true true true true true false false false
