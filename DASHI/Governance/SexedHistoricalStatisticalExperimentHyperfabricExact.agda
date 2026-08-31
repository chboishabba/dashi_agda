module DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact where

------------------------------------------------------------------------
-- STATISTICAL / EXPERIMENT-DESIGN BRIDGE FOR THE SEXED HISTORICAL HYPERFABRIC
--
-- This owner does not make biological sex an essence or causal treatment.
-- It treats recorded sex/gender, historically coded subject-position,
-- construction direction, power, epoch, exposure and observer as separately
-- typed coordinates which may enter different statistical designs.
--
-- Central separations:
--
--   recorded sex != historical construction role
--   marginal group difference != relational interaction
--   association != causal effect
--   fitted probability != subject-formation mechanism
--   logistic dynamical map != logistic-regression link
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.LogisticFoldCriticalityExact as LogisticDynamics
import DASHI.Governance.SexedHistoricalCoConstitutionHyperfabricExact as Hyper
import DASHI.Governance.SexedHistoricalCollectiveThresholdNetworkExact as Collective
import DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact as BrownDesign
import DASHI.Culture.JohnAnthonyBrownQuantitativePopulationBridgeExact as BrownQuant
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design

------------------------------------------------------------------------
-- Observed demographic label and historical construction position are not the
-- same variable.
------------------------------------------------------------------------

data RecordedSexCategory : Set where
  recordedMale recordedFemale recordedOtherOrUnresolved : RecordedSexCategory

data ConstructionDirection : Set where
  masculineToMasculine
  masculineToFeminine
  feminineToMasculine
  feminineToFeminine
  : ConstructionDirection

constructionDirection : Hyper.Position → Hyper.Position → ConstructionDirection
constructionDirection Hyper.masculine Hyper.masculine = masculineToMasculine
constructionDirection Hyper.masculine Hyper.feminine = masculineToFeminine
constructionDirection Hyper.feminine Hyper.masculine = feminineToMasculine
constructionDirection Hyper.feminine Hyper.feminine = feminineToFeminine

------------------------------------------------------------------------
-- Statistical-model vocabulary.  This is a model-specification surface, not a
-- fitted empirical result.
------------------------------------------------------------------------

data StatisticalFamily : Set where
  binaryLogisticRegression
  mixedEffectsLogisticRegression
  ordinalRegression
  multinomialRegression
  linearMixedEffects
  survivalModel
  qualitativeComparativeLane
  : StatisticalFamily

data ModelCoordinate : Set where
  recordedSexCoordinate
  constructorPositionCoordinate
  constructedPositionCoordinate
  constructionDirectionCoordinate
  epochCoordinate
  legalPowerCoordinate
  religiousPowerCoordinate
  familyPowerCoordinate
  collectiveLegibilityCoordinate
  retainedHistoryCoordinate
  exposureCoordinate
  repeatedSubjectCoordinate
  networkClusterCoordinate
  observerCoordinate
  : ModelCoordinate

data InteractionTerm : Set where
  constructorByConstructedInteraction
  positionByEpochInteraction
  positionByPowerInteraction
  positionByExposureInteraction
  exposureByHistoryInteraction
  networkByPositionInteraction
  : InteractionTerm

record StatisticalModelReceipt : Set where
  constructor statistical-model-receipt
  field
    modelKey : String
    family : StatisticalFamily
    coordinates : List ModelCoordinate
    interactions : List InteractionTerm
    repeatedMeasuresRepresented : Bool
    clusteringRepresented : Bool
    uncertaintyRequired : Bool
    modelDiagnosticsRequired : Bool
    causalIdentificationClaimed : Bool

open StatisticalModelReceipt public

canonicalSexConstructionInteractionModel : StatisticalModelReceipt
canonicalSexConstructionInteractionModel =
  statistical-model-receipt
    "sexed-history-construction-interaction-model"
    mixedEffectsLogisticRegression
    (recordedSexCoordinate
      ∷ constructorPositionCoordinate
      ∷ constructedPositionCoordinate
      ∷ epochCoordinate
      ∷ legalPowerCoordinate
      ∷ religiousPowerCoordinate
      ∷ familyPowerCoordinate
      ∷ exposureCoordinate
      ∷ retainedHistoryCoordinate
      ∷ repeatedSubjectCoordinate
      ∷ networkClusterCoordinate
      ∷ observerCoordinate
      ∷ [])
    (constructorByConstructedInteraction
      ∷ positionByEpochInteraction
      ∷ positionByPowerInteraction
      ∷ positionByExposureInteraction
      ∷ exposureByHistoryInteraction
      ∷ networkByPositionInteraction
      ∷ [])
    true true true true false

------------------------------------------------------------------------
-- A main-effect sex label cannot recover the 2x2 relational construction cell.
------------------------------------------------------------------------

data SexMarginalFineState : Set where
  femaleObservedUnderMasculineConstruction
  femaleObservedUnderFeminineSelfConstruction
  : SexMarginalFineState

recordedSexSurface : SexMarginalFineState → RecordedSexCategory
recordedSexSurface _ = recordedFemale

relationalCell : SexMarginalFineState → ConstructionDirection
relationalCell femaleObservedUnderMasculineConstruction = masculineToFeminine
relationalCell femaleObservedUnderFeminineSelfConstruction = feminineToFeminine

recordedSexCannotRecoverConstructionDirection :
  INF.FactorsThrough recordedSexSurface relationalCell → ⊥
recordedSexCannotRecoverConstructionDirection =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      femaleObservedUnderMasculineConstruction
      femaleObservedUnderFeminineSelfConstruction
      refl
      (λ ()))

------------------------------------------------------------------------
-- Conversely, the same construction direction can coexist with different
-- power contexts, so an interaction label is not itself a power coefficient.
------------------------------------------------------------------------

data ConstructionPowerFineState : Set where
  sameDirectionLowPower
  sameDirectionHighPower
  : ConstructionPowerFineState

constructionDirectionSurface : ConstructionPowerFineState → ConstructionDirection
constructionDirectionSurface _ = feminineToMasculine

powerContext : ConstructionPowerFineState → Hyper.PowerLevel
powerContext sameDirectionLowPower = Hyper.lowPower
powerContext sameDirectionHighPower = Hyper.highPower

constructionDirectionCannotRecoverPower :
  INF.FactorsThrough constructionDirectionSurface powerContext → ⊥
constructionDirectionCannotRecoverPower =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameDirectionLowPower
      sameDirectionHighPower
      refl
      (λ ()))

------------------------------------------------------------------------
-- Association and causal identification are different fibres.
------------------------------------------------------------------------

data AssociationSurface : Set where
  positiveAssociation : AssociationSurface

data CausalStatus : Set where
  causalUnidentified causalIdentified : CausalStatus

data AssociationFineState : Set where
  adjustedObservationalAssociation
  identifiedInterventionEffect
  : AssociationFineState

associationSurface : AssociationFineState → AssociationSurface
associationSurface _ = positiveAssociation

causalStatus : AssociationFineState → CausalStatus
causalStatus adjustedObservationalAssociation = causalUnidentified
causalStatus identifiedInterventionEffect = causalIdentified

associationCannotRecoverCausalStatus :
  INF.FactorsThrough associationSurface causalStatus → ⊥
associationCannotRecoverCausalStatus =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      adjustedObservationalAssociation
      identifiedInterventionEffect
      refl
      (λ ()))

------------------------------------------------------------------------
-- Statistical logistics and dynamical logistics are distinct typed roles.
------------------------------------------------------------------------

data LogisticRole : Set where
  dynamicalLogisticMap
  statisticalLogitLink
  : LogisticRole

dynamicalLogisticRoleIsNotStatisticalLogitRole :
  dynamicalLogisticMap ≡ statisticalLogitLink → ⊥
dynamicalLogisticRoleIsNotStatisticalLogitRole ()

mergedLogisticHalfIsNotUniversalStatisticalThreshold :
  LogisticDynamics.LogisticFoldCriticalityBoundary.halfIsUniversalDecisionThreshold
    LogisticDynamics.canonicalLogisticFoldCriticalityBoundary
  ≡ false
mergedLogisticHalfIsNotUniversalStatisticalThreshold =
  LogisticDynamics.LogisticFoldCriticalityBoundary.halfIsUniversalDecisionThresholdIsFalse
    LogisticDynamics.canonicalLogisticFoldCriticalityBoundary

------------------------------------------------------------------------
-- Cross-pollination with John Anthony Brown study design / quantitative lane.
------------------------------------------------------------------------

brownLongitudinalDesignStillObservational :
  BrownDesign.JohnAnthonyBrownStudyDesignBoundary.childhoodExposureIsProspectivelyRandomised
    BrownDesign.canonicalJohnAnthonyBrownStudyDesignBoundary
  ≡ false
brownLongitudinalDesignStillObservational = refl

brownStudyRequiresMixedEffects :
  BrownDesign.JohnAnthonyBrownStudyDesignBoundary.primaryAnalysisUsesMixedEffects
    BrownDesign.canonicalJohnAnthonyBrownStudyDesignBoundary
  ≡ true
brownStudyRequiresMixedEffects = refl

brownQuantitativeTargetStillMissingDirectCatholicChildhoodEffect :
  BrownQuant.QuantitativePopulationBridgeBoundary.directCatholicChildhoodLongitudinalEffectStillMissing
    BrownQuant.canonicalQuantitativePopulationBridgeBoundary
  ≡ true
brownQuantitativeTargetStillMissingDirectCatholicChildhoodEffect = refl

------------------------------------------------------------------------
-- Study-design implications for male/female-coded construction comparisons.
-- These are obligations, not empirical results.
------------------------------------------------------------------------

record SexConstructionStudyDesign : Set where
  constructor sex-construction-study-design
  field
    designKind : Design.DesignKind
    repeatedMeasures : Bool
    constructionDirectionMeasured : Bool
    powerAxesMeasuredSeparately : Bool
    observerSourceRecorded : Bool
    interactionTermsPlanned : Bool
    networkClusteringRepresented : Bool
    uncertaintyReported : Bool
    qualitativeMeaningLaneRetained : Bool
    causalEffectClaimedFromObservationalDifference : Bool
    binarySexExhaustsSubjectFormation : Bool

open SexConstructionStudyDesign public

canonicalSexConstructionStudyDesign : SexConstructionStudyDesign
canonicalSexConstructionStudyDesign =
  sex-construction-study-design
    Design.mixedMethods
    true true true true true true true true false false

------------------------------------------------------------------------
-- Collective-threshold result remains independent of statistical significance.
------------------------------------------------------------------------

data StatisticalSignificanceSurface : Set where
  conventionallySignificant : StatisticalSignificanceSurface

data InstitutionalOutcomeSurface : Set where
  noShift shift : InstitutionalOutcomeSurface

data SignificanceFineState : Set where
  significantWithoutInstitutionalShift
  significantWithInstitutionalShift
  : SignificanceFineState

significanceSurface : SignificanceFineState → StatisticalSignificanceSurface
significanceSurface _ = conventionallySignificant

institutionalOutcomeSurface : SignificanceFineState → InstitutionalOutcomeSurface
institutionalOutcomeSurface significantWithoutInstitutionalShift = noShift
institutionalOutcomeSurface significantWithInstitutionalShift = shift

significanceCannotRecoverInstitutionalOutcome :
  INF.FactorsThrough significanceSurface institutionalOutcomeSurface → ⊥
significanceCannotRecoverInstitutionalOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      significantWithoutInstitutionalShift
      significantWithInstitutionalShift
      refl
      (λ ()))

collectiveParticipationStillCannotRecoverOutcome =
  Collective.participationCannotRecoverInstitutionalOutcome

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data MaleFemaleMeanDifferencePromotesEssence : Set where

data SignificantInteractionPromotesMechanism : Set where

data AdjustedRegressionPromotesNoResidualConfounding : Set where

data SexCoefficientPromotesConstructionDirection : Set where

data BinaryCodingPromotesExhaustiveGenderOntology : Set where

data ModelFitPromotesHistoricalCausation : Set where

maleFemaleMeanDifferenceDoesNotPromoteEssence :
  MaleFemaleMeanDifferencePromotesEssence → ⊥
maleFemaleMeanDifferenceDoesNotPromoteEssence ()

significantInteractionDoesNotPromoteMechanism :
  SignificantInteractionPromotesMechanism → ⊥
significantInteractionDoesNotPromoteMechanism ()

adjustedRegressionDoesNotPromoteNoResidualConfounding :
  AdjustedRegressionPromotesNoResidualConfounding → ⊥
adjustedRegressionDoesNotPromoteNoResidualConfounding ()

sexCoefficientDoesNotPromoteConstructionDirection :
  SexCoefficientPromotesConstructionDirection → ⊥
sexCoefficientDoesNotPromoteConstructionDirection ()

binaryCodingDoesNotPromoteExhaustiveGenderOntology :
  BinaryCodingPromotesExhaustiveGenderOntology → ⊥
binaryCodingDoesNotPromoteExhaustiveGenderOntology ()

modelFitDoesNotPromoteHistoricalCausation :
  ModelFitPromotesHistoricalCausation → ⊥
modelFitDoesNotPromoteHistoricalCausation ()

record SexedHistoricalStatisticalExperimentBoundary : Set where
  constructor sexed-historical-statistical-experiment-boundary
  field
    recordedSexEqualsConstructionRole : Bool
    marginalDifferenceEqualsInteraction : Bool
    interactionEqualsPower : Bool
    adjustedAssociationEqualsCausalEffect : Bool
    statisticalLogitEqualsDynamicalLogisticMap : Bool
    significantInteractionEqualsMechanism : Bool
    binarySexCodingExhaustsSubjectFormation : Bool
    longitudinalObservationEqualsRandomisation : Bool
    mixedMethodsCanRetainDivergence : Bool
    interactionsShouldBeExplicit : Bool
    powerShouldRemainSeparateFibre : Bool
    networkClusteringShouldRemainRepresented : Bool

canonicalSexedHistoricalStatisticalExperimentBoundary :
  SexedHistoricalStatisticalExperimentBoundary
canonicalSexedHistoricalStatisticalExperimentBoundary =
  sexed-historical-statistical-experiment-boundary
    false false false false false false false false true true true true
