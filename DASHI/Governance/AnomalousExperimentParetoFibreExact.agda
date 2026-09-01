module DASHI.Governance.AnomalousExperimentParetoFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Core.CostedResidualInformationChoiceExact as ResidualChoice
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory
import DASHI.Governance.AnomalousCompetingExperimentCostedSelectionExact as Competition

------------------------------------------------------------------------
-- ADMISSION-FIRST PARETO FIBRE FOR ONE LIVE EXPERIMENTAL OBLIGATION
--
-- The front is finite and relative to the declared design language.  A design
-- reaches Pareto comparison only after it carries a literal separator receipt
-- for the current live presentiment collision.  Resource cost, participant
-- burden, calibration risk, nuisance robustness and certified residual gain
-- remain independent declared coordinates.
------------------------------------------------------------------------

data StudyDesign : Set where
  preregisteredStudy
  adversarialMultiLabStudy
  retrospectiveSurvey
  : StudyDesign

bundleOf : StudyDesign → Disc.ExperimentBundle Trajectory.Interpretation
bundleOf preregisteredStudy = Competition.cheapSeparator
bundleOf adversarialMultiLabStudy = Competition.highRigourSeparator
bundleOf retrospectiveSurvey = Competition.cheapNonSeparator

record AdmittedDesign (design : StudyDesign) : Set where
  constructor admittedDesign
  field
    separator :
      Disc.BundleSeparates
        (bundleOf design)
        Trajectory.anticipatoryPhysiologyAnomaly
        Trajectory.presentimentMethodArtifact
    ethicsReference : String
    authorityReference : String

open AdmittedDesign public

preregisteredAdmitted : AdmittedDesign preregisteredStudy
preregisteredAdmitted = admittedDesign
  Competition.cheapReallySeparates
  "low-burden preregistered replication still requires ordinary participant-protection review"
  "scientific admission does not itself issue institutional authority"

adversarialAdmitted : AdmittedDesign adversarialMultiLabStudy
adversarialAdmitted = admittedDesign
  Competition.highRigourReallySeparates
  "multi-lab adversarial design carries additional coordination/participant burden"
  "independent authority and ethics review remain required"

surveyNotAdmitted : AdmittedDesign retrospectiveSurvey → ⊥
surveyNotAdmitted admitted = Competition.cheapSurveyCannotSeparate (separator admitted)

------------------------------------------------------------------------
-- Declared objective coordinates.  These are finite design-order coordinates,
-- not probabilities, utilities, entropy estimates or fibre cardinalities.
------------------------------------------------------------------------

resourceCost : StudyDesign → Nat
resourceCost preregisteredStudy = 2
resourceCost adversarialMultiLabStudy = 4
resourceCost retrospectiveSurvey = 1

participantBurdenScore : StudyDesign → Nat
participantBurdenScore preregisteredStudy = 1
participantBurdenScore adversarialMultiLabStudy = 2
participantBurdenScore retrospectiveSurvey = 1

calibrationRiskScore : StudyDesign → Nat
calibrationRiskScore preregisteredStudy = 2
calibrationRiskScore adversarialMultiLabStudy = 1
calibrationRiskScore retrospectiveSurvey = 3

nuisanceRobustnessScore : StudyDesign → Nat
nuisanceRobustnessScore preregisteredStudy = 1
nuisanceRobustnessScore adversarialMultiLabStudy = 3
nuisanceRobustnessScore retrospectiveSurvey = 0

certifiedResidualGain : StudyDesign → Nat
certifiedResidualGain preregisteredStudy = 1
certifiedResidualGain adversarialMultiLabStudy = 1
certifiedResidualGain retrospectiveSurvey = 0

------------------------------------------------------------------------
-- Five-axis weak dominance on already-admitted designs.
------------------------------------------------------------------------

record NoWorse (left right : StudyDesign) : Set where
  constructor noWorse
  field
    noMoreResourceCost : resourceCost left ≤ resourceCost right
    noMoreParticipantBurden : participantBurdenScore left ≤ participantBurdenScore right
    noMoreCalibrationRisk : calibrationRiskScore left ≤ calibrationRiskScore right
    noLessNuisanceRobustness : nuisanceRobustnessScore right ≤ nuisanceRobustnessScore left
    noLessCertifiedResidualGain : certifiedResidualGain right ≤ certifiedResidualGain left

open NoWorse public

data StrictWitness (left right : StudyDesign) : Set where
  strictlyCheaper : suc (resourceCost left) ≤ resourceCost right → StrictWitness left right
  strictlyMoreRobust : suc (nuisanceRobustnessScore right) ≤ nuisanceRobustnessScore left → StrictWitness left right

record Dominates (left right : StudyDesign) : Set where
  constructor dominates
  field
    leftAdmitted : AdmittedDesign left
    rightAdmitted : AdmittedDesign right
    noWorse : NoWorse left right
    strict : StrictWitness left right

open Dominates public

record NonDominated (design : StudyDesign) : Set where
  constructor nonDominated
  field
    admitted : AdmittedDesign design
    noDeclaredDominator : (other : StudyDesign) → Dominates other design → ⊥

open NonDominated public

------------------------------------------------------------------------
-- The two proper designs trade objectives and are both on the finite front.
------------------------------------------------------------------------

preregisteredSelfStrictImpossible : StrictWitness preregisteredStudy preregisteredStudy → ⊥
preregisteredSelfStrictImpossible (strictlyCheaper (s≤s (s≤s ())))
preregisteredSelfStrictImpossible (strictlyMoreRobust (s≤s ()))

adversarialSelfStrictImpossible : StrictWitness adversarialMultiLabStudy adversarialMultiLabStudy → ⊥
adversarialSelfStrictImpossible (strictlyCheaper (s≤s (s≤s (s≤s (s≤s ())))))
adversarialSelfStrictImpossible (strictlyMoreRobust (s≤s (s≤s (s≤s ()))))

adversarialCannotWeaklyDominatePreregistered : NoWorse adversarialMultiLabStudy preregisteredStudy → ⊥
adversarialCannotWeaklyDominatePreregistered weak =
  fourNotLeTwo (noMoreResourceCost weak)
  where
  fourNotLeTwo : 4 ≤ 2 → ⊥
  fourNotLeTwo (s≤s (s≤s ()))

preregisteredCannotWeaklyDominateAdversarial : NoWorse preregisteredStudy adversarialMultiLabStudy → ⊥
preregisteredCannotWeaklyDominateAdversarial weak =
  threeNotLeOne (noLessNuisanceRobustness weak)
  where
  threeNotLeOne : 3 ≤ 1 → ⊥
  threeNotLeOne (s≤s ())

preregisteredNonDominated : NonDominated preregisteredStudy
preregisteredNonDominated = nonDominated preregisteredAdmitted noDominator
  where
  noDominator : (other : StudyDesign) → Dominates other preregisteredStudy → ⊥
  noDominator preregisteredStudy dom = preregisteredSelfStrictImpossible (strict dom)
  noDominator adversarialMultiLabStudy dom = adversarialCannotWeaklyDominatePreregistered (noWorse dom)
  noDominator retrospectiveSurvey dom = surveyNotAdmitted (leftAdmitted dom)

adversarialNonDominated : NonDominated adversarialMultiLabStudy
adversarialNonDominated = nonDominated adversarialAdmitted noDominator
  where
  noDominator : (other : StudyDesign) → Dominates other adversarialMultiLabStudy → ⊥
  noDominator preregisteredStudy dom = preregisteredCannotWeaklyDominateAdversarial (noWorse dom)
  noDominator adversarialMultiLabStudy dom = adversarialSelfStrictImpossible (strict dom)
  noDominator retrospectiveSurvey dom = surveyNotAdmitted (leftAdmitted dom)

surveyCannotEnterParetoFront : NonDominated retrospectiveSurvey → ⊥
surveyCannotEnterParetoFront front = surveyNotAdmitted (admitted front)

------------------------------------------------------------------------
-- Preference is downstream of the front and is not supplied by nondominance.
------------------------------------------------------------------------

data StudyPreference : Set where
  resourceBurdenPriority robustnessPriority : StudyPreference

preferredDesign : StudyPreference → StudyDesign
preferredDesign resourceBurdenPriority = preregisteredStudy
preferredDesign robustnessPriority = adversarialMultiLabStudy

preferenceCanSelectDifferentFrontPoints :
  preferredDesign resourceBurdenPriority ≡ preferredDesign robustnessPriority → ⊥
preferenceCanSelectDifferentFrontPoints ()

------------------------------------------------------------------------
-- Canonical residual-choice boundary: gain is certified/application-specific,
-- not inferred from arbitrary Set-valued fibre cardinalities.
------------------------------------------------------------------------

residualChoiceBoundary : ResidualChoice.CostedResidualChoiceBoundary
residualChoiceBoundary = ResidualChoice.canonicalCostedResidualChoiceBoundary

data ParetoFrontPromotesTruth : Set where

data ParetoFrontPromotesAuthority : Set where

data DeclaredGainPromotesFibreCardinality : Set where

data FiniteFrontPromotesGlobalOptimum : Set where

paretoFrontDoesNotPromoteTruth : ParetoFrontPromotesTruth → ⊥
paretoFrontDoesNotPromoteTruth ()

paretoFrontDoesNotPromoteAuthority : ParetoFrontPromotesAuthority → ⊥
paretoFrontDoesNotPromoteAuthority ()

declaredGainDoesNotPromoteFibreCardinality : DeclaredGainPromotesFibreCardinality → ⊥
declaredGainDoesNotPromoteFibreCardinality ()

finiteFrontDoesNotPromoteGlobalOptimum : FiniteFrontPromotesGlobalOptimum → ⊥
finiteFrontDoesNotPromoteGlobalOptimum ()

record AnomalousExperimentParetoFibreBoundary : Set where
  constructor anomalousExperimentParetoFibreBoundary
  field
    hardAdmissionPrecedesParetoRanking : Bool
    hardAdmissionPrecedesParetoRankingIsTrue : hardAdmissionPrecedesParetoRanking ≡ true
    cheaperNonSeparatorCanEnterFront : Bool
    cheaperNonSeparatorCanEnterFrontIsFalse : cheaperNonSeparatorCanEnterFront ≡ false
    multipleTradeoffDesignsCanBeNonDominated : Bool
    multipleTradeoffDesignsCanBeNonDominatedIsTrue :
      multipleTradeoffDesignsCanBeNonDominated ≡ true
    paretoFrontCreatesUniquePreference : Bool
    paretoFrontCreatesUniquePreferenceIsFalse : paretoFrontCreatesUniquePreference ≡ false
    paretoFrontCreatesAuthority : Bool
    paretoFrontCreatesAuthorityIsFalse : paretoFrontCreatesAuthority ≡ false
    declaredGainIsLiteralFibreCardinality : Bool
    declaredGainIsLiteralFibreCardinalityIsFalse : declaredGainIsLiteralFibreCardinality ≡ false
    finiteDeclaredFrontIsGlobalDesignOptimum : Bool
    finiteDeclaredFrontIsGlobalDesignOptimumIsFalse : finiteDeclaredFrontIsGlobalDesignOptimum ≡ false

canonicalAnomalousExperimentParetoFibreBoundary : AnomalousExperimentParetoFibreBoundary
canonicalAnomalousExperimentParetoFibreBoundary =
  anomalousExperimentParetoFibreBoundary
    true refl false refl true refl false refl false refl false refl false refl
