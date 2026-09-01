module DASHI.Governance.AnomalousCompetingExperimentCostedSelectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory

------------------------------------------------------------------------
-- COSTED COMPETING EXPERIMENTS ON ONE LIVE COLLISION
--
-- This finite fixture deliberately includes:
--   * a cheap separator;
--   * a more expensive separator;
--   * an even cheaper NON-separator.
--
-- Therefore the minimality theorem cannot be obtained from numeric cost alone:
-- the alternative must first carry a real BundleSeparates witness.
------------------------------------------------------------------------

data PresentimentObservation : Set where
  anomalyReadout artifactReadout collapsedReadout : PresentimentObservation

cheapObserve : Trajectory.Interpretation → PresentimentObservation
cheapObserve Trajectory.anticipatoryPhysiologyAnomaly = anomalyReadout
cheapObserve Trajectory.presentimentMethodArtifact = artifactReadout
cheapObserve _ = collapsedReadout

highRigourObserve : Trajectory.Interpretation → PresentimentObservation
highRigourObserve Trajectory.anticipatoryPhysiologyAnomaly = anomalyReadout
highRigourObserve Trajectory.presentimentMethodArtifact = artifactReadout
highRigourObserve _ = collapsedReadout

surveyObserve : Trajectory.Interpretation → PresentimentObservation
surveyObserve _ = collapsedReadout

cheapSeparator : Disc.ExperimentBundle Trajectory.Interpretation
cheapSeparator = Disc.experimentBundle
  PresentimentObservation
  cheapObserve
  2
  "preregistered presentiment replication with fixed stopping/scoring"
  "automated randomisation, leakage audit, locked preprocessing"

highRigourSeparator : Disc.ExperimentBundle Trajectory.Interpretation
highRigourSeparator = Disc.experimentBundle
  PresentimentObservation
  highRigourObserve
  4
  "multi-lab adversarial presentiment replication"
  "proponent/skeptic joint protocol, independent audit and locked pipeline"

cheapNonSeparator : Disc.ExperimentBundle Trajectory.Interpretation
cheapNonSeparator = Disc.experimentBundle
  PresentimentObservation
  surveyObserve
  1
  "retrospective experience survey"
  "self-report collection only; not calibrated as a discriminator of the live pair"

cheapReallySeparates :
  Disc.BundleSeparates
    cheapSeparator
    Trajectory.anticipatoryPhysiologyAnomaly
    Trajectory.presentimentMethodArtifact
cheapReallySeparates = Disc.bundleSeparates (λ ())

highRigourReallySeparates :
  Disc.BundleSeparates
    highRigourSeparator
    Trajectory.anticipatoryPhysiologyAnomaly
    Trajectory.presentimentMethodArtifact
highRigourReallySeparates = Disc.bundleSeparates (λ ())

cheapSurveyCannotSeparate :
  Disc.BundleSeparates
    cheapNonSeparator
    Trajectory.anticipatoryPhysiologyAnomaly
    Trajectory.presentimentMethodArtifact → ⊥
cheapSurveyCannotSeparate separator =
  Disc.separates separator refl

------------------------------------------------------------------------
-- The current coarse evidence label collapses the live pair.
------------------------------------------------------------------------

data PresentimentSurface : Set where contestedPresentimentSurface : PresentimentSurface

presentimentSurface : Trajectory.Interpretation → PresentimentSurface
presentimentSurface _ = contestedPresentimentSurface

presentimentCollision : Disc.CurrentObserverCollision presentimentSurface
presentimentCollision = Disc.currentObserverCollision
  Trajectory.anticipatoryPhysiologyAnomaly
  Trajectory.presentimentMethodArtifact
  refl

------------------------------------------------------------------------
-- Declared comparison menu.
------------------------------------------------------------------------

data DeclaredPresentimentBundle :
  Disc.ExperimentBundle Trajectory.Interpretation → Set where
  declaredCheap : DeclaredPresentimentBundle cheapSeparator
  declaredHighRigour : DeclaredPresentimentBundle highRigourSeparator
  declaredSurvey : DeclaredPresentimentBundle cheapNonSeparator

cheapIsMinimalDiscriminator :
  Disc.MinimalDiscriminator presentimentSurface DeclaredPresentimentBundle
cheapIsMinimalDiscriminator = Disc.minimalDiscriminator
  presentimentCollision
  cheapSeparator
  declaredCheap
  cheapReallySeparates
  minimal
  "minimal among declared bundles that really separate the current live pair"
  where
  minimal :
    (alternative : Disc.ExperimentBundle Trajectory.Interpretation) →
    DeclaredPresentimentBundle alternative →
    Disc.BundleSeparates
      alternative
      Trajectory.anticipatoryPhysiologyAnomaly
      Trajectory.presentimentMethodArtifact →
    Disc.cost cheapSeparator ≤ Disc.cost alternative
  minimal .cheapSeparator declaredCheap separates = s≤s (s≤s z≤n)
  minimal .highRigourSeparator declaredHighRigour separates = s≤s (s≤s z≤n)
  minimal .cheapNonSeparator declaredSurvey separates with cheapSurveyCannotSeparate separates
  ... | ()

------------------------------------------------------------------------
-- Resource cost is kept separate from burden, calibration risk and authority.
------------------------------------------------------------------------

data ParticipantBurden : Set where lowBurden moderateBurden highBurden : ParticipantBurden

data CalibrationRisk : Set where lowCalibrationRisk mediumCalibrationRisk highCalibrationRisk : CalibrationRisk

record ExperimentDesignProfile
    (bundle : Disc.ExperimentBundle Trajectory.Interpretation) : Set where
  constructor experimentDesignProfile
  field
    participantBurden : ParticipantBurden
    calibrationRisk : CalibrationRisk
    ethicsReference : String
    authorityReference : String

cheapProfile : ExperimentDesignProfile cheapSeparator
cheapProfile = experimentDesignProfile
  lowBurden
  mediumCalibrationRisk
  "participant burden and consent must be reviewed independently of resource cost"
  "scientific admissibility does not create institutional authority"

highRigourProfile : ExperimentDesignProfile highRigourSeparator
highRigourProfile = experimentDesignProfile
  moderateBurden
  lowCalibrationRisk
  "multi-lab replication adds coordination/participant burden"
  "authority and ethics review remain independent"

surveyProfile : ExperimentDesignProfile cheapNonSeparator
surveyProfile = experimentDesignProfile
  lowBurden
  highCalibrationRisk
  "low burden does not compensate for failure to discriminate the active obligation"
  "survey permission does not promote survey evidence into mechanism authority"

------------------------------------------------------------------------
-- Weld to the repository-native cost/sequential boundaries.
------------------------------------------------------------------------

choiceBoundary : Choice.ActionabilityChoiceBoundary
choiceBoundary = Choice.canonicalActionabilityChoiceBoundary

jointBoundary : Joint.JointSequentialPolicyBoundary
jointBoundary = Joint.canonicalJointSequentialPolicyBoundary

data CheapestPromotesScientificallyBest : Set where

data LowerBurdenPromotesDiscrimination : Set where

data ExpectedSeparationPromotesObservedRefinement : Set where

data ResourceCostOverridesEthics : Set where

cheapestDoesNotPromoteScientificallyBest : CheapestPromotesScientificallyBest → ⊥
cheapestDoesNotPromoteScientificallyBest ()

lowerBurdenDoesNotPromoteDiscrimination : LowerBurdenPromotesDiscrimination → ⊥
lowerBurdenDoesNotPromoteDiscrimination ()

expectedSeparationDoesNotPromoteObservedRefinement :
  ExpectedSeparationPromotesObservedRefinement → ⊥
expectedSeparationDoesNotPromoteObservedRefinement ()

resourceCostDoesNotOverrideEthics : ResourceCostOverridesEthics → ⊥
resourceCostDoesNotOverrideEthics ()

record AnomalousCompetingExperimentCostBoundary : Set where
  constructor anomalousCompetingExperimentCostBoundary
  field
    cheaperNonSeparatorMayBeatSeparatorNumerically : Bool
    cheaperNonSeparatorMayBeatSeparatorNumericallyIsTrue :
      cheaperNonSeparatorMayBeatSeparatorNumerically ≡ true
    separatorGatePrecedesCostOptimization : Bool
    separatorGatePrecedesCostOptimizationIsTrue :
      separatorGatePrecedesCostOptimization ≡ true
    cheapestSeparatorIsScientificallyBest : Bool
    cheapestSeparatorIsScientificallyBestIsFalse :
      cheapestSeparatorIsScientificallyBest ≡ false
    costIncludesEthicalAuthorityAutomatically : Bool
    costIncludesEthicalAuthorityAutomaticallyIsFalse :
      costIncludesEthicalAuthorityAutomatically ≡ false
    expectedDiscriminationEqualsObservedRefinement : Bool
    expectedDiscriminationEqualsObservedRefinementIsFalse :
      expectedDiscriminationEqualsObservedRefinement ≡ false

canonicalAnomalousCompetingExperimentCostBoundary :
  AnomalousCompetingExperimentCostBoundary
canonicalAnomalousCompetingExperimentCostBoundary =
  anomalousCompetingExperimentCostBoundary
    true refl true refl false refl false refl false refl
