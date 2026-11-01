module DASHI.Cognition.PNF.SensibLawWrongTypeRequirementSalienceFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact as Live

------------------------------------------------------------------------
-- LEGAL REQUIREMENT SALIENCE FRONTIER
--
-- A legal requirement may remain normatively/structurally required while having
-- zero present discrimination value on the CURRENT live interpretation fibre.
-- Requirement existence and next-question salience are therefore different
-- coordinates.
------------------------------------------------------------------------

record RequirementSalienceProblem
    (Requirement Interpretation Observation : Set) : Set₁ where
  constructor requirement-salience-problem
  field
    live : Live.LiveSet Interpretation
    observe : Requirement → Interpretation → Observation
    RequiredForConsumer : Requirement → Set
    ConsumerRelevant : Requirement → Set
    AuthorityAdmissible : Requirement → Set
    problemReference : String

open RequirementSalienceProblem public

record SplitsCurrentLiveFibre
    {Requirement Interpretation Observation : Set}
    (problem : RequirementSalienceProblem Requirement Interpretation Observation)
    (requirement : Requirement) : Set where
  constructor splits-current-live-fibre
  field
    left right : Interpretation
    leftLive : live problem left
    rightLive : live problem right
    observationDiffers :
      observe problem requirement left ≡ observe problem requirement right → ⊥

open SplitsCurrentLiveFibre public

record ZeroCurrentDiscrimination
    {Requirement Interpretation Observation : Set}
    (problem : RequirementSalienceProblem Requirement Interpretation Observation)
    (requirement : Requirement) : Set₁ where
  constructor zero-current-discrimination
  field
    constantOnLiveFibre :
      ∀ left right →
      live problem left →
      live problem right →
      observe problem requirement left ≡ observe problem requirement right

open ZeroCurrentDiscrimination public

record SalientRequirement
    {Requirement Interpretation Observation : Set}
    (problem : RequirementSalienceProblem Requirement Interpretation Observation)
    (requirement : Requirement) : Set where
  constructor salient-requirement
  field
    required : RequiredForConsumer problem requirement
    relevant : ConsumerRelevant problem requirement
    admissible : AuthorityAdmissible problem requirement
    splits : SplitsCurrentLiveFibre problem requirement

open SalientRequirement public

record NecessaryButCurrentlyNonDiscriminating
    {Requirement Interpretation Observation : Set}
    (problem : RequirementSalienceProblem Requirement Interpretation Observation)
    (requirement : Requirement) : Set₁ where
  constructor necessary-but-currently-nondiscriminating
  field
    stillRequired : RequiredForConsumer problem requirement
    stillRelevant : ConsumerRelevant problem requirement
    stillAdmissible : AuthorityAdmissible problem requirement
    zeroDiscrimination : ZeroCurrentDiscrimination problem requirement

open NecessaryButCurrentlyNonDiscriminating public

------------------------------------------------------------------------
-- Exact generic calibration.
------------------------------------------------------------------------

data ToyRequirement : Set where
  sharedRequiredCoordinate : ToyRequirement
  liveSplittingCoordinate : ToyRequirement


data ToyInterpretation : Set where
  interpretationA : ToyInterpretation
  interpretationB : ToyInterpretation

data ToyObservation : Set where
  observationNo : ToyObservation
  observationYes : ToyObservation

toyLive : Live.LiveSet ToyInterpretation
toyLive interpretationA = ⊤
toyLive interpretationB = ⊤

toyObserve : ToyRequirement → ToyInterpretation → ToyObservation
toyObserve sharedRequiredCoordinate interpretationA = observationNo
toyObserve sharedRequiredCoordinate interpretationB = observationNo
toyObserve liveSplittingCoordinate interpretationA = observationNo
toyObserve liveSplittingCoordinate interpretationB = observationYes

data ToyRequired : ToyRequirement → Set where
  sharedRequired : ToyRequired sharedRequiredCoordinate
  splittingRequired : ToyRequired liveSplittingCoordinate

data ToyRelevant : ToyRequirement → Set where
  sharedRelevant : ToyRelevant sharedRequiredCoordinate
  splittingRelevant : ToyRelevant liveSplittingCoordinate

data ToyAdmissible : ToyRequirement → Set where
  sharedAdmissible : ToyAdmissible sharedRequiredCoordinate
  splittingAdmissible : ToyAdmissible liveSplittingCoordinate

toyProblem : RequirementSalienceProblem ToyRequirement ToyInterpretation ToyObservation
toyProblem = requirement-salience-problem
  toyLive
  toyObserve
  ToyRequired
  ToyRelevant
  ToyAdmissible
  "A legally required coordinate may be constant across the current live interpretations while another required coordinate actually splits them."

sharedCoordinateHasZeroCurrentDiscrimination :
  ZeroCurrentDiscrimination toyProblem sharedRequiredCoordinate
sharedCoordinateHasZeroCurrentDiscrimination = zero-current-discrimination same
  where
    same : ∀ left right → toyLive left → toyLive right →
      toyObserve sharedRequiredCoordinate left ≡ toyObserve sharedRequiredCoordinate right
    same interpretationA interpretationA leftLive rightLive = refl
    same interpretationA interpretationB leftLive rightLive = refl
    same interpretationB interpretationA leftLive rightLive = refl
    same interpretationB interpretationB leftLive rightLive = refl

sharedCoordinateStillNecessary :
  NecessaryButCurrentlyNonDiscriminating toyProblem sharedRequiredCoordinate
sharedCoordinateStillNecessary = necessary-but-currently-nondiscriminating
  sharedRequired sharedRelevant sharedAdmissible sharedCoordinateHasZeroCurrentDiscrimination

splittingCoordinateIsSalient :
  SalientRequirement toyProblem liveSplittingCoordinate
splittingCoordinateIsSalient = salient-requirement
  splittingRequired
  splittingRelevant
  splittingAdmissible
  (splits-current-live-fibre
    interpretationA interpretationB tt tt (λ ()))

------------------------------------------------------------------------
-- Cross-pollination with the generic residual live-set theorem.
------------------------------------------------------------------------

smallResidualCanBeLiveSetSalient : Live.SalientOn Live.smallSeparating Live.toyLive
smallResidualCanBeLiveSetSalient = Live.smallResidualIsSalient

largeResidualCanBeLiveSetInert : Live.SalientOn Live.largeInert Live.toyLive → ⊥
largeResidualCanBeLiveSetInert = Live.largeResidualIsNotSalient

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RequiredMeansCurrentlySalient : Set where
data ZeroCurrentDiscriminationMeansRequirementMayBeDeleted : Set where
data SalientMeansLegallySatisfied : Set where
data SalientMeansAuthorityRecovered : Set where

requiredDoesNotMeanNextQuestion : RequiredMeansCurrentlySalient → ⊥
requiredDoesNotMeanNextQuestion ()

zeroDiscriminationDoesNotDeleteRequirement :
  ZeroCurrentDiscriminationMeansRequirementMayBeDeleted → ⊥
zeroDiscriminationDoesNotDeleteRequirement ()

salienceDoesNotPayRequirement : SalientMeansLegallySatisfied → ⊥
salienceDoesNotPayRequirement ()

salienceDoesNotCreateAuthority : SalientMeansAuthorityRecovered → ⊥
salienceDoesNotCreateAuthority ()
