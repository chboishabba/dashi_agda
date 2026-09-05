module DASHI.Law.WandingOperationDeploymentProofExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Deployment is proof-relevant.  Authorisation, place, time, officer presence,
-- traffic/exposure and the eligible exposure set are separate coordinates.
------------------------------------------------------------------------

data Closure : Set where open closed : Closure

data DeploymentCoordinate : Set where
  authorisationCoordinate placeCoordinate timeCoordinate officerDeploymentCoordinate
  publicTrafficCoordinate exposureSetCoordinate : DeploymentCoordinate

record OperationDeployment : Set where
  constructor operationDeployment
  field
    operationId : String
    authorisation : Closure
    place : Closure
    timeWindow : Closure
    officerDeployment : Closure
    publicTrafficObserved : Closure
    eligibleExposureSetConstructed : Closure
    authorisationReference : String
    placeReference : String
    timeReference : String
    officerReference : String
    trafficReference : String
    exposureSetReference : String

open OperationDeployment public

data DeploymentReverseResult : Set where
  deploymentClosed : DeploymentReverseResult
  firstOpenDeploymentCoordinate : DeploymentCoordinate → DeploymentReverseResult

firstOpenDeployment : OperationDeployment → DeploymentReverseResult
firstOpenDeployment d with authorisation d
... | open = firstOpenDeploymentCoordinate authorisationCoordinate
... | closed with place d
...   | open = firstOpenDeploymentCoordinate placeCoordinate
...   | closed with timeWindow d
...     | open = firstOpenDeploymentCoordinate timeCoordinate
...     | closed with officerDeployment d
...       | open = firstOpenDeploymentCoordinate officerDeploymentCoordinate
...       | closed with publicTrafficObserved d
...         | open = firstOpenDeploymentCoordinate publicTrafficCoordinate
...         | closed with eligibleExposureSetConstructed d
...           | open = firstOpenDeploymentCoordinate exposureSetCoordinate
...           | closed = deploymentClosed

------------------------------------------------------------------------
-- The exposure set is not just the resident population.  It represents people
-- actually within the operation's place/time opportunity surface.
------------------------------------------------------------------------

record ExposureSetLedger : Set where
  constructor exposureSetLedger
  field
    encounteredPersons : ℕ
    uniquePersons : ℕ
    legallyEligiblePersons : ℕ
    selectedPersons : ℕ
    repeatedPersonEncounters : ℕ
    linkageClosed : Bool
    exposureReference : String

open ExposureSetLedger public

record ConditionalSelectionCount : Set where
  constructor conditionalSelectionCount
  field
    numerator : ℕ
    denominator : ℕ
    numeratorMeaning : String
    denominatorMeaning : String
    conditioningReference : String

open ConditionalSelectionCount public

selectedGivenOpportunityEligibility : ExposureSetLedger → ConditionalSelectionCount
selectedGivenOpportunityEligibility x = conditionalSelectionCount
  (selectedPersons x)
  (legallyEligiblePersons x)
  "persons selected for wanding within the deployment exposure set"
  "persons legally eligible for wanding within the same deployment exposure set"
  "P(Selected | Opportunity, Eligibility) count pair"

canonicalDeployment : OperationDeployment
canonicalDeployment = operationDeployment
  "deployment-qld-synthetic-001"
  closed closed closed closed closed open
  "synthetic authorisation receipt"
  "synthetic place receipt"
  "synthetic time-window receipt"
  "synthetic officer-deployment receipt"
  "synthetic public-traffic observation receipt"
  "eligible exposure set not yet reconstructed"

canonicalDeploymentStopsAtExposureSet :
  firstOpenDeployment canonicalDeployment ≡
  firstOpenDeploymentCoordinate exposureSetCoordinate
canonicalDeploymentStopsAtExposureSet = refl

canonicalExposureLedger : ExposureSetLedger
canonicalExposureLedger = exposureSetLedger
  10 8 6 3 2 true
  "synthetic denominator regression"

canonicalConditionalSelectionNumerator :
  numerator (selectedGivenOpportunityEligibility canonicalExposureLedger) ≡ 3
canonicalConditionalSelectionNumerator = refl

canonicalConditionalSelectionDenominator :
  denominator (selectedGivenOpportunityEligibility canonicalExposureLedger) ≡ 6
canonicalConditionalSelectionDenominator = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record DeploymentBoundary : Set where
  constructor deploymentBoundary
  field
    residentPopulationEqualsExposureSet : Bool
    residentPopulationEqualsExposureSetIsFalse : residentPopulationEqualsExposureSet ≡ false
    encounterCountEqualsUniquePersons : Bool
    encounterCountEqualsUniquePersonsIsFalse : encounterCountEqualsUniquePersons ≡ false
    deploymentAuthorisedMeansEverySelectionLawful : Bool
    deploymentAuthorisedMeansEverySelectionLawfulIsFalse : deploymentAuthorisedMeansEverySelectionLawful ≡ false
    exposureSetClosedMeansOfficerSelectionUnbiased : Bool
    exposureSetClosedMeansOfficerSelectionUnbiasedIsFalse : exposureSetClosedMeansOfficerSelectionUnbiased ≡ false

canonicalDeploymentBoundary : DeploymentBoundary
canonicalDeploymentBoundary =
  deploymentBoundary false refl false refl false refl false refl
