module DASHI.Law.CoerciveEncounterDenominatorIntegrityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Law.CoerciveEncounterFixtureCompilerExact as Fixture
import DASHI.Law.CoerciveEncounterPopulationAggregationExact as Population

------------------------------------------------------------------------
-- Denominator domains are typed separately.  Encounter counts, unique-person
-- counts, eligible populations, and selected populations are not interchangeable.
------------------------------------------------------------------------

data DenominatorDomain : Set where
  encounterDomain uniquePersonDomain eligiblePopulationDomain selectedPopulationDomain : DenominatorDomain

data IdentityState : Set where
  stablePersonKey identityMissing identityConflict : IdentityState

data EligibilityState : Set where
  eligible notEligible eligibilityMissing eligibilityConflict : EligibilityState

data SelectionState : Set where
  selected notSelected selectionMissing selectionConflict : SelectionState

record PersonLinkedFixture : Set where
  constructor personLinkedFixture
  field
    fixture : Fixture.EncounterFixture
    personKey : String
    identityState : IdentityState
    eligibilityState : EligibilityState
    selectionState : SelectionState
    linkageReference : String

open PersonLinkedFixture public

record DenominatorLedger : Set where
  constructor denominatorLedger
  field
    linkedFixtures : List PersonLinkedFixture
    encounterCount : ℕ
    uniquePersonCount : ℕ
    eligiblePersonCount : ℕ
    selectedPersonCount : ℕ
    repeatedEncounterCount : ℕ
    identityMissingCount : ℕ
    eligibilityMissingCount : ℕ
    selectionMissingCount : ℕ
    ledgerReference : String

open DenominatorLedger public

------------------------------------------------------------------------
-- We do not pretend to derive unique-person counts without an identity/linkage
-- producer.  The ledger therefore stores the counts together with provenance.
------------------------------------------------------------------------

record DenominatorIntegrityReceipt (ledger : DenominatorLedger) : Set where
  constructor denominatorIntegrityReceipt
  field
    encounterAndPersonDomainsSeparated : Bool
    encounterAndPersonDomainsSeparatedIsTrue : encounterAndPersonDomainsSeparated ≡ true
    eligibleAndSelectedDomainsSeparated : Bool
    eligibleAndSelectedDomainsSeparatedIsTrue : eligibleAndSelectedDomainsSeparated ≡ true
    missingnessRetained : Bool
    missingnessRetainedIsTrue : missingnessRetained ≡ true
    identityLinkageReference : String

open DenominatorIntegrityReceipt public

------------------------------------------------------------------------
-- Claim-specific denominator routing.
------------------------------------------------------------------------

data DenominatorConsumer : Set where
  perEncounterGatewayRate perPersonExposureRate selectionRate disparityRate : DenominatorConsumer

data DenominatorObligation : Set where
  encounterDenominator uniquePersonDenominator eligiblePopulationDenominator selectedPopulationDenominator : DenominatorObligation

reverseDenominator : DenominatorConsumer → DenominatorObligation
reverseDenominator perEncounterGatewayRate = encounterDenominator
reverseDenominator perPersonExposureRate = uniquePersonDenominator
reverseDenominator selectionRate = eligiblePopulationDenominator
reverseDenominator disparityRate = eligiblePopulationDenominator

perPersonExposureNeedsUniquePersons :
  reverseDenominator perPersonExposureRate ≡ uniquePersonDenominator
perPersonExposureNeedsUniquePersons = refl

selectionNeedsEligibilityDenominator :
  reverseDenominator selectionRate ≡ eligiblePopulationDenominator
selectionNeedsEligibilityDenominator = refl

------------------------------------------------------------------------
-- Missingness and negative observation are intentionally non-coincident.
------------------------------------------------------------------------

data StatusObservation : Set where
  statusPositive statusNegative statusMissing statusConflict : StatusObservation

data StatusInterpretation : Set where
  observedPositive observedNegative unresolvedStatus : StatusInterpretation

interpretStatus : StatusObservation → StatusInterpretation
interpretStatus statusPositive = observedPositive
interpretStatus statusNegative = observedNegative
interpretStatus statusMissing = unresolvedStatus
interpretStatus statusConflict = unresolvedStatus

missingStatusIsNotNegative :
  interpretStatus statusMissing ≡ unresolvedStatus
missingStatusIsNotNegative = refl

conflictingStatusIsNotNegative :
  interpretStatus statusConflict ≡ unresolvedStatus
conflictingStatusIsNotNegative = refl

------------------------------------------------------------------------
-- Canonical regression: four encounter records may correspond to only two
-- people.  Per-encounter and per-person denominators therefore differ.
------------------------------------------------------------------------

canonicalLinkedFixtureA1 : PersonLinkedFixture
canonicalLinkedFixtureA1 = personLinkedFixture
  Fixture.canonicalMissingSafeguardFixture
  "person-A"
  stablePersonKey eligible selected
  "synthetic person-A encounter 1"

canonicalLinkedFixtureA2 : PersonLinkedFixture
canonicalLinkedFixtureA2 = personLinkedFixture
  Fixture.canonicalMissingSafeguardFixture
  "person-A"
  stablePersonKey eligible selected
  "synthetic person-A encounter 2"

canonicalLinkedFixtureB1 : PersonLinkedFixture
canonicalLinkedFixtureB1 = personLinkedFixture
  Fixture.canonicalMissingSafeguardFixture
  "person-B"
  stablePersonKey eligible selected
  "synthetic person-B encounter 1"

canonicalLinkedFixtureB2 : PersonLinkedFixture
canonicalLinkedFixtureB2 = personLinkedFixture
  Fixture.canonicalMissingSafeguardFixture
  "person-B"
  stablePersonKey eligible selected
  "synthetic person-B encounter 2"

canonicalDenominatorLedger : DenominatorLedger
canonicalDenominatorLedger = denominatorLedger
  (canonicalLinkedFixtureA1 ∷ canonicalLinkedFixtureA2 ∷ canonicalLinkedFixtureB1 ∷ canonicalLinkedFixtureB2 ∷ [])
  4 2 2 2 2 0 0 0
  "synthetic repeated-encounter regression; counts are explicit receipts"

canonicalDenominatorIntegrity : DenominatorIntegrityReceipt canonicalDenominatorLedger
canonicalDenominatorIntegrity = denominatorIntegrityReceipt
  true refl true refl true refl
  "synthetic stable person-key linkage"

canonicalEncounterCount : encounterCount canonicalDenominatorLedger ≡ 4
canonicalEncounterCount = refl

canonicalUniquePersonCount : uniquePersonCount canonicalDenominatorLedger ≡ 2
canonicalUniquePersonCount = refl

canonicalRepeatedEncounterCount : repeatedEncounterCount canonicalDenominatorLedger ≡ 2
canonicalRepeatedEncounterCount = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record DenominatorIntegrityBoundary : Set where
  constructor denominatorIntegrityBoundary
  field
    encounterCountEqualsUniquePersonCount : Bool
    encounterCountEqualsUniquePersonCountIsFalse : encounterCountEqualsUniquePersonCount ≡ false
    selectedPopulationEqualsEligiblePopulation : Bool
    selectedPopulationEqualsEligiblePopulationIsFalse : selectedPopulationEqualsEligiblePopulation ≡ false
    missingStatusCountsAsNegative : Bool
    missingStatusCountsAsNegativeIsFalse : missingStatusCountsAsNegative ≡ false
    repeatedEncountersMayBeUsedAsIndependentPeople : Bool
    repeatedEncountersMayBeUsedAsIndependentPeopleIsFalse : repeatedEncountersMayBeUsedAsIndependentPeople ≡ false
    populationShareAloneProvesSelectionDisparity : Bool
    populationShareAloneProvesSelectionDisparityIsFalse : populationShareAloneProvesSelectionDisparity ≡ false

canonicalDenominatorIntegrityBoundary : DenominatorIntegrityBoundary
canonicalDenominatorIntegrityBoundary =
  denominatorIntegrityBoundary false refl false refl false refl false refl false refl
