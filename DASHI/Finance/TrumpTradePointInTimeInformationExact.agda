module DASHI.Finance.TrumpTradePointInTimeInformationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.OGE278TReportingSemanticsExact as OGE
import DASHI.Finance.TrumpPresident278TTechnologyBasketExact as Basket
import DASHI.Finance.TrumpFamilyTradePrimarySourceRound3Exact as Round3
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- POINT-IN-TIME PUBLIC INFORMATION CUT
--
-- A transaction can have an event date earlier than the date on which the
-- public documentary evidence becomes available.  The later OGE filing may
-- establish that the transaction occurred, but a game/strategy model evaluated
-- before disclosure may not import that later filing into the earlier public
-- information set without an independent contemporaneous source.
------------------------------------------------------------------------

data PublicInformationStage : Set where
  beforeMay8Disclosure : PublicInformationStage
  onOrAfterMay8Disclosure : PublicInformationStage

data Availability : Set where
  unavailable : Availability
  available : Availability

record DelayedPublicEvidence : Set₁ where
  constructor delayed-public-evidence
  field
    claim : Atlas.TradeEvidenceClaim
    eventTimeReference : String
    publicDisclosureTimeReference : String
    availabilityAt : PublicInformationStage → Availability
    timingReference : String

open DelayedPublicEvidence public

may8Availability : PublicInformationStage → Availability
may8Availability beforeMay8Disclosure = unavailable
may8Availability onOrAfterMay8Disclosure = available

coinbaseSaleDelayedPublicEvidence : DelayedPublicEvidence
coinbaseSaleDelayedPublicEvidence =
  delayed-public-evidence
    Round3.trumpCoinbaseSale20260212
    "transaction date reported as 2026-02-12"
    "public OGE Form 278-T dated 2026-05-08"
    may8Availability
    "later OGE filing pays the reported February transaction; it is not automatically a February public signal"

palantirSaleDelayedPublicEvidence : DelayedPublicEvidence
palantirSaleDelayedPublicEvidence =
  delayed-public-evidence
    Basket.palantirSale20260210
    "transaction date reported as 2026-02-10"
    "public OGE Form 278-T dated 2026-05-08"
    may8Availability
    "later OGE filing pays the reported February transaction; it is not automatically a February public signal"

metaSaleDelayedPublicEvidence : DelayedPublicEvidence
metaSaleDelayedPublicEvidence =
  delayed-public-evidence
    Basket.metaSale20260210
    "transaction date reported as 2026-02-10"
    "public OGE Form 278-T dated 2026-05-08"
    may8Availability
    "later OGE filing pays the reported February transaction; it is not automatically a February public signal"

amazonSaleDelayedPublicEvidence : DelayedPublicEvidence
amazonSaleDelayedPublicEvidence =
  delayed-public-evidence
    Basket.amazonSale20260210
    "transaction date reported as 2026-02-10"
    "public OGE Form 278-T dated 2026-05-08"
    may8Availability
    "later OGE filing pays the reported February transaction; it is not automatically a February public signal"

microsoftSaleDelayedPublicEvidence : DelayedPublicEvidence
microsoftSaleDelayedPublicEvidence =
  delayed-public-evidence
    Basket.microsoftSale20260210
    "transaction date reported as 2026-02-10"
    "public OGE Form 278-T dated 2026-05-08"
    may8Availability
    "later OGE filing pays the reported February transaction; it is not automatically a February public signal"

coinbaseNotInPreDisclosurePublicCut :
  availabilityAt coinbaseSaleDelayedPublicEvidence beforeMay8Disclosure ≡ unavailable
coinbaseNotInPreDisclosurePublicCut = refl

coinbaseInPostDisclosurePublicCut :
  availabilityAt coinbaseSaleDelayedPublicEvidence onOrAfterMay8Disclosure ≡ available
coinbaseInPostDisclosurePublicCut = refl

technologyBasketNotInPreDisclosurePublicCut :
  availabilityAt palantirSaleDelayedPublicEvidence beforeMay8Disclosure ≡ unavailable
  × availabilityAt metaSaleDelayedPublicEvidence beforeMay8Disclosure ≡ unavailable
  × availabilityAt amazonSaleDelayedPublicEvidence beforeMay8Disclosure ≡ unavailable
  × availabilityAt microsoftSaleDelayedPublicEvidence beforeMay8Disclosure ≡ unavailable
technologyBasketNotInPreDisclosurePublicCut = refl , refl , refl , refl

technologyBasketInPostDisclosurePublicCut :
  availabilityAt palantirSaleDelayedPublicEvidence onOrAfterMay8Disclosure ≡ available
  × availabilityAt metaSaleDelayedPublicEvidence onOrAfterMay8Disclosure ≡ available
  × availabilityAt amazonSaleDelayedPublicEvidence onOrAfterMay8Disclosure ≡ available
  × availabilityAt microsoftSaleDelayedPublicEvidence onOrAfterMay8Disclosure ≡ available
technologyBasketInPostDisclosurePublicCut = refl , refl , refl , refl

------------------------------------------------------------------------
-- The OGE reporting-system semantics provide the governing attribution rule:
-- transaction time and public-information time are distinct coordinates.
------------------------------------------------------------------------

ogeSemanticsAnchor : OGE.OGE278TReportingSemantics
ogeSemanticsAnchor = OGE.canonicalOGE278TSemantics

------------------------------------------------------------------------
-- Game-theoretic reading.
--
-- `available` means the identified public artifact may enter a model's public
-- evidence state at that cut.  It does not imply that all players observed it,
-- believed it, or shared a common posterior.  `unavailable` means only that this
-- later filing is not a legitimate source for the earlier public-information
-- cut; some different contemporaneous source could independently pay the same
-- proposition.
------------------------------------------------------------------------

data LaterDisclosureMayBeImportedIntoEarlierPublicSignal : Set where
data PublicAvailabilityMeansEveryPlayerObserved : Set where
data PublicAvailabilityMeansCommonKnowledge : Set where
data PreDisclosureUnavailabilityProvesPrivateKnowledge : Set where

afterTheFactFilingCannotPopulateEarlierPublicCut :
  LaterDisclosureMayBeImportedIntoEarlierPublicSignal → ⊥
afterTheFactFilingCannotPopulateEarlierPublicCut ()

publicAvailabilityDoesNotMeanEveryPlayerObserved :
  PublicAvailabilityMeansEveryPlayerObserved → ⊥
publicAvailabilityDoesNotMeanEveryPlayerObserved ()

publicAvailabilityDoesNotCreateCommonKnowledge :
  PublicAvailabilityMeansCommonKnowledge → ⊥
publicAvailabilityDoesNotCreateCommonKnowledge ()

absenceFromPublicCutDoesNotProvePrivateKnowledge :
  PreDisclosureUnavailabilityProvesPrivateKnowledge → ⊥
absenceFromPublicCutDoesNotProvePrivateKnowledge ()

record TrumpTradePointInTimeInformationBoundary : Set where
  constructor trump-trade-point-in-time-information-boundary
  field
    eventTimeAndDisclosureTimeAreSeparate : Bool
    laterFilingCannotBeBackdatedIntoPublicSignal : Bool
    postDisclosureArtifactMayEnterPublicEvidenceState : Bool
    publicAvailabilityDoesNotMeanUniversalObservation : Bool
    absenceFromPublicEvidenceDoesNotProvePrivateKnowledge : Bool
    contemporaneousIndependentSourceCouldStillPayEarlierAvailability : Bool

canonicalTrumpTradePointInTimeInformationBoundary :
  TrumpTradePointInTimeInformationBoundary
canonicalTrumpTradePointInTimeInformationBoundary =
  trump-trade-point-in-time-information-boundary
    true true true true true true
