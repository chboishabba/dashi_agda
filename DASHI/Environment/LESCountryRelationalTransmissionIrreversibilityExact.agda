module DASHI.Environment.LESCountryRelationalTransmissionIrreversibilityExact where

------------------------------------------------------------------------
-- COUNTRY RELATIONAL TRANSMISSION / IRREVERSIBILITY
--
-- Refines the coarse `countryRelationContinuity` / `culturalContinuity`
-- coordinates in LESCountryExternalityRealisationExact.  The richer fibre is a
-- DASHI reconstruction informed by existing source-bounded PatternMind,
-- Indigenous Knowledge / Story / Two-Eyed Seeing, and primary-source legal
-- receipts.  No source is attributed this exact coordinate list.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESCountryExternalityRealisationExact as LESCountry
import DASHI.Culture.PatternMindReciprocityLoveBridge as PatternMind
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawCountryRelationalIrreversibilitySourceAtlasExact as Sources

------------------------------------------------------------------------
-- The relational fibre is not reducible to a single cultural-continuity bit.
------------------------------------------------------------------------

data CountryRelationalCoordinate : Set where
  accessToSpecificCountry : CountryRelationalCoordinate
  placeSpecificKnowledgeTransmission : CountryRelationalCoordinate
  storyLawLanguageTransmission : CountryRelationalCoordinate
  kinshipAndAncestralContinuity : CountryRelationalCoordinate
  ceremonialPracticeContinuity : CountryRelationalCoordinate
  custodialResponsibilityCapacity : CountryRelationalCoordinate
  permissionAndAuthorityContinuity : CountryRelationalCoordinate
  intergenerationalTeachingChain : CountryRelationalCoordinate
  ecologicalMemoryOfPlace : CountryRelationalCoordinate
  reciprocalObligationPractice : CountryRelationalCoordinate
  collectiveDecisionAuthority : CountryRelationalCoordinate
  communityReconstitutionCapacity : CountryRelationalCoordinate
  historicalTransmissionOccurrence : CountryRelationalCoordinate
  irreversibleRelationalLoss : CountryRelationalCoordinate


data RelationalCoordinateState : Set where
  relationIntact : RelationalCoordinateState
  relationImpaired : RelationalCoordinateState
  transmissionInterrupted : RelationalCoordinateState
  reconstitutionInProgress : RelationalCoordinateState
  historicallyMissed : RelationalCoordinateState
  permanentlyLostInSourceRecord : RelationalCoordinateState
  sourceUnresolved : RelationalCoordinateState


record CountryRelationalOutcome : Set where
  constructor country-relational-outcome
  field
    stateOf : CountryRelationalCoordinate → RelationalCoordinateState
    outcomeReference : String
    sourceSpecificWorldClaim : Bool
    sourceSpecificWorldClaimIsFalse : sourceSpecificWorldClaim ≡ false

open CountryRelationalOutcome public

------------------------------------------------------------------------
-- PatternMind/IK cross-pollination: relation/practice/story/place are distinct
-- carrier coordinates, not decorative metadata around a detached proposition.
------------------------------------------------------------------------

patternMindRelationBeforeObject :
  PatternMind.relationBeforeObjectTracked
    PatternMind.canonicalPatternMindReciprocityLoveBridge ≡ true
patternMindRelationBeforeObject = refl

patternMindRepeatedAttentionCompilesChart :
  PatternMind.repeatedAttentionCompilesChart
    PatternMind.canonicalPatternMindReciprocityLoveBridge ≡ true
patternMindRepeatedAttentionCompilesChart = refl

indigenousKnowledgeCarrierTracksPlace : IK.PlaceContext
indigenousKnowledgeCarrierTracksPlace = IK.place IK.indigenousMedicinalStoryCarrier

indigenousKnowledgeCarrierTracksCustodialRelation : IK.PeopleRelation
indigenousKnowledgeCarrierTracksCustodialRelation =
  IK.peopleRelation IK.indigenousMedicinalStoryCarrier

indigenousKnowledgeCarrierTracksObligation : IK.ObligationStatus
indigenousKnowledgeCarrierTracksObligation =
  IK.obligation IK.indigenousMedicinalStoryCarrier

indigenousKnowledgeCarrierTracksTransmission : IK.TransmissionMode
indigenousKnowledgeCarrierTracksTransmission =
  IK.transmission IK.indigenousMedicinalStoryCarrier

extractedPropositionCannotRecoverPlaceRelationAuthorityOrObligation :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionCannotRecoverPlaceRelationAuthorityOrObligation =
  IK.propositionCannotRecoverAuthority

sharedObservationDoesNotFuseKnowledgeHistories :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationDoesNotFuseKnowledgeHistories = refl

------------------------------------------------------------------------
-- Existing LES carrier remains useful, but the two old continuity coordinates
-- are only coarse addresses into this richer relation/transmission fibre.
------------------------------------------------------------------------

data CoarseCountryContinuitySurface : Set where
  sameCoarseContinuity : CoarseCountryContinuitySurface

data FineRelationalState : Set where
  accessWithoutTransmission : FineRelationalState
  accessWithLivingTransmission : FineRelationalState


data TransmissionState : Set where
  transmissionAbsent : TransmissionState
  transmissionLiving : TransmissionState

coarseContinuityObserver : FineRelationalState → CoarseCountryContinuitySurface
coarseContinuityObserver _ = sameCoarseContinuity

transmissionState : FineRelationalState → TransmissionState
transmissionState accessWithoutTransmission = transmissionAbsent
transmissionState accessWithLivingTransmission = transmissionLiving

transmissionDiffers :
  transmissionState accessWithoutTransmission
  ≡ transmissionState accessWithLivingTransmission → ⊥
transmissionDiffers ()

coarseContinuityCannotRecoverTransmission :
  INF.FactorsThrough coarseContinuityObserver transmissionState → ⊥
coarseContinuityCannotRecoverTransmission =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      accessWithoutTransmission accessWithLivingTransmission refl transmissionDiffers)

------------------------------------------------------------------------
-- Temporal irreversibility is carefully scoped.
--
-- A missed historical transmission event cannot later be made to have occurred
-- at its original time.  That does NOT imply culture is frozen, that future
-- reconstitution is impossible, or that every damaged relation is unrecoverable.
------------------------------------------------------------------------

data TransmissionMoment : Set where
  transmissionOccurredAtHistoricalMoment : TransmissionMoment
  transmissionMissedAtHistoricalMoment : TransmissionMoment
  laterReconstitutionOccurred : TransmissionMoment


data HistoricalOccurrenceState : Set where
  occurredHistorically : HistoricalOccurrenceState
  didNotOccurHistorically : HistoricalOccurrenceState

data FutureRelationalCapacity : Set where
  futureReconstitutionOpen : FutureRelationalCapacity
  futureReconstitutionBlocked : FutureRelationalCapacity

historicalOccurrence : TransmissionMoment → HistoricalOccurrenceState
historicalOccurrence transmissionOccurredAtHistoricalMoment = occurredHistorically
historicalOccurrence transmissionMissedAtHistoricalMoment = didNotOccurHistorically
historicalOccurrence laterReconstitutionOccurred = didNotOccurHistorically

futureCapacity : TransmissionMoment → FutureRelationalCapacity
futureCapacity transmissionOccurredAtHistoricalMoment = futureReconstitutionOpen
futureCapacity transmissionMissedAtHistoricalMoment = futureReconstitutionOpen
futureCapacity laterReconstitutionOccurred = futureReconstitutionOpen

laterRepairDoesNotRetroactivelyCreateMissedHistoricalTransmission :
  historicalOccurrence transmissionMissedAtHistoricalMoment
  ≡ historicalOccurrence laterReconstitutionOccurred
laterRepairDoesNotRetroactivelyCreateMissedHistoricalTransmission = refl

missedHistoryDoesNotProveFutureReconstitutionImpossible :
  futureCapacity transmissionMissedAtHistoricalMoment ≡ futureReconstitutionOpen
missedHistoryDoesNotProveFutureReconstitutionImpossible = refl

------------------------------------------------------------------------
-- Source-role-specific legal/institutional propositions.
------------------------------------------------------------------------

data RelationalSourceRole : Set where
  highCourtAcceptedFinding : RelationalSourceRole
  humanRightsInquiryFinding : RelationalSourceRole
  internationalDeclarationProvision : RelationalSourceRole
  dashiInterpretiveBridge : RelationalSourceRole


record RelationalSourceProposition : Set where
  constructor relational-source-proposition
  field
    sourceRole : RelationalSourceRole
    sourceReference : String
    proposition : String
    pinpoint : String
    sourceSaysPermanentOrIntergenerational : Bool
    sourceSaysCustodialResponsibility : Bool
    dashiUniversalisedBeyondSource : Bool
    dashiUniversalisedBeyondSourceIsFalse : dashiUniversalisedBeyondSource ≡ false

open RelationalSourceProposition public

griffithsPermanentIntergenerationalLoss : RelationalSourceProposition
griffithsPermanentIntergenerationalLoss = relational-source-proposition
  highCourtAcceptedFinding
  "Northern Territory v Griffiths [2019] HCA 7"
  "The accepted cultural-loss findings included permanent and intergenerational loss arising from harm to Country and differing according to connection, age, ritual knowledge and responsibility."
  "[230]; see also [180]-[206]"
  true
  true
  false refl

griffithsCustodialResponsibility : RelationalSourceProposition
griffithsCustodialResponsibility = relational-source-proposition
  highCourtAcceptedFinding
  "Northern Territory v Griffiths [2019] HCA 7"
  "The Court recorded accepted evidence of a duty and concern to look after Country and a sense of failed responsibility under traditional laws and customs when Country was harmed."
  "[194], [200]-[206]"
  true
  true
  false refl

bringingThemHomeDestroyedCulturalLinks : RelationalSourceProposition
bringingThemHomeDestroyedCulturalLinks = relational-source-proposition
  humanRightsInquiryFinding
  "Bringing them Home (HREOC, 1997)"
  "Forcible removal destroyed cultural links and deprived many people of language, cultural knowledge, traditional responsibilities, kinship and land connection, with intergenerational effects."
  "Chapter 11; Chapter 14; Recommendations 11-14"
  true
  true
  false refl

undripCountryFutureGenerationRelation : RelationalSourceProposition
undripCountryFutureGenerationRelation = relational-source-proposition
  internationalDeclarationProvision
  "UN Declaration on the Rights of Indigenous Peoples"
  "Indigenous peoples have rights to maintain and strengthen their distinctive spiritual relationship with lands, territories, waters and resources and to uphold responsibilities to future generations."
  "Article 25; related arts 26, 28 and 31"
  false
  true
  false refl

------------------------------------------------------------------------
-- Place-specific non-fungibility: another parcel is not automatically an
-- equivalent substitute for a relation to this Country.
------------------------------------------------------------------------

data PlaceRelation : Set where
  relationToThisCountry : PlaceRelation
  relationToDifferentCountry : PlaceRelation

data GenericLandArea : Set where
  equalArea : GenericLandArea

areaObserver : PlaceRelation → GenericLandArea
areaObserver _ = equalArea

data CountryAttachment : Set where
  thisCountryAttachment : CountryAttachment
  differentCountryAttachment : CountryAttachment

attachment : PlaceRelation → CountryAttachment
attachment relationToThisCountry = thisCountryAttachment
attachment relationToDifferentCountry = differentCountryAttachment

attachmentDiffers :
  attachment relationToThisCountry ≡ attachment relationToDifferentCountry → ⊥
attachmentDiffers ()

equalLandAreaCannotRecoverCountryAttachment :
  INF.FactorsThrough areaObserver attachment → ⊥
equalLandAreaCannotRecoverCountryAttachment =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      relationToThisCountry relationToDifferentCountry refl attachmentDiffers)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record CountryRelationalIrreversibilityBoundary : Set where
  constructor country-relational-irreversibility-boundary
  field
    culturalContinuityBitExhaustsRelationalContinuity : Bool
    culturalContinuityBitExhaustsRelationalContinuityIsFalse :
      culturalContinuityBitExhaustsRelationalContinuity ≡ false
    accessToLandEqualsLivingTransmission : Bool
    accessToLandEqualsLivingTransmissionIsFalse : accessToLandEqualsLivingTransmission ≡ false
    compensationRestoresMissedHistoricalTransmissionRetroactively : Bool
    compensationRestoresMissedHistoricalTransmissionRetroactivelyIsFalse :
      compensationRestoresMissedHistoricalTransmissionRetroactively ≡ false
    permanentHistoricalLossMeansFutureCultureCannotReconstitute : Bool
    permanentHistoricalLossMeansFutureCultureCannotReconstituteIsFalse :
      permanentHistoricalLossMeansFutureCultureCannotReconstitute ≡ false
    equivalentAreaOfLandIsEquivalentCountryRelation : Bool
    equivalentAreaOfLandIsEquivalentCountryRelationIsFalse :
      equivalentAreaOfLandIsEquivalentCountryRelation ≡ false
    custodialResponsibilityIsOnlyEconomicUseRight : Bool
    custodialResponsibilityIsOnlyEconomicUseRightIsFalse :
      custodialResponsibilityIsOnlyEconomicUseRight ≡ false
    sourceSpecificLossFindingBecomesUniversalIndigenousOntology : Bool
    sourceSpecificLossFindingBecomesUniversalIndigenousOntologyIsFalse :
      sourceSpecificLossFindingBecomesUniversalIndigenousOntology ≡ false

open CountryRelationalIrreversibilityBoundary public

canonicalCountryRelationalIrreversibilityBoundary :
  CountryRelationalIrreversibilityBoundary
canonicalCountryRelationalIrreversibilityBoundary =
  country-relational-irreversibility-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
