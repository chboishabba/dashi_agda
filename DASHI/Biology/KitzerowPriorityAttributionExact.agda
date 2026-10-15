module DASHI.Biology.KitzerowPriorityAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4SourceAtlasExact as Sources

data ChronologyRelation : Set where
  kitzerowClearlyEarlier : ChronologyRelation
  comparisonClearlyEarlier : ChronologyRelation
  samePeriodUnresolved : ChronologyRelation
  startDateUnknown : ChronologyRelation

data ExposureEvidence : Set where
  noExposureEvidenceFound : ExposureEvidence
  publicAvailabilityOnly : ExposureEvidence
  originatorReportedContact : ExposureEvidence
  publicContactArtifactInspected : ExposureEvidence
  institutionalAcknowledgementInspected : ExposureEvidence
  directCitationInPaper : ExposureEvidence
  citationAbsentInInspectedText : ExposureEvidence
  exposureUndetermined : ExposureEvidence

data DerivationStatus : Set where
  independentDerivationSupported : DerivationStatus
  derivationUndetermined : DerivationStatus
  directUseDocumented : DerivationStatus

record AttributionAssessment : Set where
  constructor attributionAssessment
  field
    comparisonLabel : String
    chronology : ChronologyRelation
    exposure : ExposureEvidence
    derivation : DerivationStatus
    directContactVerified : Bool
    directContactVerifiedIsFalseWhenReportedOnly : directContactVerified ≡ false
    legalInfringementConcluded : Bool
    legalInfringementConcludedIsFalse : legalInfringementConcluded ≡ false
    reading : String

open AttributionAssessment public

canonicalNomuraAttribution : AttributionAssessment
canonicalNomuraAttribution =
  attributionAssessment
    "Nomura / Japan translational-vulnerability study"
    comparisonClearlyEarlier
    noExposureEvidenceFound
    independentDerivationSupported
    false refl
    false refl
    "reported 2022 preprint chronology predates the relevant Kitzerow articulation; bounded convergence is therefore treated as an independence-supporting control"

canonicalStanfordAttribution : AttributionAssessment
canonicalStanfordAttribution =
  attributionAssessment
    "Stanford reticular-thalamus / Z944 study"
    kitzerowClearlyEarlier
    originatorReportedContact
    derivationUndetermined
    false refl
    false refl
    "Kitzerow publicly reports direct Stanford Neurodiversity Project contact on 2023-11-27; underlying correspondence has not yet been independently acquired in this tranche"

stanfordDirectContactVerified : AttributionAssessment → Bool
stanfordDirectContactVerified = directContactVerified

canonicalBrazilReviewAttribution : AttributionAssessment
canonicalBrazilReviewAttribution =
  attributionAssessment
    "Brazil BH4 ASD systematic review"
    kitzerowClearlyEarlier
    originatorReportedContact
    derivationUndetermined
    false refl
    false refl
    "post-publication author/journal contact is originator-reported here; chronology, exposure and derivation remain separate"

canonicalItalyAttribution : AttributionAssessment
canonicalItalyAttribution =
  attributionAssessment
    "Italy connectivity-subtype comparison"
    kitzerowClearlyEarlier
    publicAvailabilityOnly
    derivationUndetermined
    false refl
    false refl
    "structural convergence plus public availability does not establish access or derivation"

canonicalMelilloAttribution : AttributionAssessment
canonicalMelilloAttribution =
  attributionAssessment
    "Melillo developmental neuroimmune cascade"
    kitzerowClearlyEarlier
    publicAvailabilityOnly
    derivationUndetermined
    false refl
    false refl
    "model-to-model structural similarity is retained without inferring use of Kitzerow's work"

canonicalIACCAttribution : AttributionAssessment
canonicalIACCAttribution =
  attributionAssessment
    "IACC developmental-systems material"
    kitzerowClearlyEarlier
    originatorReportedContact
    derivationUndetermined
    false refl
    false refl
    "reported MedMaps/IACC exposure chain is not upgraded without the underlying contact/acknowledgement artifact"

------------------------------------------------------------------------
-- Non-implication firewalls.  These are explicit proposition carriers rather
-- than scalar plagiarism scoring.
------------------------------------------------------------------------

record AttributionFirewall : Set where
  constructor attributionFirewall
  field
    earlierDoesNotProveCopying : Bool
    contactDoesNotProveUse : Bool
    publicAvailabilityDoesNotProveAccess : Bool
    accessDoesNotProveDerivation : Bool
    derivationDoesNotProveInfringement : Bool
    scientificSupportDoesNotProvePriority : Bool
    priorityDoesNotProveScientificCorrectness : Bool
    citationAbsenceDoesNotProvePlagiarism : Bool
    overlapScoreDoesNotCreateLegalConclusion : Bool

open AttributionFirewall public

canonicalAttributionFirewall : AttributionFirewall
canonicalAttributionFirewall =
  attributionFirewall true true true true true true true true true

contactDoesNotProveUse : Bool
contactDoesNotProveUse = AttributionFirewall.contactDoesNotProveUse canonicalAttributionFirewall

citationAbsenceDoesNotProvePlagiarism : Bool
citationAbsenceDoesNotProvePlagiarism = AttributionFirewall.citationAbsenceDoesNotProvePlagiarism canonicalAttributionFirewall
