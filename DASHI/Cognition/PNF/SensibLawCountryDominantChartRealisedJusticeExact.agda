module DASHI.Cognition.PNF.SensibLawCountryDominantChartRealisedJusticeExact where

open import DASHI.Core.Prelude

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Cognition.PNF.SensibLawRemedyUniversalLegalAlgebraBridgeExact as LegalRemedy

------------------------------------------------------------------------
-- COUNTRY / REALISED JUSTICE AS AN OBSERVER-ADEQUACY PROBLEM
------------------------------------------------------------------------

administrativeConsultationCompression :
  Compression.ProjectionInadequacyReceipt
    Remedy.administrativeConsultationObserver
    Remedy.communityConsultationOutcome
administrativeConsultationCompression =
  Compression.projection-inadequacy-receipt
    Compression.administrativeClassificationCompression
    "administrative consultation observable"
    "community-defined consultation/remedy outcome consumer"
    "the same administrative consultation surface can coexist with distinct community-defined outcomes"
    Remedy.administrativeConsultationWitness
    true refl
    false refl
    false refl
    false refl

administrativeConsultationCannotCarryCommunityOutcome :
  INF.FactorsThrough
    Remedy.administrativeConsultationObserver
    Remedy.communityConsultationOutcome → ⊥
administrativeConsultationCannotCarryCommunityOutcome =
  Compression.projectionCannotFactorTarget administrativeConsultationCompression

administrativeConsultationRelabellingCannotRepairOutcome :
  ∀ {Recharted : Set} →
  (rechart : Remedy.AdministrativeConsultationObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Remedy.administrativeConsultationObserver state))
    Remedy.communityConsultationOutcome → ⊥
administrativeConsultationRelabellingCannotRepairOutcome =
  Compression.projectionCannotBeRepairedByPostcomposition
    administrativeConsultationCompression

------------------------------------------------------------------------
-- Legal availability and realised justice remain sequential consumers.
------------------------------------------------------------------------

record LegalOperationalJusticeBoundary : Set where
  constructor legal-operational-justice-boundary
  field
    legalAvailabilityEqualsRealizedJustice : Bool
    legalAvailabilityEqualsRealizedJusticeIsFalse :
      legalAvailabilityEqualsRealizedJustice ≡ false
    doctrinalCorrectionEqualsLandReturn : Bool
    doctrinalCorrectionEqualsLandReturnIsFalse :
      doctrinalCorrectionEqualsLandReturn ≡ false
    stateImplementationReportEqualsCommunityDefinedSuccess : Bool
    stateImplementationReportEqualsCommunityDefinedSuccessIsFalse :
      stateImplementationReportEqualsCommunityDefinedSuccess ≡ false
    realisedEffectMustRemainIndependentCoordinate : Bool
    realisedEffectMustRemainIndependentCoordinateIsTrue :
      realisedEffectMustRemainIndependentCoordinate ≡ true
    correctionResponseMustRemainIndependentCoordinate : Bool
    correctionResponseMustRemainIndependentCoordinateIsTrue :
      correctionResponseMustRemainIndependentCoordinate ≡ true

canonicalLegalOperationalJusticeBoundary : LegalOperationalJusticeBoundary
canonicalLegalOperationalJusticeBoundary =
  legal-operational-justice-boundary
    false refl
    false refl
    false refl
    true refl
    true refl

legalAvailabilityDoesNotEqualRealisation :
  LegalRemedy.LegalAvailabilityAutomaticallyMeansRealisedRemedy → ⊥
legalAvailabilityDoesNotEqualRealisation =
  LegalRemedy.availabilityDoesNotEqualRealisation

countryDoctrinalCorrectionStillDoesNotEqualMaterialRepair :
  Country.DoctrinalCorrectionEqualsMaterialRepair → ⊥
countryDoctrinalCorrectionStillDoesNotEqualMaterialRepair =
  Country.doctrinalCorrectionDoesNotEqualMaterialRepair

stateReportStillDoesNotEqualCommunitySuccess :
  Country.StateImplementationReportEqualsCommunityDefinedSuccess → ⊥
stateReportStillDoesNotEqualCommunitySuccess =
  Country.stateReportDoesNotEqualCommunityDefinedSuccess

------------------------------------------------------------------------
-- POSIWID-style operational state remains plural and Two-Eyed.
------------------------------------------------------------------------

communityOutcomeCanReopenImplementation :
  Country.communityOutcomeCanReopenImplementation
    Country.canonicalBraidedRemedyAssessment ≡ true
communityOutcomeCanReopenImplementation = refl

stateObservationDoesNotExhaustCommunityOutcome :
  Country.stateObservationExhaustsCommunityOutcome
    Country.canonicalBraidedRemedyAssessment ≡ false
stateObservationDoesNotExhaustCommunityOutcome = refl

sharedObservationDoesNotFuseAuthority :
  Country.sharedObservationFusesAuthority
    Country.canonicalBraidedRemedyAssessment ≡ false
sharedObservationDoesNotFuseAuthority = refl

------------------------------------------------------------------------
-- Consumer routing: the residual names the missing producer, not a nicer label.
------------------------------------------------------------------------

landResidualStillRoutesToLandControl :
  Country.producerFor Country.landAndCountryControl
  ≡ Country.landReturnOrControlProducer
landResidualStillRoutesToLandControl = refl

compensationResidualStillRoutesToExecution :
  Country.producerFor Country.compensationAndReparation
  ≡ Country.compensationExecutionProducer
compensationResidualStillRoutesToExecution = refl

record CountryCompressionBoundary : Set where
  constructor country-compression-boundary
  field
    betterAdministrativeMetricCreatesLandReturn : Bool
    betterAdministrativeMetricCreatesLandReturnIsFalse :
      betterAdministrativeMetricCreatesLandReturn ≡ false
    recognitionLabelCreatesEqualSovereignRelation : Bool
    recognitionLabelCreatesEqualSovereignRelationIsFalse :
      recognitionLabelCreatesEqualSovereignRelation ≡ false
    implementationActivityClosesReparationByDefault : Bool
    implementationActivityClosesReparationByDefaultIsFalse :
      implementationActivityClosesReparationByDefault ≡ false

canonicalCountryCompressionBoundary : CountryCompressionBoundary
canonicalCountryCompressionBoundary =
  country-compression-boundary false refl false refl false refl
