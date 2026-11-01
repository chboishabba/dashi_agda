module DASHI.Cognition.PNF.SensibLawCountryDominantChartRealisedJusticeV02Exact where

open import DASHI.Core.Prelude

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Cognition.PNF.SensibLawRemedyUniversalLegalAlgebraBridgeExact as LegalRemedy

------------------------------------------------------------------------
-- Corrected V02 owner.  The earlier experimental adapter remains unimported;
-- this owner uses the exact existing consultation API and witness coordinates.
------------------------------------------------------------------------

administrativeConsultationWitness :
  INF.NonFactorabilityWitness
    Remedy.administrativeConsultationObserver
    Remedy.communityConsultationOutcome
administrativeConsultationWitness =
  INF.nonFactorabilityWitness
    Remedy.extractiveMeetingState
    Remedy.authorityBearingCoDesignState
    refl
    Remedy.consultationOutcomesDiffer

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
    administrativeConsultationWitness
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
  (rechart : Remedy.AdministrativeConsultationSurface → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Remedy.administrativeConsultationObserver state))
    Remedy.communityConsultationOutcome → ⊥
administrativeConsultationRelabellingCannotRepairOutcome =
  Compression.projectionCannotBeRepairedByPostcomposition
    administrativeConsultationCompression

------------------------------------------------------------------------
-- Legal availability / doctrinal correction remain separate from realised
-- Country/remedy coordinates.
------------------------------------------------------------------------

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

stateObservationDoesNotExhaustCommunityOutcome :
  Country.stateObservationExhaustsCommunityOutcome
    Country.canonicalBraidedRemedyAssessment ≡ false
stateObservationDoesNotExhaustCommunityOutcome = refl

sharedObservationDoesNotFuseAuthority :
  Country.sharedObservationFusesAuthority
    Country.canonicalBraidedRemedyAssessment ≡ false
sharedObservationDoesNotFuseAuthority = refl

communityOutcomeCanReopenImplementation :
  Country.communityOutcomeCanReopenImplementation
    Country.canonicalBraidedRemedyAssessment ≡ true
communityOutcomeCanReopenImplementation = refl

------------------------------------------------------------------------
-- Reverse route names a materially missing producer rather than permitting a
-- better label on the old administrative surface to masquerade as repair.
------------------------------------------------------------------------

landResidualStillRoutesToLandControl :
  Country.producerFor Country.landAndCountryControl
  ≡ Country.landReturnOrControlProducer
landResidualStillRoutesToLandControl = refl

compensationResidualStillRoutesToExecution :
  Country.producerFor Country.compensationAndReparation
  ≡ Country.compensationExecutionProducer
compensationResidualStillRoutesToExecution = refl

record CountryCompressionV02Boundary : Set where
  constructor country-compression-v02-boundary
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
    materialResidualNeedsMaterialProducer : Bool
    materialResidualNeedsMaterialProducerIsTrue :
      materialResidualNeedsMaterialProducer ≡ true

canonicalCountryCompressionV02Boundary : CountryCompressionV02Boundary
canonicalCountryCompressionV02Boundary =
  country-compression-v02-boundary false refl false refl false refl true refl
