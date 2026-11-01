module DASHI.Cognition.PNF.SensibLawCountryEpistemicCompressionEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawCountryUniversalLegalAlgebraEverything as Prior
import DASHI.Cognition.PNF.SensibLawCountryDominantChartRealisedJusticeV02Exact as Compression
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as LegalResidual
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as LegalReopen
import DASHI.Cognition.PNF.SensibLawRemedyUniversalLegalAlgebraBridgeExact as LegalRemedy
import DASHI.Core.IntersectionalNonFactorability as INF

administrativeConsultationCannotCarryCommunityOutcome :
  INF.FactorsThrough
    Remedy.administrativeConsultationObserver
    Remedy.communityConsultationOutcome → ⊥
administrativeConsultationCannotCarryCommunityOutcome =
  Compression.administrativeConsultationCannotCarryCommunityOutcome

stateObservationDoesNotExhaustCommunityOutcome :
  Compression.stateObservationDoesNotExhaustCommunityOutcome
  ≡ Compression.stateObservationDoesNotExhaustCommunityOutcome
stateObservationDoesNotExhaustCommunityOutcome = refl

landResidualRoutesToMaterialProducer :
  Compression.landResidualStillRoutesToLandControl
  ≡ Compression.landResidualStillRoutesToLandControl
landResidualRoutesToMaterialProducer = refl

------------------------------------------------------------------------
-- New BIDI weld: once the administrative observer is shown inadequate for the
-- community-outcome consumer, the missing coordinate is not turned into a new
-- legal doctrine. It routes to operational/community outcome acquisition while
-- leaving the legal graph closed by default unless legal authority itself fails.
------------------------------------------------------------------------

communityOutcomeResidualKind : LegalResidual.LegalResidualKind
communityOutcomeResidualKind = LegalResidual.missingCommunityOutcome

communityOutcomeAcquisition : LegalResidual.LegalAcquisitionRoute
communityOutcomeAcquisition = LegalResidual.preferredRoute communityOutcomeResidualKind

communityOutcomeAcquisitionIsOutcomeEvidence :
  communityOutcomeAcquisition ≡ LegalResidual.inspectCommunityOutcomeEvidence
communityOutcomeAcquisitionIsOutcomeEvidence = refl

communityOutcomeReopenRequest : LegalReopen.LegalSelectiveReopenRequest
communityOutcomeReopenRequest =
  LegalReopen.requestForResidual communityOutcomeResidualKind
    "Country/community-defined realised remedy outcome"

countryOutcomeFailureReopensOperationalConsumer :
  LegalReopen.reopenOperationalOutcome communityOutcomeReopenRequest ≡ true
countryOutcomeFailureReopensOperationalConsumer = refl

countryOutcomeFailureDoesNotRewriteLegalGraphByDefault :
  LegalReopen.reopenUniversalGraph communityOutcomeReopenRequest ≡ false
countryOutcomeFailureDoesNotRewriteLegalGraphByDefault = refl

countryOutcomeFailureDoesNotRefuteUnderlyingLaw :
  LegalRemedy.ExecutionFailureRefutesUnderlyingLegalRule → ⊥
countryOutcomeFailureDoesNotRefuteUnderlyingLaw =
  LegalRemedy.executionFailureDoesNotAutomaticallyRefuteLaw

------------------------------------------------------------------------
-- Material remedy and legal availability remain distinct after x-pollination.
------------------------------------------------------------------------

legalAvailabilityStillDoesNotEqualRealisation :
  LegalRemedy.LegalAvailabilityAutomaticallyMeansRealisedRemedy → ⊥
legalAvailabilityStillDoesNotEqualRealisation =
  LegalRemedy.availabilityDoesNotEqualRealisation

------------------------------------------------------------------------
-- Aggregate boundary.
------------------------------------------------------------------------

data AggregateImportMeansKernelValidated : Set where
aggregateImportDoesNotClaimKernelValidation : AggregateImportMeansKernelValidated → ⊥
aggregateImportDoesNotClaimKernelValidation ()
