module DASHI.Cognition.PNF.SensibLawCountryOperationalRevisionParaconsistentExact where

------------------------------------------------------------------------
-- COUNTRY OPERATIONAL REVISION / PARACONSISTENT HISTORY
--
-- Historical legal/reform events are append-only evidence carriers.  Later
-- material/community evidence may revise the operational justice conclusion
-- without deleting the earlier event.  Conflicting cross-order support remains
-- paraconsistent and does not explode the operational audit.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.RequiredAxisSupportSquareExact as Square
import DASHI.Cognition.PNF.SensibLawCountryPluralEpistemicOperationalAuditExact as CountryAudit
import DASHI.Cognition.PNF.SensibLawMaboTwoOrderParaconsistentSpaceExact as Para
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country

------------------------------------------------------------------------
-- Finite Country/reform history.
------------------------------------------------------------------------

data CountryEvidence : Set where
  maboDoctrinalCorrectionEvidence
  stateImplementationActivityEvidence
  communityMaterialResidualEvidence
  communityAuthorityResidualEvidence
  correctionLoopResidualEvidence
  : CountryEvidence

data CountryHistory : Set where
  doctrinalCorrectionHistory
  correctionPlusImplementationHistory
  correctionPlusImplementationAndMaterialResidualHistory
  : CountryHistory

data CountryOperationalConclusion : Set where
  doctrinalCorrectionRecognised
  partialOperationalCorrectionRecognised
  materialClosureReopened
  : CountryOperationalConclusion

data CountryContains : CountryEvidence → CountryHistory → Set where
  maboInDoctrinalHistory :
    CountryContains maboDoctrinalCorrectionEvidence doctrinalCorrectionHistory
  maboInImplementationHistory :
    CountryContains maboDoctrinalCorrectionEvidence correctionPlusImplementationHistory
  implementationInImplementationHistory :
    CountryContains stateImplementationActivityEvidence correctionPlusImplementationHistory
  maboInResidualHistory :
    CountryContains maboDoctrinalCorrectionEvidence correctionPlusImplementationAndMaterialResidualHistory
  implementationInResidualHistory :
    CountryContains stateImplementationActivityEvidence correctionPlusImplementationAndMaterialResidualHistory
  materialResidualInResidualHistory :
    CountryContains communityMaterialResidualEvidence correctionPlusImplementationAndMaterialResidualHistory
  authorityResidualInResidualHistory :
    CountryContains communityAuthorityResidualEvidence correctionPlusImplementationAndMaterialResidualHistory
  correctionResidualInResidualHistory :
    CountryContains correctionLoopResidualEvidence correctionPlusImplementationAndMaterialResidualHistory

appendCountryEvidence : CountryHistory → CountryEvidence → CountryHistory
appendCountryEvidence doctrinalCorrectionHistory maboDoctrinalCorrectionEvidence = doctrinalCorrectionHistory
appendCountryEvidence doctrinalCorrectionHistory stateImplementationActivityEvidence = correctionPlusImplementationHistory
appendCountryEvidence doctrinalCorrectionHistory _ = correctionPlusImplementationAndMaterialResidualHistory
appendCountryEvidence correctionPlusImplementationHistory communityMaterialResidualEvidence = correctionPlusImplementationAndMaterialResidualHistory
appendCountryEvidence correctionPlusImplementationHistory communityAuthorityResidualEvidence = correctionPlusImplementationAndMaterialResidualHistory
appendCountryEvidence correctionPlusImplementationHistory correctionLoopResidualEvidence = correctionPlusImplementationAndMaterialResidualHistory
appendCountryEvidence correctionPlusImplementationHistory _ = correctionPlusImplementationHistory
appendCountryEvidence correctionPlusImplementationAndMaterialResidualHistory _ =
  correctionPlusImplementationAndMaterialResidualHistory

persistCountryEvidence :
  (history : CountryHistory) →
  (old new : CountryEvidence) →
  CountryContains old history →
  CountryContains old (appendCountryEvidence history new)
persistCountryEvidence doctrinalCorrectionHistory maboDoctrinalCorrectionEvidence
  maboDoctrinalCorrectionEvidence maboInDoctrinalHistory = maboInDoctrinalHistory
persistCountryEvidence doctrinalCorrectionHistory maboDoctrinalCorrectionEvidence
  stateImplementationActivityEvidence maboInDoctrinalHistory = maboInImplementationHistory
persistCountryEvidence doctrinalCorrectionHistory maboDoctrinalCorrectionEvidence
  communityMaterialResidualEvidence maboInDoctrinalHistory = maboInResidualHistory
persistCountryEvidence doctrinalCorrectionHistory maboDoctrinalCorrectionEvidence
  communityAuthorityResidualEvidence maboInDoctrinalHistory = maboInResidualHistory
persistCountryEvidence doctrinalCorrectionHistory maboDoctrinalCorrectionEvidence
  correctionLoopResidualEvidence maboInDoctrinalHistory = maboInResidualHistory
persistCountryEvidence correctionPlusImplementationHistory maboDoctrinalCorrectionEvidence
  communityMaterialResidualEvidence maboInImplementationHistory = maboInResidualHistory
persistCountryEvidence correctionPlusImplementationHistory maboDoctrinalCorrectionEvidence
  communityAuthorityResidualEvidence maboInImplementationHistory = maboInResidualHistory
persistCountryEvidence correctionPlusImplementationHistory maboDoctrinalCorrectionEvidence
  correctionLoopResidualEvidence maboInImplementationHistory = maboInResidualHistory
persistCountryEvidence correctionPlusImplementationHistory maboDoctrinalCorrectionEvidence
  maboDoctrinalCorrectionEvidence maboInImplementationHistory = maboInImplementationHistory
persistCountryEvidence correctionPlusImplementationHistory maboDoctrinalCorrectionEvidence
  stateImplementationActivityEvidence maboInImplementationHistory = maboInImplementationHistory
persistCountryEvidence correctionPlusImplementationHistory stateImplementationActivityEvidence
  communityMaterialResidualEvidence implementationInImplementationHistory = implementationInResidualHistory
persistCountryEvidence correctionPlusImplementationHistory stateImplementationActivityEvidence
  communityAuthorityResidualEvidence implementationInImplementationHistory = implementationInResidualHistory
persistCountryEvidence correctionPlusImplementationHistory stateImplementationActivityEvidence
  correctionLoopResidualEvidence implementationInImplementationHistory = implementationInResidualHistory
persistCountryEvidence correctionPlusImplementationHistory stateImplementationActivityEvidence
  maboDoctrinalCorrectionEvidence implementationInImplementationHistory = implementationInImplementationHistory
persistCountryEvidence correctionPlusImplementationHistory stateImplementationActivityEvidence
  stateImplementationActivityEvidence implementationInImplementationHistory = implementationInImplementationHistory
persistCountryEvidence correctionPlusImplementationAndMaterialResidualHistory _ _ receipt = receipt

countryConclusion : CountryHistory → CountryOperationalConclusion
countryConclusion doctrinalCorrectionHistory = doctrinalCorrectionRecognised
countryConclusion correctionPlusImplementationHistory = partialOperationalCorrectionRecognised
countryConclusion correctionPlusImplementationAndMaterialResidualHistory = materialClosureReopened

countryEvidenceReference : CountryEvidence → String
countryEvidenceReference maboDoctrinalCorrectionEvidence = "Mabo doctrinal correction evidence carrier"
countryEvidenceReference stateImplementationActivityEvidence = "State implementation/activity evidence carrier"
countryEvidenceReference communityMaterialResidualEvidence = "affected-community/material residual evidence carrier"
countryEvidenceReference communityAuthorityResidualEvidence = "community-authority residual evidence carrier"
countryEvidenceReference correctionLoopResidualEvidence = "correction-loop residual evidence carrier"

countryConclusionReference : CountryOperationalConclusion → String
countryConclusionReference doctrinalCorrectionRecognised = "doctrinal correction recognised"
countryConclusionReference partialOperationalCorrectionRecognised = "partial operational correction recognised"
countryConclusionReference materialClosureReopened = "material closure reopened by later residual evidence"

countryRevisionSystem : Revision.AppendOnlyEvidenceSystem
countryRevisionSystem = Revision.appendOnlyEvidenceSystem
  CountryEvidence CountryHistory CountryOperationalConclusion
  appendCountryEvidence CountryContains persistCountryEvidence
  countryConclusion countryEvidenceReference countryConclusionReference

------------------------------------------------------------------------
-- Exact revision: Mabo remains in history while later material residual reopens
-- the stronger operational-success conclusion.
------------------------------------------------------------------------

partialConclusionDiffersFromReopened :
  partialOperationalCorrectionRecognised ≡ materialClosureReopened → ⊥
partialConclusionDiffersFromReopened ()

maboPersistsAfterMaterialResidual :
  CountryContains maboDoctrinalCorrectionEvidence
    (appendCountryEvidence correctionPlusImplementationHistory communityMaterialResidualEvidence)
maboPersistsAfterMaterialResidual = maboInResidualHistory

countryOperationalRevision : Revision.ConclusionRevision countryRevisionSystem
countryOperationalRevision = Revision.conclusionRevision
  correctionPlusImplementationHistory
  communityMaterialResidualEvidence
  maboDoctrinalCorrectionEvidence
  maboInImplementationHistory
  maboInResidualHistory
  partialOperationalCorrectionRecognised
  materialClosureReopened
  refl refl
  partialConclusionDiffersFromReopened
  "Appending affected-community/material residual evidence preserves Mabo and implementation history while reopening the stronger operational-justice conclusion."

oldCorrectionEvidenceRemainsValidWhileConclusionChanges :
  Revision.oldEvidenceMayRemainValidWhileConsumerConclusionChanges
    Revision.canonicalAppendOnlyEvidenceRevisionBoundary ≡ true
oldCorrectionEvidenceRemainsValidWhileConclusionChanges = refl

appendOnlyHistoryDoesNotForceMonotoneConclusion :
  Revision.moreEvidenceImpliesSameConclusionOnlyStronger
    Revision.canonicalAppendOnlyEvidenceRevisionBoundary ≡ false
appendOnlyHistoryDoesNotForceMonotoneConclusion = refl

------------------------------------------------------------------------
-- Current Country operational snapshot remains unclosed independently of the
-- fact that the historical doctrinal correction remains present.
------------------------------------------------------------------------

currentOperationalClosureStillImpossible :
  Operational.FullOperationalClosure CountryAudit.currentCountryOperationalSnapshot → ⊥
currentOperationalClosureStillImpossible = CountryAudit.currentFullOperationalClosureImpossible

maboCorrectionStillHistoricallyReal :
  Country.doctrinalCorrectionOccurred Country.currentCorrectionWithoutFullRepair ≡ true
maboCorrectionStillHistoricallyReal = refl

landReturnStillNotRealisedInCurrentCompiledState :
  Country.landReturnRealised Country.currentCorrectionWithoutFullRepair ≡ false
landReturnStillNotRealisedInCurrentCompiledState = refl

------------------------------------------------------------------------
-- Paraconsistent cross-order space is orthogonal to temporal revision.
------------------------------------------------------------------------

crownSourceExhaustivenessStillConflicting :
  Para.axisState Para.crownExhaustiveSourceAxis ≡ Square.conflictingState
crownSourceExhaustivenessStillConflicting = refl

indigenousOrderIndependenceStillPositive :
  Para.axisState Para.indigenousOrderIndependenceAxis ≡ Square.positiveOnly
indigenousOrderIndependenceStillPositive = refl

colonialLegitimacyStillUnresolved :
  Para.axisState Para.colonialLegitimacyAxis ≡ Square.missingState
colonialLegitimacyStillUnresolved = refl

indigenousCessionStillUnresolved :
  Para.axisState Para.indigenousCessionAxis ≡ Square.missingState
indigenousCessionStillUnresolved = refl

record TemporalParaconsistentBoundary : Set where
  constructor temporal-paraconsistent-boundary
  field
    appendOnlyHistoricalEvidenceRequiresMonotoneJusticeConclusion : Bool
    appendOnlyHistoricalEvidenceRequiresMonotoneJusticeConclusionIsFalse :
      appendOnlyHistoricalEvidenceRequiresMonotoneJusticeConclusion ≡ false
    laterResidualEvidenceDeletesEarlierDoctrinalCorrection : Bool
    laterResidualEvidenceDeletesEarlierDoctrinalCorrectionIsFalse :
      laterResidualEvidenceDeletesEarlierDoctrinalCorrection ≡ false
    crossOrderConflictExplodesTemporalHistory : Bool
    crossOrderConflictExplodesTemporalHistoryIsFalse :
      crossOrderConflictExplodesTemporalHistory ≡ false
    materialReopeningMeansEarlierCorrectionNeverOccurred : Bool
    materialReopeningMeansEarlierCorrectionNeverOccurredIsFalse :
      materialReopeningMeansEarlierCorrectionNeverOccurred ≡ false
    affectedCommunityEvidenceMayReviseStateSuccessAssessment : Bool
    affectedCommunityEvidenceMayReviseStateSuccessAssessmentIsTrue :
      affectedCommunityEvidenceMayReviseStateSuccessAssessment ≡ true

open TemporalParaconsistentBoundary public

canonicalTemporalParaconsistentBoundary : TemporalParaconsistentBoundary
canonicalTemporalParaconsistentBoundary = temporal-paraconsistent-boundary
  false refl false refl false refl false refl true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ReopenedOperationalConclusionDeletesMabo : Set where
data CrossOrderConflictMeansNoHistoricalFactCanBeKnown : Set where
data StateEvidenceMustBeDiscardedWhenCommunityEvidenceDiffers : Set where
data AppendOnlyEvidenceMeansPoliticalProgressIsMonotone : Set where

reopeningDoesNotDeleteMabo : ReopenedOperationalConclusionDeletesMabo → ⊥
reopeningDoesNotDeleteMabo ()

conflictDoesNotEraseHistoricalKnowledge : CrossOrderConflictMeansNoHistoricalFactCanBeKnown → ⊥
conflictDoesNotEraseHistoricalKnowledge ()

communityEvidenceDoesNotRequireDeletingStateEvidence :
  StateEvidenceMustBeDiscardedWhenCommunityEvidenceDiffers → ⊥
communityEvidenceDoesNotRequireDeletingStateEvidence ()

appendOnlyEvidenceDoesNotMakeProgressMonotone :
  AppendOnlyEvidenceMeansPoliticalProgressIsMonotone → ⊥
appendOnlyEvidenceDoesNotMakeProgressMonotone ()
