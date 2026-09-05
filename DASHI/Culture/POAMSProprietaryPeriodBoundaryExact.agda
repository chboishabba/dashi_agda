module DASHI.Culture.POAMSProprietaryPeriodBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- POAMS PROPRIETARY-PERIOD BOUNDARY
--
-- The NASA TM itself distinguishes public reporting from possession/access to
-- underlying V5 hardware/data and from the Space Act proprietary-period limit.
------------------------------------------------------------------------

record POAMSBoundaryReceipt : Set where
  constructor poams-boundary-receipt
  field
    sourceReference : String
    publicTMReleased : Bool
    publicTMReleasedIsTrue : publicTMReleased ≡ true
    v5AndDataReportedInQMPossession : Bool
    v5AndDataReportedInQMPossessionIsTrue :
      v5AndDataReportedInQMPossession ≡ true
    proprietaryPeriodReportedAsLimitingNASAWork : Bool
    proprietaryPeriodReportedAsLimitingNASAWorkIsTrue :
      proprietaryPeriodReportedAsLimitingNASAWork ≡ true
    proprietaryPeriodReportedEndedByWriting : Bool
    proprietaryPeriodReportedEndedByWritingIsTrue :
      proprietaryPeriodReportedEndedByWriting ≡ true

canonicalPOAMSBoundaryReceipt : POAMSBoundaryReceipt
canonicalPOAMSBoundaryReceipt = poams-boundary-receipt
  "NASA/TM-20205010911 / M-1531, especially discussion of V5/QM possession and Space Act proprietary period"
  true refl
  true refl
  true refl
  true refl

record POAMSBoundaryFirewall : Set where
  constructor poams-boundary-firewall
  field
    proprietaryPeriodEndedMeansAllUnderlyingDataPublic : Bool
    proprietaryPeriodEndedMeansAllUnderlyingDataPublicIsFalse :
      proprietaryPeriodEndedMeansAllUnderlyingDataPublic ≡ false
    publicTMMeansV5HardwarePubliclyAccessible : Bool
    publicTMMeansV5HardwarePubliclyAccessibleIsFalse :
      publicTMMeansV5HardwarePubliclyAccessible ≡ false
    publicTMMeansAllQMDataPublished : Bool
    publicTMMeansAllQMDataPublishedIsFalse :
      publicTMMeansAllQMDataPublished ≡ false
    limitationEndedMeansAmyReviewObjectIdentified : Bool
    limitationEndedMeansAmyReviewObjectIdentifiedIsFalse :
      limitationEndedMeansAmyReviewObjectIdentified ≡ false

canonicalPOAMSBoundaryFirewall : POAMSBoundaryFirewall
canonicalPOAMSBoundaryFirewall = poams-boundary-firewall
  false refl
  false refl
  false refl
  false refl

record CurrentPOAMSBoundaryInterpretation : Set where
  constructor current-poams-boundary-interpretation
  field
    genuineProprietaryBoundaryDocumented : Bool
    genuineProprietaryBoundaryDocumentedIsTrue :
      genuineProprietaryBoundaryDocumented ≡ true
    boundaryLaterReportedEnded : Bool
    boundaryLaterReportedEndedIsTrue : boundaryLaterReportedEnded ≡ true
    publicTechnicalReportExists : Bool
    publicTechnicalReportExistsIsTrue : publicTechnicalReportExists ≡ true
    completedAllInformationRestrictedToPublicTransferOwned : Bool
    completedAllInformationRestrictedToPublicTransferOwnedIsFalse :
      completedAllInformationRestrictedToPublicTransferOwned ≡ false

canonicalCurrentPOAMSBoundaryInterpretation : CurrentPOAMSBoundaryInterpretation
canonicalCurrentPOAMSBoundaryInterpretation = current-poams-boundary-interpretation
  true refl
  true refl
  true refl
  false refl
