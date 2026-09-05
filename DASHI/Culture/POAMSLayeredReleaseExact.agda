module DASHI.Culture.POAMSLayeredReleaseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.LayeredKnowledgeReleaseBidiExact as L

------------------------------------------------------------------------
-- POAMS / QUANTUM MACHINES LAYERED RELEASE PROFILE
--
-- Primary NASA sources distinguish at least four states:
--   * a Space Act proprietary-period limitation on NASA continuation;
--   * a later public NASA technical memorandum;
--   * V5 data remaining in Quantum Machines possession;
--   * V5 hardware remaining in Quantum Machines possession.
-- This is therefore a genuine partial-release topology, not evidence that all
-- technical material crossed into the public domain.
------------------------------------------------------------------------

poamsGovernance : L.LayerReceipt
poamsGovernance = L.layer-receipt
  "POAMS / SAA8-1519855"
  L.governanceRestriction
  L.endedRestriction
  "NASA/TM-20205010911, p. 23 discussion of Space Act proprietary period"
  "NASA reports that work was limited during the Space Act proprietary period and that, at the time of writing, the proprietary period had ended."

poamsPublicReport : L.LayerReceipt
poamsPublicReport = L.layer-receipt
  "NASA/TM-20205010911 / M-1531"
  L.publicTechnicalReport
  L.public
  "NASA NTRS 20205010911; distribution limits Public; Standard Form 298 Unclassified-Unlimited"
  "The technical memorandum itself is publicly distributed."

poamsData : L.LayerReceipt
poamsData = L.layer-receipt
  "POAMS V5 experimental data"
  L.underlyingData
  L.privateCustody
  "NASA/TM-20205010911, p. 23"
  "NASA reports that the V5 data remained in the possession of Quantum Machines. Public availability of the complete underlying dataset is not established."

poamsHardware : L.LayerReceipt
poamsHardware = L.layer-receipt
  "POAMS V5 apparatus"
  L.physicalHardware
  L.privateCustody
  "NASA/TM-20205010911, p. 23"
  "NASA reports that the V5 apparatus remained in the possession of Quantum Machines."

poamsKnowHow : L.LayerReceipt
poamsKnowHow = L.layer-receipt
  "POAMS implementation know-how"
  L.implementationKnowHow
  L.unknown
  "NASA/TM-20205010911 and public NTRS record"
  "The public report describes design and experiments, but the current record does not establish that all tacit or implementation-specific know-how was public."

poamsPrivateDerivatives : L.LayerReceipt
poamsPrivateDerivatives = L.layer-receipt
  "Institute-derived/matured results described by Amy Eskridge in September 2020"
  L.derivedPrivateResults
  L.unknown
  "Archived September 2020 statement attributed to Amy Eskridge"
  "Amy stated that NASA-origin foundational work had been further matured privately by The Institute. Exact identity and release status of those derivative results remain unresolved."

poamsLayeredReleaseProfile : L.LayeredReleaseProfile
poamsLayeredReleaseProfile = L.layered-release-profile
  "POAMS / Quantum Machines / later Institute derivative lineage"
  poamsGovernance
  poamsPublicReport
  poamsData
  poamsHardware
  poamsKnowHow
  poamsPrivateDerivatives
  "NASA/TM-20205010911; NTRS 20205010911; archived Amy Eskridge September 2020 statement"

poamsPartialRelease : L.PartialReleaseWitness poamsLayeredReleaseProfile
poamsPartialRelease = L.partial-release-witness
  refl
  (inj₁ refl)
  "Public report exists while the underlying V5 data are still reported in private Quantum Machines custody."

poamsGovernanceRelaxed : L.GovernanceRelaxationWitness poamsLayeredReleaseProfile
poamsGovernanceRelaxed = L.governance-relaxation-witness
  refl
  "NASA reports the Space Act proprietary period had ended by the time of the TM."

poamsNeedsDerivativeIdentity : L.LayeredReleaseReverseObligation
poamsNeedsDerivativeIdentity = L.layered-release-reverse-obligation
  "Amy Eskridge September 2020 review object / Institute derivative"
  L.sameLayerSameObjectWeld
  "recover the original Estes Park correspondence, attachment/title, NASA DAA/release identifier, or direct Schaeffer recording that identifies the exact reviewed object"
  "whether Amy's unnamed review object is the public POAMS TM, an earlier NASA study, or a distinct Institute-derived object"
  "a completed Amy-specific restricted-to-public transfer unless exact identity and release status are independently closed"

record CurrentPOAMSLayeredAssessment : Set where
  constructor current-poams-layered-assessment
  field
    governanceBoundaryDocumented : Bool
    governanceBoundaryDocumentedIsTrue : governanceBoundaryDocumented ≡ true
    governanceBoundaryEnded : Bool
    governanceBoundaryEndedIsTrue : governanceBoundaryEnded ≡ true
    publicTechnicalReportOwned : Bool
    publicTechnicalReportOwnedIsTrue : publicTechnicalReportOwned ≡ true
    underlyingDataPubliclyReleased : Bool
    underlyingDataPubliclyReleasedIsFalse : underlyingDataPubliclyReleased ≡ false
    hardwarePubliclyAccessible : Bool
    hardwarePubliclyAccessibleIsFalse : hardwarePubliclyAccessible ≡ false
    amyDerivativeExactIdentityClosed : Bool
    amyDerivativeExactIdentityClosedIsFalse : amyDerivativeExactIdentityClosed ≡ false

canonicalCurrentPOAMSLayeredAssessment : CurrentPOAMSLayeredAssessment
canonicalCurrentPOAMSLayeredAssessment = current-poams-layered-assessment
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
