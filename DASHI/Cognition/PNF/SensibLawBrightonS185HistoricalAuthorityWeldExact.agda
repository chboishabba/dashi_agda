module DASHI.Cognition.PNF.SensibLawBrightonS185HistoricalAuthorityWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawDirectionalEvidenceApplicabilityBridgeExact as Directional
import DASHI.Cognition.PNF.SensibLawEventTimeLegalSourceAuthorityExact as EventTime
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify
import DASHI.Law.SensibLawBrightonS185HistoricalAuthoritySourceExact as Historical

------------------------------------------------------------------------
-- BRIGHTON HISTORICAL s 185 -> EXACT APPLICABILITY AUTHORITY WELD
------------------------------------------------------------------------

meetAuthority :
  ∀ {residual demand receipt admission state} →
  Directional.SourceConditionedApplicabilityMeetInput
    {residual} {demand} receipt admission state →
  Authority.LegalSourceAuthorityReceiptInState state
meetAuthority input =
  Meet.legalSourceAuthority
    (Meet.prerequisites (Directional.applicabilityInput input))

historicalReceiptForMeet :
  ∀ {residual demand receipt admission state}
    (input : Directional.SourceConditionedApplicabilityMeetInput
      {residual} {demand} receipt admission state) →
  Historical.HistoricalS185SourceVersionReceipt
    (Ontology.LegalSystem.systemId (Authority.system (meetAuthority input)))
historicalReceiptForMeet input =
  Historical.canonicalHistoricalS185SourceVersionReceipt
    (Ontology.LegalSystem.systemId (Authority.system (meetAuthority input)))

record BrightonHistoricalAuthorityWeld
    {residual : Source.NatSourceSupportResidual}
    {demand : Verify.SourceVerificationDemand residual}
    {receipt : Verify.SourceVerificationReceipt demand}
    {admission : Verify.SourceSupportAdmission receipt}
    {state : Status.SemanticCommitmentState}
    (input : Directional.SourceConditionedApplicabilityMeetInput
      receipt admission state) : Set₁ where
  constructor brighton-historical-authority-weld
  field
    historicalSourceReceipt :
      Historical.HistoricalS185SourceVersionReceipt
        (Ontology.LegalSystem.systemId (Authority.system (meetAuthority input)))

    exactHistoricalSourceIsMeetAuthoritySource :
      Historical.HistoricalS185SourceVersionReceipt.source historicalSourceReceipt
      ≡ Authority.source (meetAuthority input)

    eventTimeAuthority :
      EventTime.EventTimeLegalSourceAuthorityReceipt (meetAuthority input)

    eventTimeAuthorityUsesSameHistoricalSource :
      EventTime.exactAuthoritySource eventTimeAuthority
      ≡ Historical.HistoricalS185SourceVersionReceipt.source historicalSourceReceipt

    matterDateIs24Jan2023 :
      EventTime.eventDate eventTimeAuthority ≡ Historical.brightonMatterDate

    versionStarts1Oct2022 :
      EventTime.intervalEffectiveFrom eventTimeAuthority
      ≡ Historical.versionEffectiveFrom

    nextVersionStarts1Mar2023 :
      EventTime.nextVersionEffectiveFrom eventTimeAuthority
      ≡ Historical.nextVersionEffectiveFrom

    provisionLocatorIsS185 :
      EventTime.exactProvisionLocator eventTimeAuthority
      ≡ "Residential Tenancies and Rooming Accommodation Act 2008 (Qld) s 185(3)(a)-(b)"

    weldReference : String

open BrightonHistoricalAuthorityWeld public

compileEventTimeAuthority :
  ∀ {residual demand receipt admission state}
    (input : Directional.SourceConditionedApplicabilityMeetInput
      {residual} {demand} receipt admission state) →
  (sameSource :
    Historical.HistoricalS185SourceVersionReceipt.source (historicalReceiptForMeet input)
    ≡ Authority.source (meetAuthority input)) →
  EventTime.EventTimeLegalSourceAuthorityReceipt (meetAuthority input)
compileEventTimeAuthority input sameSource =
  EventTime.event-time-legal-source-authority-receipt
    Historical.brightonMatterDate
    Historical.versionEffectiveFrom
    Historical.nextVersionEffectiveFrom
    Historical.BrightonMatterDateWithinVersion
    "Residential Tenancies and Rooming Accommodation Act 2008 (Qld) s 185(3)(a)-(b)"
    "Queensland Legislation point-in-time Act source in the 1-Oct-2022 reprint envelope"
    "Queensland Legislation table of reprints: 1-Oct-2022; next reprint 1-Mar-2023"
    (Historical.HistoricalS185SourceVersionReceipt.source (historicalReceiptForMeet input))
    sameSource
    true refl
    true refl
    false refl
    "Brighton 24-Jan-2023 s185 event-time authority receipt v1"

compiledEventTimeAuthorityUsesMeetSource :
  ∀ {residual demand receipt admission state}
    (input : Directional.SourceConditionedApplicabilityMeetInput
      {residual} {demand} receipt admission state)
    (sameSource :
      Historical.HistoricalS185SourceVersionReceipt.source (historicalReceiptForMeet input)
      ≡ Authority.source (meetAuthority input)) →
  EventTime.exactAuthoritySource (compileEventTimeAuthority input sameSource)
  ≡ Authority.source (meetAuthority input)
compiledEventTimeAuthorityUsesMeetSource input sameSource = sameSource

data HistoricalVersionWithSameCitationAutomaticallyEqualsMeetSource : Set where
data EventTimeReceiptCreatesMatterFact : Set where
data EventTimeReceiptCreatesViolation : Set where
data HistoricalAuthorityBypassesJurisdictionOrScope : Set where

sameCitationDoesNotAutoWeldHistoricalSource :
  HistoricalVersionWithSameCitationAutomaticallyEqualsMeetSource → ⊥
sameCitationDoesNotAutoWeldHistoricalSource ()

eventTimeReceiptDoesNotCreateMatterFact : EventTimeReceiptCreatesMatterFact → ⊥
eventTimeReceiptDoesNotCreateMatterFact ()

eventTimeReceiptDoesNotCreateViolation : EventTimeReceiptCreatesViolation → ⊥
eventTimeReceiptDoesNotCreateViolation ()

historicalAuthorityDoesNotBypassJurisdictionOrScope :
  HistoricalAuthorityBypassesJurisdictionOrScope → ⊥
historicalAuthorityDoesNotBypassJurisdictionOrScope ()

record BrightonHistoricalAuthorityWeldBoundary : Set where
  constructor brighton-historical-authority-weld-boundary
  field
    exactHistoricalSourceVersionRequired : Bool
    exactMeetAuthoritySourceWeldRequired : Bool
    exactEventDateRequired : Bool
    exactVersionIntervalRequired : Bool
    exactProvisionLocatorRequired : Bool
    presentDayValidityRequiredForHistoricalPayment : Bool
    sameCitationAutomaticallyWeldsSource : Bool
    eventTimeAuthorityCreatesMatterFact : Bool
    eventTimeAuthorityCreatesViolation : Bool
    eventTimeAuthorityBypassesJurisdictionOrScope : Bool

canonicalBrightonHistoricalAuthorityWeldBoundary :
  BrightonHistoricalAuthorityWeldBoundary
canonicalBrightonHistoricalAuthorityWeldBoundary =
  brighton-historical-authority-weld-boundary
    true true true true true
    false false false false false
