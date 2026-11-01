module DASHI.Culture.McCaslandOrganizationalTransitionSurfaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.EventTimeCapabilityAlignmentBidiExact as T
import DASHI.Core.CapabilityFragilityConfoundersBidiExact as F

------------------------------------------------------------------------
-- McCASLAND ORGANISATIONAL TRANSITION SURFACE
--
-- Applied Technology Associates joined the formation of BlueHalo in 2020.
-- AeroVironment closed its acquisition of BlueHalo on 1 May 2025. These are
-- source-backed organisational transitions prior to McCasland's 2026
-- disappearance, but they do not establish any adverse event or targeting.
--
-- A separate primary USRA 2025 Board of Trustees page lists Maj. Gen. Neil
-- McCasland (ret.) as an At-Large trustee. That is a close-to-event governance
-- carrier. It does not identify his employer, consulting clients, technical
-- programme, access, or application-object possession.
------------------------------------------------------------------------

ataToBlueHalo : F.FragilityReceipt
ataToBlueHalo = F.fragility-receipt
  "William Neil McCasland / ATA"
  F.mergerOrAcquisition
  F.sourceBacked
  "BlueHalo/PRNewswire 29 Oct 2020; Arlington Capital Partners 29 Oct 2020"
  "ATA joined the formation of BlueHalo with AEgis Technologies and Brilligent Solutions, creating a broader national-security technology platform."

blueHaloToAeroVironment : F.FragilityReceipt
blueHaloToAeroVironment = F.fragility-receipt
  "William Neil McCasland / BlueHalo"
  F.mergerOrAcquisition
  F.sourceBacked
  "AeroVironment SEC filing, acquisition closed 1 May 2025"
  "AeroVironment acquired BlueHalo before McCasland's February 2026 disappearance; role, access, portfolio and handover consequences for McCasland are not yet established."

record GovernanceContinuityReceipt : Set where
  constructor governance-continuity-receipt
  field
    person : String
    organisation : String
    role : String
    datedSurface : String
    sourceReference : String
    formalGovernanceRoleOwned : Bool
    employerIdentityOwned : Bool
    technicalProgrammeIdentityOwned : Bool
    programmeAccessOwned : Bool

open GovernanceContinuityReceipt public

mcCaslandUSRA2025Governance : GovernanceContinuityReceipt
mcCaslandUSRA2025Governance = governance-continuity-receipt
  "Maj. Gen. Neil McCasland (ret.)"
  "Universities Space Research Association"
  "At-Large member, Board of Trustees"
  "USRA Board of Trustees 2025"
  "USRA primary Board of Trustees page"
  true false false false

mccaslandEventTimeAlignment : T.EventTimeCapabilityReceipt
mccaslandEventTimeAlignment = T.event-time-capability-receipt
  "William Neil McCasland"
  "historical ATA/BlueHalo technology work plus 2025 USRA space-research governance"
  T.recentPreEvent
  "Riverside Research 2019 board announcement; ATA/BlueHalo organisational records; AeroVironment 2025 acquisition record; USRA Board of Trustees 2025"
  "Public sources support historical technology leadership, later organisational transitions, and a 2025 USRA governance role, but do not yet prove his 2025-2026 employer/client, exact technical application carrier, possession or access at event time."

record McCaslandOrganisationalTransitionAssessment : Set where
  constructor mccasland-organisational-transition-assessment
  field
    preEventAcquisitionSurfaceExists : Bool
    preEventAcquisitionSurfaceExistsIsTrue : preEventAcquisitionSurfaceExists ≡ true
    usra2025GovernanceContinuityOwned : Bool
    usra2025GovernanceContinuityOwnedIsTrue : usra2025GovernanceContinuityOwned ≡ true
    exactRoleAfterAeroVironmentAcquisitionClosed : Bool
    exactRoleAfterAeroVironmentAcquisitionClosedIsFalse : exactRoleAfterAeroVironmentAcquisitionClosed ≡ false
    exact2025To2026EmployerOrClientClosed : Bool
    exact2025To2026EmployerOrClientClosedIsFalse : exact2025To2026EmployerOrClientClosed ≡ false
    exactAccessAfterAcquisitionClosed : Bool
    exactAccessAfterAcquisitionClosedIsFalse : exactAccessAfterAcquisitionClosed ≡ false
    governanceRoleImpliesTechnicalProgrammePossession : Bool
    governanceRoleImpliesTechnicalProgrammePossessionIsFalse : governanceRoleImpliesTechnicalProgrammePossession ≡ false
    acquisitionImpliesEventCause : Bool
    acquisitionImpliesEventCauseIsFalse : acquisitionImpliesEventCause ≡ false

canonicalMcCaslandOrganisationalTransitionAssessment : McCaslandOrganisationalTransitionAssessment
canonicalMcCaslandOrganisationalTransitionAssessment =
  mccasland-organisational-transition-assessment
    true refl true refl false refl false refl false refl false refl false refl
