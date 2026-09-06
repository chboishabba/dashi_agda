module DASHI.Culture.McCaslandOrganizationalTransitionSurfaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.EventTimeCapabilityAlignmentBidiExact as T
import DASHI.Core.CapabilityFragilityConfoundersBidiExact as F

------------------------------------------------------------------------
-- McCASLAND ORGANISATIONAL TRANSITION SURFACE
--
-- Applied Technology Associates joined the formation of BlueHalo in 2020.
-- AeroVironment closed its acquisition of BlueHalo on 1 May 2025.  These are
-- source-backed organisational transitions prior to McCasland's 2026
-- disappearance, but they do not establish any adverse event or targeting.
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

mccaslandEventTimeAlignment : T.EventTimeCapabilityReceipt
mccaslandEventTimeAlignment = T.event-time-capability-receipt
  "William Neil McCasland"
  "ATA/BlueHalo technology identification, development, integration and strategy portfolio"
  T.recentPreEvent
  "Riverside Research 2019 board announcement; ATA/BlueHalo organisational records; AeroVironment 2025 acquisition record"
  "Public sources support a technology-leadership role and later organisational transitions, but do not yet prove which exact application carrier McCasland possessed or accessed at event time."

record McCaslandOrganisationalTransitionAssessment : Set where
  constructor mccasland-organisational-transition-assessment
  field
    preEventAcquisitionSurfaceExists : Bool
    preEventAcquisitionSurfaceExistsIsTrue : preEventAcquisitionSurfaceExists ≡ true
    exactRoleAfterAeroVironmentAcquisitionClosed : Bool
    exactRoleAfterAeroVironmentAcquisitionClosedIsFalse : exactRoleAfterAeroVironmentAcquisitionClosed ≡ false
    exactAccessAfterAcquisitionClosed : Bool
    exactAccessAfterAcquisitionClosedIsFalse : exactAccessAfterAcquisitionClosed ≡ false
    acquisitionImpliesEventCause : Bool
    acquisitionImpliesEventCauseIsFalse : acquisitionImpliesEventCause ≡ false

canonicalMcCaslandOrganisationalTransitionAssessment : McCaslandOrganisationalTransitionAssessment
canonicalMcCaslandOrganisationalTransitionAssessment =
  mccasland-organisational-transition-assessment true refl false refl false refl false refl
