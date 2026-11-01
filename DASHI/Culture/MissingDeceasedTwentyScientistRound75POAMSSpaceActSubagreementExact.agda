module DASHI.Culture.MissingDeceasedTwentyScientistRound75POAMSSpaceActSubagreementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound74AmyPOAMSCounterCoordinateExact as R74

------------------------------------------------------------------------
-- ROUND 75: POAMS SPACE ACT SUB-AGREEMENT
--
-- NASA's own active-SAA register distinguishes the umbrella agreement
-- SAA8-1519855 from a separately listed POAMS Familiarization entry
-- SAA8-1519855.1.  This materially strengthens the institutional POAMS object
-- but does not identify Amy Eskridge, Richard Eskridge, or The Institute on the
-- agreement-register surface.
------------------------------------------------------------------------

nasaActiveSAARegister : Attribution.AttributedSource
nasaActiveSAARegister = Attribution.mkNoDOISource
  "National Aeronautics and Space Administration"
  "List of Active Space Act Agreements as of December 31, 2016 with Domestic Commercial, State Local Government, and Non-profit Partners"
  "NASA/NSSC public agreement register"
  "2016"
  "https://searchpub.nssc.nasa.gov/servlet/sm.web.Fetch/Active%20Domestic%20Private%20Sector%20SAAs%20as%20of%20%2012-31-2016.pdf?did=1848490&rhid=1000&type=released"
  Attribution.governmentSource
  "Pays NASA/MSFC agreement metadata for Quantum Machines LLC including SAA8-1519855 and the separately titled SAA8-1519855.1 POAMS Familiarization entry; does not identify Amy Eskridge, Richard Eskridge or The Institute on this register surface."
  Attribution.publicAttribution

mainAgreementReference : String
mainAgreementReference = "SAA8-1519855 / Advanced Propulsion Theory and Experimentation / Quantum Machines LLC / MSFC / 2015-07-01 to 2020-07-01"

poamsFamiliarizationReference : String
poamsFamiliarizationReference = "SAA8-1519855.1 / Advanced Propulsion Theory and Experimentation POAMS Familiarization / Quantum Machines LLC / MSFC / 2015-07-01 to 2017-07-01"

poamsFamiliarizationSubagreementPaid : Bool
poamsFamiliarizationSubagreementPaid = true

mainAgreementAndPOAMSSubagreementDistinguished : Bool
mainAgreementAndPOAMSSubagreementDistinguished = true

poamsObjectInstitutionalNamingPaid : Bool
poamsObjectInstitutionalNamingPaid = true

quantumMachinesCounterpartyPaid : Bool
quantumMachinesCounterpartyPaid = true

subagreementDoesNotIdentifyAmyOrRichard : Bool
subagreementDoesNotIdentifyAmyOrRichard = true

subagreementDoesNotIdentifyTheInstitute : Bool
subagreementDoesNotIdentifyTheInstitute = true

subagreementExistenceDoesNotPaySamePaperIdentity : Bool
subagreementExistenceDoesNotPaySamePaperIdentity = true

------------------------------------------------------------------------
-- A later secondary narrative claims an earlier Eskridge/Nelson/Milam study,
-- NASA IP/release processing and transfer toward The Institute.  That is a
-- useful acquisition lead but not an institutional receipt.
------------------------------------------------------------------------

secondaryReleaseProcessLead : String
secondaryReleaseProcessLead = "secondary 2024 narrative reports an earlier Eskridge/Nelson/Milam study and an NASA intellectual-property/release process allegedly involving The Institute"

secondaryReleaseProcessLeadCannotPromoteIdentity : Bool
secondaryReleaseProcessLeadCannotPromoteIdentity = true

secondaryLeadDemandsInstitutionalCarrier : Bool
secondaryLeadDemandsInstitutionalCarrier = true

releaseProcessInstitutionalCarrierLocated : Bool
releaseProcessInstitutionalCarrierLocated = false

samePaperIdentityStillUnpaid : Bool
samePaperIdentityStillUnpaid = true

round75H2PaidCount : Nat
round75H2PaidCount = 0

round75H3PaidCount : Nat
round75H3PaidCount = 0

round75Reading : String
round75Reading = "NASA's own 2016 active Space Act Agreement register independently pays that Quantum Machines LLC held umbrella agreement SAA8-1519855 and a separately listed POAMS Familiarization agreement SAA8-1519855.1 at MSFC. This strengthens the exact institutional POAMS lineage beyond inference from the later Technical Memorandum. The register does not identify Amy Eskridge, Richard Eskridge or The Institute, so it does not pay the Amy-referent or same-paper weld. A secondary report describing an earlier Eskridge/Nelson/Milam study and NASA IP-release process is retained only as an acquisition lead pending a NASA/MSFC agreement attachment, manuscript-routing, technology-transfer, correspondence, review or release carrier."
