module DASHI.Culture.MissingDeceasedTwentyScientistRound77POAMSNamedPrivateSponsorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound75POAMSSpaceActSubagreementExact as R75
import DASHI.Culture.MissingDeceasedTwentyScientistRound76POAMSFundingIdentifierWeldExact as R76

------------------------------------------------------------------------
-- ROUND 77: POAMS NAMED PRIVATE-SPONSOR RECEIPT
--
-- NASA/TM-20205010911 acknowledgments name Chris Milam, CEO of Quantum
-- Machines, LLC, as requesting and funding the effort.  This strengthens the
-- exact private-side POAMS sponsor identity.  It does not name Amy Eskridge or
-- The Institute for Exotic Science on the exact NASA POAMS carrier.
------------------------------------------------------------------------

poamsTM : Attribution.AttributedSource
poamsTM = Attribution.mkNoDOISource
  "R.H. Eskridge; M.A. Nelson; M.P. Schoenfeld"
  "A Study of the Pope-Osborne Angular Momentum Synthesis Theory (POAMS) Including a Mathematical Reformulation and Validation Experiment"
  "NASA Technical Memorandum 20205010911 / M-1531"
  "2021"
  "https://ntrs.nasa.gov/citations/20205010911"
  Attribution.governmentSource
  "Pays exact NASA/MSFC POAMS memorandum identity, authorship, Space Act funding family, and the acknowledgments naming Chris Milam of Quantum Machines LLC as requester/funder; does not name Amy Eskridge or The Institute as participant/counterparty."
  Attribution.publicAttribution

poamsNamedPrivateSponsorPaid : Bool
poamsNamedPrivateSponsorPaid = true

chrisMilamRequestedAndFundedEffortPaid : Bool
chrisMilamRequestedAndFundedEffortPaid = true

quantumMachinesCounterpartyPaid : Bool
quantumMachinesCounterpartyPaid = true

msfcPropulsionBranchSupportAcknowledgedPaid : Bool
msfcPropulsionBranchSupportAcknowledgedPaid = true

amyNamedOnExactPOAMSInstitutionalCarrierPaid : Bool
amyNamedOnExactPOAMSInstitutionalCarrierPaid = false

instituteNamedOnExactPOAMSInstitutionalCarrierPaid : Bool
instituteNamedOnExactPOAMSInstitutionalCarrierPaid = false

amyOrInstituteNamedOnExactPOAMSInstitutionalCarrierPaid : Bool
amyOrInstituteNamedOnExactPOAMSInstitutionalCarrierPaid = false

privateSponsorIdentityDoesNotPayAmyBridge : Bool
privateSponsorIdentityDoesNotPayAmyBridge = true

requesterFunderRoleDoesNotTransferAuthorship : Bool
requesterFunderRoleDoesNotTransferAuthorship = true

spaceActCounterpartyDoesNotImplyLaterTechnologyRecipient : Bool
spaceActCounterpartyDoesNotImplyLaterTechnologyRecipient = true

secondaryReleaseNarrativeStillRequiresInstitutionalCarrier : Bool
secondaryReleaseNarrativeStillRequiresInstitutionalCarrier = true

round77H2PaidCount : Nat
round77H2PaidCount = 0

round77H3PaidCount : Nat
round77H3PaidCount = 0

round77Reading : String
round77Reading = "The exact POAMS NASA Technical Memorandum now provides a named private-side sponsor receipt: its acknowledgments thank Chris Milam, CEO of Quantum Machines, LLC, for requesting and funding the effort, while thanking MSFC Propulsion Research and Technology Branch staff for support. This strengthens the institutional POAMS lineage and private counterparty identity. It still does not place Amy Eskridge or The Institute for Exotic Science on the exact NASA POAMS carrier, and therefore does not pay the Amy/Richard/POAMS referent bridge or any technology-transfer relation to The Institute."
