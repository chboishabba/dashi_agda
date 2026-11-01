module DASHI.Culture.MissingDeceasedTwentyScientistRound79AmyPOAMSTransferBoundedExhaustionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound73AmyEvidenceLayerBoundaryExact as R73
import DASHI.Culture.MissingDeceasedTwentyScientistRound75POAMSSpaceActSubagreementExact as R75
import DASHI.Culture.MissingDeceasedTwentyScientistRound76POAMSFundingIdentifierWeldExact as R76
import DASHI.Culture.MissingDeceasedTwentyScientistRound77POAMSNamedPrivateSponsorExact as R77
import DASHI.Culture.MissingDeceasedTwentyScientistRound78AmyInstituteCorporateEndpointExact as R78

------------------------------------------------------------------------
-- ROUND 79: AMY / POAMS TRANSFER SEARCH BOUNDED EXHAUSTION
--
-- Exact public searches over the known NASA identifiers and agreement title
-- recover the Active Space Act Agreement register and NTRS TM 20205010911, but
-- have not produced the signed SAA8-1519855.1 instrument, an amendment or
-- attachment, STI/manuscript-routing record, technology-transfer/IP-release
-- carrier, or another institutional document explicitly naming Amy Eskridge or
-- Institute, P.B.C. on the POAMS transfer/release path.
--
-- This is a bounded searched-surface result only.  It does not establish that
-- no such record exists, that a record was concealed, or that NASA prevented a
-- release.  Derivative journalism remains a lead rather than payment.
------------------------------------------------------------------------

nasaActiveAgreementRegister : Attribution.AttributedSource
nasaActiveAgreementRegister = Attribution.mkNoDOISource
  "National Aeronautics and Space Administration"
  "List of Active Space Act Agreements as of December 31, 2016"
  "NASA Shared Services Center public agreement register"
  "2016"
  "https://searchpub.nssc.nasa.gov/servlet/sm.web.Fetch/Active%20Domestic%20Private%20Sector%20SAAs%20as%20of%20%2012-31-2016.pdf?did=1848490&rhid=1000&type=released"
  Attribution.governmentSource
  "Pays the public register entries for SAA8-1519855 and SAA8-1519855.1 with Quantum Machines LLC, including the POAMS Familiarization title; does not supply the signed instrument, parties' personnel, or an Amy/Institute transfer bridge."
  Attribution.publicAttribution

ntrsPOAMSTM : Attribution.AttributedSource
ntrsPOAMSTM = Attribution.mkNoDOISource
  "R.H. Eskridge; M.A. Nelson; M.P. Schoenfeld"
  "A Study of the Pope-Osborne Angular Momentum Synthesis Theory (POAMS) Including a Mathematical Reformulation and Validation Experiment"
  "NASA Technical Memorandum / NTRS 20205010911"
  "2021"
  "https://ntrs.nasa.gov/citations/20205010911"
  Attribution.governmentSource
  "Pays the public POAMS TM, MSFC acquisition source, Quantum Machines Space Act Agreement family and funding identifier; does not name Amy Eskridge or Institute, P.B.C. on a transfer/release path."
  Attribution.publicAttribution

signedSAAInstrumentLocated : Bool
signedSAAInstrumentLocated = false

saaAmendmentOrAttachmentLocated : Bool
saaAmendmentOrAttachmentLocated = false

stiRoutingCarrierLocated : Bool
stiRoutingCarrierLocated = false

technologyTransferCarrierLocated : Bool
technologyTransferCarrierLocated = false

ipReleaseCarrierLocated : Bool
ipReleaseCarrierLocated = false

amyInstituteTransferCarrierLocated : Bool
amyInstituteTransferCarrierLocated = false

explicitAmyToPOAMSInstitutionalBridgePaid : Bool
explicitAmyToPOAMSInstitutionalBridgePaid = false

explicitInstituteToPOAMSInstitutionalBridgePaid : Bool
explicitInstituteToPOAMSInstitutionalBridgePaid = false

------------------------------------------------------------------------
-- Search-result and source-role firewalls.
------------------------------------------------------------------------

boundedTransferSearchDoesNotPayUniversalAbsence : Bool
boundedTransferSearchDoesNotPayUniversalAbsence = true

noPublicAttachmentHitDoesNotPayConcealment : Bool
noPublicAttachmentHitDoesNotPayConcealment = true

noTransferCarrierHitDoesNotPaySuppression : Bool
noTransferCarrierHitDoesNotPaySuppression = true

derivativeIPNarrativeCannotPayTransferIdentity : Bool
derivativeIPNarrativeCannotPayTransferIdentity = true

derivativeCeaseAndDesistNarrativeCannotPayNASAReceipt : Bool
derivativeCeaseAndDesistNarrativeCannotPayNASAReceipt = true

selfReportCannotPayNASAReleaseDecision : Bool
selfReportCannotPayNASAReleaseDecision = true

corporateEndpointDoesNotCloseTransferResidual : Bool
corporateEndpointDoesNotCloseTransferResidual = true

------------------------------------------------------------------------
-- Pareto handoff.
------------------------------------------------------------------------

amyBranchMayYieldUntilNewPrimaryTransferLead : Bool
amyBranchMayYieldUntilNewPrimaryTransferLead = true

newPrimaryTransferLeadWouldReopenBranch : Bool
newPrimaryTransferLeadWouldReopenBranch = true

knownInstitutionalEndpointsRemainRecorded : Bool
knownInstitutionalEndpointsRemainRecorded = true

round79H2PaidCount : Nat
round79H2PaidCount = 0

round79H3PaidCount : Nat
round79H3PaidCount = 0

round79Reading : String
round79Reading = "The public NASA transfer search is now bounded enough to yield: exact searches over SAA8-1519855.1, its POAMS Familiarization title, TM 20205010911, agreement amendments/attachments and release-routing terminology recover the known NASA agreement register and POAMS TM but no signed SAA instrument, STI routing carrier, technology-transfer/IP-release record, or institutional document explicitly naming Amy Eskridge or Institute, P.B.C. on the POAMS transfer path. This is a searched-surface result only and does not establish universal absence, concealment, suppression or a NASA release decision. The Amy branch may leave the current Pareto frontier until a new primary transfer/release lead appears. H2 and H3 remain unpaid."
