module DASHI.Culture.MissingDeceasedTwentyScientistRound78AmyInstituteCorporateEndpointExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound73AmyEvidenceLayerBoundaryExact as R73
import DASHI.Culture.MissingDeceasedTwentyScientistRound77POAMSNamedPrivateSponsorExact as R77

------------------------------------------------------------------------
-- ROUND 78: AMY / INSTITUTE CORPORATE ENDPOINT
--
-- A primary SEC Form D pays Amy Eskridge Pettigrew's corporate identity with
-- Institute, P.B.C. in 2019: President, Executive Officer and Director, with
-- the filing signed by Amy as President.
--
-- This closes the Amy -> Institute corporate endpoint only.  It does NOT put
-- Amy or Institute, P.B.C. on NASA POAMS SAA8-1519855.1, TM 20205010911, the
-- Quantum Machines funding line, an STI release route, or an IP/technology-
-- transfer carrier.  Corporate identity cannot be used as a surrogate for a
-- NASA research-transfer receipt.
------------------------------------------------------------------------

secInstituteFormD : Attribution.AttributedSource
secInstituteFormD = Attribution.mkNoDOISource
  "Institute, P.B.C. / Amy Eskridge Pettigrew"
  "SEC Form D, Institute, P.B.C., CIK 0001771320, accession 0001771320-19-000001"
  "U.S. Securities and Exchange Commission EDGAR"
  "2019"
  "https://www.sec.gov/Archives/edgar/data/1771320/000177132019000001/xslFormDX01/primary_doc.xml"
  Attribution.governmentSource
  "Issuer-filed federal securities notice naming Amy Eskridge Pettigrew as President, Executive Officer and Director of Institute, P.B.C.; signed by Amy as President on 2019-03-27. Pays corporate identity only, not NASA/POAMS participation or technology transfer."
  Attribution.publicAttribution

amyInstituteCorporateIdentityPaid : Bool
amyInstituteCorporateIdentityPaid = true

secFormDPrimaryCarrierPaid : Bool
secFormDPrimaryCarrierPaid = true

amyPresidentPaid : Bool
amyPresidentPaid = true

amyExecutiveOfficerPaid : Bool
amyExecutiveOfficerPaid = true

amyDirectorPaid : Bool
amyDirectorPaid = true

amySignedIssuerFilingPaid : Bool
amySignedIssuerFilingPaid = true

------------------------------------------------------------------------
-- Cross-system bridge remains unpaid.
------------------------------------------------------------------------

nasaPOAMSTransferBridgePaid : Bool
nasaPOAMSTransferBridgePaid = false

amyNamedOnPOAMSSAABySEC : Bool
amyNamedOnPOAMSSAABySEC = false

instituteNamedOnTM20205010911BySEC : Bool
instituteNamedOnTM20205010911BySEC = false

stiReleaseIdentityPaid : Bool
stiReleaseIdentityPaid = false

technologyTransferIdentityPaid : Bool
technologyTransferIdentityPaid = false

ipReleaseIdentityPaid : Bool
ipReleaseIdentityPaid = false

corporateIdentityDoesNotPayNASAResearchParticipation : Bool
corporateIdentityDoesNotPayNASAResearchParticipation = true

federalFilingDoesNotPayTechnicalValidation : Bool
federalFilingDoesNotPayTechnicalValidation = true

corporateOfficeDoesNotPaySamePaperIdentity : Bool
corporateOfficeDoesNotPaySamePaperIdentity = true

selfReportStillCannotPromoteToInstitutionalTransfer : Bool
selfReportStillCannotPromoteToInstitutionalTransfer = true

------------------------------------------------------------------------
-- Interaction with the existing evidence-layer and POAMS sponsor receipts.
------------------------------------------------------------------------

goatsStyleLayerBoundaryRetained : Bool
goatsStyleLayerBoundaryRetained = true

quantumMachinesNamedSponsorLineageStillPaid : Bool
quantumMachinesNamedSponsorLineageStillPaid = R77.poamsNamedPrivateSponsorPaid

amyInstituteEndpointNowPrimaryPaid : Bool
amyInstituteEndpointNowPrimaryPaid = amyInstituteCorporateIdentityPaid

crossSystemIdentityBridgeStillMissing : Bool
crossSystemIdentityBridgeStillMissing = true

round78H2PaidCount : Nat
round78H2PaidCount = 0

round78H3PaidCount : Nat
round78H3PaidCount = 0

round78Reading : String
round78Reading = "A primary SEC Form D now pays the Amy Eskridge Pettigrew <-> Institute, P.B.C. corporate endpoint: Amy is named President, Executive Officer and Director and signs the issuer filing as President. This removes uncertainty about her formal corporate role in the Institute entity, but it does not place Amy or Institute, P.B.C. on NASA POAMS SAA8-1519855.1, TM 20205010911, the Quantum Machines sponsor line, an STI manuscript route, or a technology-transfer/IP-release carrier. The remaining residual is specifically a cross-system NASA/Institute transfer or release identity bridge. H2 and H3 remain unpaid."
