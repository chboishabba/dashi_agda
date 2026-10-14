module DASHI.Governance.AUKUSUSPersonnelExchangeAuthorityEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- GENERIC U.S. PERSONNEL-EXCHANGE AUTHORITY ENVELOPE
--
-- This owner pays only the generic U.S. statutory/program layer.  It does not
-- substitute that layer for the bilateral Australia-US MOU, the RAN directive,
-- or the same-episode IRIS Dena duty record.
------------------------------------------------------------------------

usCode311 : Source.AttributedSource
usCode311 = Source.mkNoDOISource
  "United States Congress"
  "10 U.S.C. § 311 — Exchange of defense personnel between United States and friendly foreign countries"
  "United States Code"
  "2018"
  "https://www.law.cornell.edu/uscode/text/10/311"
  Source.governmentSource
  "primary statutory authority: permits international defence personnel exchange agreements; assignments must be acceptable to both governments; exchanged personnel need not take a host-country oath or hold official capacity in the host government"
  Source.publicAttribution

myNavyHRPEP : Source.AttributedSource
myNavyHRPEP = Source.mkNoDOISource
  "U.S. Navy"
  "Personnel Exchange Program"
  "MyNavyHR"
  "2026"
  "https://www.mynavyhr.navy.mil/Career-Management/Language-Culture/PEP/"
  Source.governmentSource
  "primary official program description: Australia is a PEP partner and Navy participants normally serve as fully-integrated members of the host nation's military or U.S. service"
  Source.publicAttribution

opnavInstructionIndex : Source.AttributedSource
opnavInstructionIndex = Source.mkNoDOISource
  "Office of the Chief of Naval Operations"
  "OPNAVINST 5700.7J — U.S. Navy Personnel Exchange Program"
  "Department of the Navy Issuances"
  "2018"
  "https://www.secnav.navy.mil/doni/allinstructions.aspx"
  Source.governmentSource
  "primary official instruction index: OPNAV 5700.7J is active; index establishes instruction identity/status, not the content of every operative bilateral arrangement"
  Source.publicAttribution

navseaEmoryLand : Source.AttributedSource
navseaEmoryLand = Source.mkNoDOISource
  "AUKUS Integration and Acquisition Program Public Affairs"
  "In AUKUS First, Royal Australian Navy personnel report to U.S. Submarine Tender"
  "Naval Sea Systems Command"
  "2024"
  "https://www.navsea.navy.mil/Media/News/Article-View/Article/3667880/in-aukus-first-royal-australian-navy-personnel-report-to-us-submarine-tender/"
  Source.governmentSource
  "primary official operational-program context: RAN personnel served as part of USS Emory S. Land's crew under PEP and supported the tender mission of repair, rearm and resupply of forward-deployed U.S. SSNs"
  Source.publicAttribution

record USPEPAuthorityEnvelopeReceipt : Set where
  constructor us-pep-authority-envelope-receipt
  field
    statutoryExchangeAuthorityPaid : Bool
    statutoryExchangeAuthorityPaidIsTrue : statutoryExchangeAuthorityPaid ≡ true
    assignmentMustBeJointlyAcceptablePaid : Bool
    assignmentMustBeJointlyAcceptablePaidIsTrue : assignmentMustBeJointlyAcceptablePaid ≡ true
    noHostOathRequiredPaid : Bool
    noHostOathRequiredPaidIsTrue : noHostOathRequiredPaid ≡ true
    australiaPartnerPaid : Bool
    australiaPartnerPaidIsTrue : australiaPartnerPaid ≡ true
    fullyIntegratedProgramModelAttributed : Bool
    fullyIntegratedProgramModelAttributedIsTrue : fullyIntegratedProgramModelAttributed ≡ true
    genericOperationalIntegrationPaid : Bool
    genericOperationalIntegrationPaidIsTrue : genericOperationalIntegrationPaid ≡ true
    bilateralMOUOperativeTextPaid : Bool
    bilateralMOUOperativeTextPaidIsFalse : bilateralMOUOperativeTextPaid ≡ false
    ranDirectivePrimaryTextPaid : Bool
    ranDirectivePrimaryTextPaidIsFalse : ranDirectivePrimaryTextPaid ≡ false
    irisSameEpisodeDutyPaid : Bool
    irisSameEpisodeDutyPaidIsFalse : irisSameEpisodeDutyPaid ≡ false

open USPEPAuthorityEnvelopeReceipt public

canonicalEnvelope : USPEPAuthorityEnvelopeReceipt
canonicalEnvelope =
  us-pep-authority-envelope-receipt
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

data FullyIntegratedMeansFormalRANCommandDelegated : Set where
data GenericPEPMeansBilateralMOUClauseKnown : Set where
data GenericPEPMeansIRISSameEpisodeDutyKnown : Set where
data NoOathMeansNoHostDirectionAuthority : Set where
data USStatutoryEnvelopeMeansAustralianDFDAAuthority : Set where

fullyIntegratedDoesNotMeanFormalRANCommandDelegation :
  FullyIntegratedMeansFormalRANCommandDelegated → ⊥
fullyIntegratedDoesNotMeanFormalRANCommandDelegation ()

genericPEPDoesNotRevealBilateralMOU :
  GenericPEPMeansBilateralMOUClauseKnown → ⊥
genericPEPDoesNotRevealBilateralMOU ()

genericPEPDoesNotRevealIRISDuty :
  GenericPEPMeansIRISSameEpisodeDutyKnown → ⊥
genericPEPDoesNotRevealIRISDuty ()

noOathDoesNotEraseHostDirectionAuthority :
  NoOathMeansNoHostDirectionAuthority → ⊥
noOathDoesNotEraseHostDirectionAuthority ()

usStatutoryEnvelopeDoesNotCreateAustralianAuthority :
  USStatutoryEnvelopeMeansAustralianDFDAAuthority → ⊥
usStatutoryEnvelopeDoesNotCreateAustralianAuthority ()

usCodeSnowball : Snowball.SourceRoleSnowballReceipt usCode311
usCodeSnowball = Snowball.canonicalSourceRoleSnowballReceipt usCode311

navyPEPSnowball : Snowball.SourceRoleSnowballReceipt myNavyHRPEP
navyPEPSnowball = Snowball.canonicalSourceRoleSnowballReceipt myNavyHRPEP
