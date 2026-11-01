module DASHI.Physics.Closure.W5CT18ExternalIntakeReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest as Intake
import DASHI.Physics.Closure.W5PDFCarrierExternalConfirmedGap as Gap
import DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic as DYConvention

------------------------------------------------------------------------
-- W5 CT18/MSHT/LHAPDF external intake receipt surface.
--
-- This module is the provider-facing receipt lane for blocker 6.  It records
-- the exact fields an external PDF carrier packet must carry before the t45
-- neutral-current correction can be evaluated.  The canonical value below is
-- intentionally a first-missing receipt diagnostic: a local CT18NLO grid
-- artifact is present and parsed, but no accepted LHAPDF runtime route,
-- parton-luminosity/bin-integration convention, authority packet, W5 closure,
-- or t45 promotion follows from this file.

data W5ExternalPDFFamily : Set where
  ct18PDF :
    W5ExternalPDFFamily
  mshtPDF :
    W5ExternalPDFFamily
  lhapdfCompatiblePDF :
    W5ExternalPDFFamily

data W5CT18ExternalIntakeStatus : Set where
  waitingForExternalPDFPacketFields :
    W5CT18ExternalIntakeStatus

data W5CT18ExternalPacketReadiness : Set where
  packetFieldsMissing :
    W5CT18ExternalPacketReadiness

data W5CT18ExternalPacketField : Set where
  missingPDFSetIdentifierAndVersion :
    W5CT18ExternalPacketField
  missingLHAPDFGridOrEquivalentTable :
    W5CT18ExternalPacketField
  missingPartonLuminosityRoute :
    W5CT18ExternalPacketField
  missingMassWindowConvention :
    W5CT18ExternalPacketField
  missingFlavourChannelConvention :
    W5CT18ExternalPacketField
  missingT45CorrectionComputation :
    W5CT18ExternalPacketField
  missingAcceptedRapidityIntegrationConvention :
    W5CT18ExternalPacketField
  missingCorrectionToleranceStatement :
    W5CT18ExternalPacketField
  missingPDFTableAuthorityReceipt :
    W5CT18ExternalPacketField

record W5CT18ExternalIntakeReceipt : Set where
  field
    intakeStatus :
      W5CT18ExternalIntakeStatus

    packetReadiness :
      W5CT18ExternalPacketReadiness

    intakeRequest :
      Intake.W5PDFCarrierExternalIntakeRequest

    confirmedGap :
      Gap.W5PDFCarrierExternalConfirmedGap

    authorityFirstMissing :
      DYConvention.W4W5DYLuminosityFirstMissing

    acceptableFamilies :
      List W5ExternalPDFFamily

    requiredT45Correction :
      Float

    requiredT45CorrectionDecimal :
      String

    requiredPacketFields :
      List String

    missingPacketFields :
      List W5CT18ExternalPacketField

    missingPacketFieldLabels :
      List String

    firstMissingStatus :
      String

    externalReady :
      Bool

    receiptNotes :
      List String

    conventionAcceptanceGate :
      List String

    acceptedAuthorityReceiptSurface :
      List String

    missingAuthorityFields :
      List DYConvention.W4W5DYLuminosityAuthorityField

    lhapdf6ExternalIntakeContract :
      List Intake.LHAPDF6ExternalIntakeContractField

    lhapdf6ExternalIntakeContractIsCanonical :
      lhapdf6ExternalIntakeContract
      ≡
      Intake.canonicalLHAPDF6ExternalIntakeContractFields

    lhapdf6ExternalIntakeContractLabels :
      List String

    localCT18GridParsed :
      Bool

    localCT18GridParsedIsTrue :
      localCT18GridParsed ≡ true

    localCT18DASHIProjectionBinding :
      List String

    providerAuthorityContract :
      List String

    networkFetchPerformed :
      Bool

    noAcceptedLHAPDFRuntimeAssumed :
      ⊤

    noExternalPDFPacketAccepted :
      ⊤

    noPDFCarrierConstructed :
      ⊤

    noT45PromotionConstructed :
      ⊤

    noW5ClosureConstructed :
      ⊤

canonicalW5CT18ExternalIntakeReceipt :
  W5CT18ExternalIntakeReceipt
canonicalW5CT18ExternalIntakeReceipt =
  record
    { intakeStatus =
        waitingForExternalPDFPacketFields
    ; packetReadiness =
        packetFieldsMissing
    ; intakeRequest =
        Intake.canonicalW5PDFCarrierExternalIntakeRequest
    ; confirmedGap =
        Gap.canonicalW5PDFCarrierExternalConfirmedGap
    ; authorityFirstMissing =
        DYConvention.missingAcceptedDYLuminosityConventionAuthority
    ; acceptableFamilies =
        ct18PDF
        ∷ mshtPDF
        ∷ lhapdfCompatiblePDF
        ∷ []
    ; requiredT45Correction =
        0.8804486068
    ; requiredT45CorrectionDecimal =
        "0.8804486068"
    ; requiredPacketFields =
        "PDF family: CT18, MSHT, or LHAPDF-compatible equivalent"
        ∷ "PDF set identifier and version"
        ∷ "LHAPDF id and grid path/checksum or equivalent provider table checksum"
        ∷ "parton-luminosity route for the CMS-SMP-20-003 t45 window"
        ∷ "factorization scale convention for 106-170 and 76-106 GeV mass windows"
        ∷ "rapidity-window convention for the Drell-Yan luminosity ratio"
        ∷ "mass-bin integration rule for the Drell-Yan luminosity ratio"
        ∷ "flavour-weight rule for the Drell-Yan luminosity ratio"
        ∷ "computed t45 correction factor targeting 0.8804486068"
        ∷ "source DOI for the PDF set and/or accepted luminosity convention"
        ∷ "tolerance statement for the difference from 0.8804486068"
        ∷ "authority/provenance receipt for the external PDF table"
        ∷ []
    ; missingPacketFields =
        missingPartonLuminosityRoute
        ∷ missingMassWindowConvention
        ∷ missingFlavourChannelConvention
        ∷ missingT45CorrectionComputation
        ∷ missingAcceptedRapidityIntegrationConvention
        ∷ missingCorrectionToleranceStatement
        ∷ missingPDFTableAuthorityReceipt
        ∷ []
    ; missingPacketFieldLabels =
        "missing accepted parton-luminosity route"
        ∷ "missing 106-170 and 76-106 GeV mass-window convention"
        ∷ "missing flavour/channel convention"
        ∷ "local fixed-x CT18 central extraction computed 1.0506681065158017; missing accepted computation that targets 0.8804486068"
        ∷ "z-peak denominator rapidity-window CT18 query computed t45/z_peak = 0.7514043986785174 with abs gap 0.12904420812148265"
        ∷ "t43 denominator hypothesis was tested directly and computed t45/t43 = 0.3348750784006896 with abs gap 0.5455735283993104; changing only the denominator does not satisfy the W5 target"
        ∷ "missing accepted convention that maps CT18NLO onto the W5 target"
        ∷ "missing tolerance statement against 0.8804486068"
        ∷ "missing external PDF table authority/provenance receipt"
        ∷ []
    ; firstMissingStatus =
        "first missing: missingAcceptedDYLuminosityConventionAuthority; CT18 grid provenance exists locally but is not an accepted W5 t45 correction convention"
    ; externalReady =
        false
    ; receiptNotes =
        "This is a CT18/MSHT/LHAPDF intake receipt surface, not a positive external PDF carrier"
        ∷ "The required correction remains 0.8804486068"
        ∷ "Local CT18NLO artifact is present: archive SHA-256 c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213; central grid SHA-256 375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410"
        ∷ "Local parser extraction at x = 0.01 gives u-quark xfxQ ratio 1.0506681065158017, which does not satisfy the W5 target"
        ∷ "The repo t45 prediction baseline is sigma_DASHI(106-170, phi bin) / sigma_DASHI(76-106, phi bin)"
        ∷ "Local parser rapidity-window DY luminosity integration gives t45/z_peak = 0.7514043986785174, which does not satisfy the W5 target"
        ∷ "Local parser also records the t43-denominator mass-window ratio t45/t43 = 0.3348750784006896 and center ratio 0.13510406305538247; the t43 denominator hypothesis is rejected under this convention"
        ∷ "The packet now records formula, bin integration, scale choice, flavour sum, CT18NLO member/provenance, and required authority fields, but remains candidate-not-accepted"
        ∷ "Euler 2026-05-13 reran the CT18 equivalent-table candidate packet at logs/research/w4w5_pdf_ct18_candidate_run_20260513.json; SHA-256 7b4e5e815c3e65619cd9591734eb00e7c80be0402c6d06c3c8d33d1c8da6609f"
        ∷ "Euler 2026-05-13 recorded that a real LHAPDF runtime run is not possible here: lhapdf, lhapdf-config, and Python lhapdf are absent; no MSHT20 grid was found locally"
        ∷ "The exact tool/provider obstruction is logs/research/w4w5_pdf_lhapdf_intake_obstruction_20260513.json; SHA-256 a67318e71b4c18fde71597874f93aa28ab020557f230dd3843f807e40545b88d"
        ∷ "The confirmed internal DGLAP/LO carrier route remains insufficient for t45"
        ∷ "W5 is not externally ready until an accepted parton-luminosity/bin-integration convention and authority/provenance packet are supplied"
        ∷ []
    ; conventionAcceptanceGate =
        "the local CT18NLO packet may feed an accepted receipt only after an authority accepts the formula, bin integration, scale choice, flavour sum, member/error treatment, and tolerance"
        ∷ "the present receipt therefore cannot construct a PDF carrier and cannot promote W5"
        ∷ "W4/W5 merged blocker status remains first-missing rather than closed"
        ∷ []
    ; acceptedAuthorityReceiptSurface =
        "PDF set"
        ∷ "LHAPDF id"
        ∷ "grid checksum"
        ∷ "factorization scale convention"
        ∷ "rapidity window"
        ∷ "mass-bin integration rule"
        ∷ "flavour-weight rule"
        ∷ "source DOI"
        ∷ "external authority/provenance"
        ∷ []
    ; missingAuthorityFields =
        DYConvention.W4W5AcceptedDYLuminosityConventionDiagnostic.missingAuthorityFields
          DYConvention.canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ; lhapdf6ExternalIntakeContract =
        Intake.canonicalLHAPDF6ExternalIntakeContractFields
    ; lhapdf6ExternalIntakeContractIsCanonical =
        refl
    ; lhapdf6ExternalIntakeContractLabels =
        Intake.W5PDFCarrierExternalIntakeRequest.lhapdf6ExternalIntakeContractLabels
          Intake.canonicalW5PDFCarrierExternalIntakeRequest
    ; localCT18GridParsed =
        true
    ; localCT18GridParsedIsTrue =
        refl
    ; localCT18DASHIProjectionBinding =
        Intake.W5PDFCarrierExternalIntakeRequest.localCT18DASHIProjectionBinding
          Intake.canonicalW5PDFCarrierExternalIntakeRequest
    ; providerAuthorityContract =
        "receipt is provider-ready only as an intake surface: no accepted external packet is present"
        ∷ "receipt must accept or replace the candidate CT18NLO formula, bin integration, scale choice, flavour sum, member/error treatment, and tolerance"
        ∷ "receipt must carry provider, command/API, source path or DOI, input checksums, timestamp, and explicit acceptance statement"
        ∷ "receipt must leave local CT18 fixed-x and rapidity-window probes candidate-only/falsified until an authority supersedes them"
        ∷ "receipt must supply a real LHAPDF route or accepted equivalent provider table because the 2026-05-13 local preflight found no LHAPDF runtime and no MSHT20 grid"
        ∷ "receipt must not construct W5 closure or W4/W5 shared closure"
        ∷ []
    ; networkFetchPerformed =
        false
    ; noAcceptedLHAPDFRuntimeAssumed =
        tt
    ; noExternalPDFPacketAccepted =
        tt
    ; noPDFCarrierConstructed =
        tt
    ; noT45PromotionConstructed =
        tt
    ; noW5ClosureConstructed =
        tt
    }

canonicalW5CT18ExternalIntakeStillWaiting :
  W5CT18ExternalIntakeReceipt.intakeStatus
    canonicalW5CT18ExternalIntakeReceipt
    ≡
  waitingForExternalPDFPacketFields
canonicalW5CT18ExternalIntakeStillWaiting = refl

canonicalW5CT18ExternalPacketFieldsStillMissing :
  W5CT18ExternalIntakeReceipt.packetReadiness
    canonicalW5CT18ExternalIntakeReceipt
    ≡
  packetFieldsMissing
canonicalW5CT18ExternalPacketFieldsStillMissing = refl

canonicalW5CT18ExternalNotReady :
  W5CT18ExternalIntakeReceipt.externalReady
    canonicalW5CT18ExternalIntakeReceipt
    ≡
  false
canonicalW5CT18ExternalNotReady = refl

canonicalW5CT18ExternalAuthorityFirstMissing :
  W5CT18ExternalIntakeReceipt.authorityFirstMissing
    canonicalW5CT18ExternalIntakeReceipt
    ≡
  DYConvention.missingAcceptedDYLuminosityConventionAuthority
canonicalW5CT18ExternalAuthorityFirstMissing =
  refl
