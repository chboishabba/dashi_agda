module DASHI.Physics.Closure.W5CT18ExternalIntakeReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest as Intake
import DASHI.Physics.Closure.W5PDFCarrierExternalConfirmedGap as Gap

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

    externalReady :
      Bool

    receiptNotes :
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
        ∷ "LHAPDF grid path/checksum or equivalent provider table checksum"
        ∷ "parton-luminosity route for the CMS-SMP-20-003 t45 window"
        ∷ "x and Q2 convention for 106-170 and 76-106 GeV mass windows"
        ∷ "flavour/channel convention for the Drell-Yan luminosity ratio"
        ∷ "computed t45 correction factor targeting 0.8804486068"
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
        ∷ "matching local rapidity-window CT18 query for sigma_DASHI(106-170)/sigma_DASHI(76-106) computed t45/z_peak = 0.7514043986785174 with abs gap 0.12904420812148265; missing accepted convention that maps CT18NLO onto the W5 target"
        ∷ "missing tolerance statement against 0.8804486068"
        ∷ "missing external PDF table authority/provenance receipt"
        ∷ []
    ; externalReady =
        false
    ; receiptNotes =
        "This is a CT18/MSHT/LHAPDF intake receipt surface, not a positive external PDF carrier"
        ∷ "The required correction remains 0.8804486068"
        ∷ "Local CT18NLO artifact is present: archive SHA-256 c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213; central grid SHA-256 375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410"
        ∷ "Local parser extraction at x = 0.01 gives u-quark xfxQ ratio 1.0506681065158017, which does not satisfy the W5 target"
        ∷ "The repo t45 prediction baseline is sigma_DASHI(106-170, phi bin) / sigma_DASHI(76-106, phi bin)"
        ∷ "Local parser matching rapidity-window DY luminosity integration gives t45/z_peak = 0.7514043986785174, which does not satisfy the W5 target"
        ∷ "Local parser also records non-matching t45/t43 center ratio 0.13510406305538247 and mass-window ratio 0.3348750784006896 for audit continuity"
        ∷ "The confirmed internal DGLAP/LO carrier route remains insufficient for t45"
        ∷ "W5 is not externally ready until an accepted parton-luminosity/bin-integration convention and authority/provenance packet are supplied"
        ∷ []
    ; networkFetchPerformed =
        true
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
