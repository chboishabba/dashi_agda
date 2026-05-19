module DASHI.Physics.Closure.W5T45CorrectionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic as DYConvention

------------------------------------------------------------------------
-- W5 t45 correction receipt surface.
--
-- This module records the typed surface prepared for the gated runner
-- scripts/run_w5_t45_pdf_correction.py.  The canonical local value remains
-- blocked: no accepted DY luminosity convention authority or provider
-- luminosity packet is present here, and no W5 promotion follows.

data W5T45CorrectionReceiptStatus : Set where
  blockedMissingAcceptedDYLuminosityConvention :
    W5T45CorrectionReceiptStatus
  acceptedConventionCorrectionPass :
    W5T45CorrectionReceiptStatus
  acceptedConventionNegativeObstruction :
    W5T45CorrectionReceiptStatus

data W5T45CorrectionProviderPacketStatus : Set where
  providerPacketAbsent :
    W5T45CorrectionProviderPacketStatus
  providerPacketAccepted :
    W5T45CorrectionProviderPacketStatus
  providerPacketReplacementAccepted :
    W5T45CorrectionProviderPacketStatus

data W5T45CorrectionFirstMissing : Set where
  missingAcceptedDYLuminosityConventionAuthority :
    W5T45CorrectionFirstMissing
  missingProviderLuminosityMethod :
    W5T45CorrectionFirstMissing
  noFirstMissingAfterAcceptedPass :
    W5T45CorrectionFirstMissing

record W5T45CorrectionReceipt : Set where
  field
    receiptStatus :
      W5T45CorrectionReceiptStatus

    providerPacketStatus :
      W5T45CorrectionProviderPacketStatus

    authorityFirstMissing :
      DYConvention.W4W5DYLuminosityFirstMissing

    firstMissing :
      W5T45CorrectionFirstMissing

    target :
      Float

    targetDecimal :
      String

    formula :
      String

    runnerPath :
      String

    providerPacketPath :
      String

    computedR45R43 :
      String

    tolerance :
      String

    absoluteGap :
      String

    successSurface :
      List String

    negativeResultSurface :
      List String

    rejectedLocalCandidateProbes :
      List String

    requiredProviderFields :
      List String

    canonicalBlocker :
      List String

    receiptNotes :
      List String

    pass :
      Bool

    canonicalLocalStateBlocked :
      Bool

    noSyntheticAcceptedConvention :
      ⊤

    noTargetPassClaimed :
      ⊤

    noW5Promotion :
      ⊤

canonicalW5T45CorrectionReceipt :
  W5T45CorrectionReceipt
canonicalW5T45CorrectionReceipt =
  record
    { receiptStatus =
        blockedMissingAcceptedDYLuminosityConvention
    ; providerPacketStatus =
        providerPacketAbsent
    ; authorityFirstMissing =
        DYConvention.missingAcceptedDYLuminosityConventionAuthority
    ; firstMissing =
        missingAcceptedDYLuminosityConventionAuthority
    ; target =
        0.8804486068
    ; targetDecimal =
        "0.8804486068"
    ; formula =
        "R45/R43 = L(M45,Y45) / L(M43,Y43)"
    ; runnerPath =
        "scripts/run_w5_t45_pdf_correction.py"
    ; providerPacketPath =
        "absent; runner requires --provider-packet"
    ; computedR45R43 =
        "not computed in canonical local state"
    ; tolerance =
        "not accepted in canonical local state"
    ; absoluteGap =
        "not computed in canonical local state"
    ; successSurface =
        "provider packet status is accepted or replacement"
        ∷ "accepted DY luminosity authority supplies PDF set, LHAPDF id, grid checksum, scale, rapidity window, mass-bin rule, flavour weights, source, and provenance"
        ∷ "provider luminosities L(M45,Y45) and L(M43,Y43) are finite and L(M43,Y43) is nonzero"
        ∷ "computed R45/R43 equals 0.8804486068 within the accepted tolerance"
        ∷ "receipt still does not promote W5 without downstream governance"
        ∷ []
    ; negativeResultSurface =
        "provider packet absent: fail closed before computation"
        ∷ "provider packet invalid: fail closed before computation"
        ∷ "accepted authority present but luminosity method or fields missing"
        ∷ "accepted authority present but computed R45/R43 misses 0.8804486068 outside tolerance"
        ∷ []
    ; rejectedLocalCandidateProbes =
        "fixed-x CT18 candidate probe = 1.0506681065158017"
        ∷ "rapidity-window t45/z_peak CT18 candidate probe = 0.7514043986785174"
        ∷ "rapidity-window t45/t43 CT18 denominator hypothesis = 0.3348750784006896"
        ∷ []
    ; requiredProviderFields =
        "status: accepted or replacement"
        ∷ "accepted_dy_luminosity_convention.pdf_set"
        ∷ "accepted_dy_luminosity_convention.lhapdf_id"
        ∷ "accepted_dy_luminosity_convention.grid_checksum"
        ∷ "accepted_dy_luminosity_convention.factorization_scale"
        ∷ "accepted_dy_luminosity_convention.rapidity_window"
        ∷ "accepted_dy_luminosity_convention.mass_bin_integration"
        ∷ "accepted_dy_luminosity_convention.flavour_weight_rule"
        ∷ "accepted_dy_luminosity_convention.source"
        ∷ "accepted_dy_luminosity_convention.provenance"
        ∷ "luminosities.L_M45_Y45"
        ∷ "luminosities.L_M43_Y43"
        ∷ "tolerance"
        ∷ []
    ; canonicalBlocker =
        "first missing remains missingAcceptedDYLuminosityConventionAuthority"
        ∷ "provider luminosity method is absent"
        ∷ "no synthetic accepted convention is constructed from local CT18 files"
        ∷ "local CT18 candidate probes remain rejected diagnostics"
        ∷ []
    ; receiptNotes =
        "The runner computes only after an accepted provider packet is supplied"
        ∷ "The typed receipt names both success and clean negative obstruction surfaces"
        ∷ "Canonical local state remains blocked and non-promoting"
        ∷ []
    ; pass =
        false
    ; canonicalLocalStateBlocked =
        true
    ; noSyntheticAcceptedConvention =
        tt
    ; noTargetPassClaimed =
        tt
    ; noW5Promotion =
        tt
    }

canonicalW5T45CorrectionStillBlocked :
  W5T45CorrectionReceipt.receiptStatus
    canonicalW5T45CorrectionReceipt
    ≡
  blockedMissingAcceptedDYLuminosityConvention
canonicalW5T45CorrectionStillBlocked = refl

canonicalW5T45CorrectionNoPass :
  W5T45CorrectionReceipt.pass
    canonicalW5T45CorrectionReceipt
    ≡
  false
canonicalW5T45CorrectionNoPass = refl

canonicalW5T45CorrectionLocalStateBlocked :
  W5T45CorrectionReceipt.canonicalLocalStateBlocked
    canonicalW5T45CorrectionReceipt
    ≡
  true
canonicalW5T45CorrectionLocalStateBlocked = refl
