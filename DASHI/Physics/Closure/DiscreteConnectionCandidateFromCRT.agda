module DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.CRTPeriodJFixedBridge as CRTJ
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET

------------------------------------------------------------------------
-- CRT-derived discrete connection audit.
--
-- This module answers the GR-lane promotion question conservatively.  The
-- current CRT/J surface supplies finite scalar and periodicity targets, while
-- DiscreteEinsteinTensorCandidate already records that no carrier-internal
-- non-flat connection from CRT has been constructed.  Therefore this file is
-- a first-missing diagnostic, not a promoted connection candidate.

data DiscreteConnectionFromCRTStatus : Set where
  firstMissingDiagnosticOnly :
    DiscreteConnectionFromCRTStatus

data DiscreteConnectionFromCRTUnsupportedClaim : Set where
  unsupportedAsymptoticConnectionClaim :
    DiscreteConnectionFromCRTUnsupportedClaim
  unsupportedFiniteRadiusGRClaim :
    DiscreteConnectionFromCRTUnsupportedClaim
  unsupportedNonFlatConnectionClaim :
    DiscreteConnectionFromCRTUnsupportedClaim
  unsupportedBianchiClaim :
    DiscreteConnectionFromCRTUnsupportedClaim
  unsupportedEinsteinTensorPromotionClaim :
    DiscreteConnectionFromCRTUnsupportedClaim

record DiscreteConnectionCandidateFromCRTDiagnostic : Set₁ where
  field
    status :
      DiscreteConnectionFromCRTStatus

    crtMoonshineCoupling :
      CRTJ.SSPMoonshineCoupling

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    inheritedCRTConnectionAudit :
      DET.CRTMoonshineNonFlatConnectionAudit

    firstMissing :
      DET.DiscreteEinsteinTensorFirstMissingCondition

    firstMissingIsCarrierInternalCRTConnection :
      firstMissing
      ≡
      DET.missingCarrierInternalNonFlatConnectionFromCRT

    suppliedSurface :
      List String

    missingSurface :
      List String

    unsupportedClaims :
      List DiscreteConnectionFromCRTUnsupportedClaim

    diagnosticBoundary :
      List String

    nextAdmissibleReceipt :
      String

canonicalDiscreteConnectionCandidateFromCRTDiagnostic :
  DiscreteConnectionCandidateFromCRTDiagnostic
canonicalDiscreteConnectionCandidateFromCRTDiagnostic =
  record
    { status =
        firstMissingDiagnosticOnly
    ; crtMoonshineCoupling =
        CRTJ.sspMoonshineCouplingSurface
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; inheritedCRTConnectionAudit =
        DET.canonicalCRTMoonshineNonFlatConnectionAudit
    ; firstMissing =
        DET.missingCarrierInternalNonFlatConnectionFromCRT
    ; firstMissingIsCarrierInternalCRTConnection =
        refl
    ; suppliedSurface =
        "CRT period product over p47/p59/p71"
        ∷ "J contract bridge to CRT period plus one"
        ∷ "p47/p59/p71 active-wall channel projections"
        ∷ "W3 periodicity and moonshine representation obligation targets"
        ∷ "Flat Minkowski quadratic from the discrete Einstein tensor diagnostic"
        ∷ []
    ; missingSurface =
        "No CRT-derived endomap on the Minkowski carrier"
        ∷ "No connection coefficients or parallel-transport law"
        ∷ "No non-flat shift/connection law internal to the carrier"
        ∷ "No curvature-to-Ricci contraction from CRT/J"
        ∷ "No Bianchi witness for a non-flat discrete connection"
        ∷ "No finite-radius or asymptotic GR theorem"
        ∷ []
    ; unsupportedClaims =
        unsupportedAsymptoticConnectionClaim
        ∷ unsupportedFiniteRadiusGRClaim
        ∷ unsupportedNonFlatConnectionClaim
        ∷ unsupportedBianchiClaim
        ∷ unsupportedEinsteinTensorPromotionClaim
        ∷ []
    ; diagnosticBoundary =
        "This module does not add a promoted DiscreteConnection candidate"
        ∷ "The current repository supports only the first-missing CRT-to-connection diagnostic"
        ∷ "Finite CRT/J scalar surfaces are not treated as connection data"
        ∷ "The flat Minkowski receipt remains flat-only and does not imply curved GR"
        ∷ "No numeric approximate evidence is retyped as an exact Agda theorem"
        ∷ []
    ; nextAdmissibleReceipt =
        "carrier-internal non-flat connection or shift law derived from CRT/J, with explicit curvature and downstream Bianchi/Einstein obligations"
    }

discreteConnectionFromCRTExactFirstMissing :
  DiscreteConnectionCandidateFromCRTDiagnostic.firstMissing
    canonicalDiscreteConnectionCandidateFromCRTDiagnostic
  ≡
  DET.missingCarrierInternalNonFlatConnectionFromCRT
discreteConnectionFromCRTExactFirstMissing = refl

discreteConnectionFromCRTStatusIsDiagnosticOnly :
  DiscreteConnectionCandidateFromCRTDiagnostic.status
    canonicalDiscreteConnectionCandidateFromCRTDiagnostic
  ≡
  firstMissingDiagnosticOnly
discreteConnectionFromCRTStatusIsDiagnosticOnly = refl
