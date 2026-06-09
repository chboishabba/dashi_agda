module DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Vec using (map)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Algebra.TritTriTruthBridge using (rotTrit)
import DASHI.Physics.CRTPeriodJFixedBridge as CRTJ
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.RealTernaryCarrier as RTC
import DASHI.Physics.TritCarrierBridge as TCB

------------------------------------------------------------------------
-- CRT-derived discrete connection audit.
--
-- This module answers the GR-lane promotion question conservatively.  The
-- current CRT/J surface supplies finite scalar and periodicity targets.  The
-- legacy diagnostic below still records the old first-missing boundary, while
-- the additive candidate surface records a typed CRT-monodromy connection
-- shape.  It is not a promoted Einstein-equation or continuum-GR receipt.

data DiscreteConnectionFromCRTStatus : Set where
  firstMissingDiagnosticOnly :
    DiscreteConnectionFromCRTStatus
  typedCRTConnectionCandidateNoEinsteinPromotion :
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

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data TritNonZero : Trit → Set where
  negNonZero :
    TritNonZero neg
  posNonZero :
    TritNonZero pos

data CRTHolonomyElement : Set where
  identityHolonomy :
    CRTHolonomyElement
  crtMonodromyHolonomy :
    CRTHolonomyElement

crtHolonomyFromTrit :
  Trit →
  CRTHolonomyElement
crtHolonomyFromTrit neg = crtMonodromyHolonomy
crtHolonomyFromTrit zer = identityHolonomy
crtHolonomyFromTrit pos = crtMonodromyHolonomy

NonFlatCRTHolonomy :
  Trit →
  Set
NonFlatCRTHolonomy t =
  crtHolonomyFromTrit t ≢ identityHolonomy

tritNonZeroImpliesNonFlatHolonomy :
  (t : Trit) →
  TritNonZero t →
  NonFlatCRTHolonomy t
tritNonZeroImpliesNonFlatHolonomy neg negNonZero ()
tritNonZeroImpliesNonFlatHolonomy pos posNonZero ()

CRTMonodromyConnection :
  RTC.Carrier 1 →
  RTC.Carrier 1
CRTMonodromyConnection =
  map rotTrit

data CRTTritMonodromyCandidateObligation : Set where
  candidateTritCRTMonodromyCompatibility :
    CRTTritMonodromyCandidateObligation

data DiscreteConnectionCandidateResidualObligation : Set where
  missingFullCRTJToTritCosetIsomorphism :
    DiscreteConnectionCandidateResidualObligation
  missingCurvatureToRicciFromCRTMonodromy :
    DiscreteConnectionCandidateResidualObligation
  missingBianchiIdentityForCRTMonodromy :
    DiscreteConnectionCandidateResidualObligation
  missingEinsteinTensorLawForCRTMonodromy :
    DiscreteConnectionCandidateResidualObligation
  missingStressEnergySourceCouplingForCRTMonodromy :
    DiscreteConnectionCandidateResidualObligation
  missingContinuumLimitForCRTMonodromy :
    DiscreteConnectionCandidateResidualObligation

record DiscreteConnectionCandidateFromCRT : Set₁ where
  field
    status :
      DiscreteConnectionFromCRTStatus

    Carrier :
      Set

    carrierIsOneTrit :
      Carrier ≡ RTC.Carrier 1

    connection :
      RTC.Carrier 1 →
      RTC.Carrier 1

    connectionIsCRTMonodromyRotation :
      connection ≡ CRTMonodromyConnection

    holonomyElement :
      Set

    holonomyElementIsCRT :
      holonomyElement ≡ CRTHolonomyElement

    identity :
      CRTHolonomyElement

    monodromy :
      CRTHolonomyElement

    tritHolonomy :
      Trit →
      CRTHolonomyElement

    tritHolonomyIsCRT :
      tritHolonomy ≡ crtHolonomyFromTrit

    nonFlatWitness :
      (t : Trit) →
      TritNonZero t →
      NonFlatCRTHolonomy t

    nonFlatWitnessName :
      String

    crtMoonshineCoupling :
      CRTJ.SSPMoonshineCoupling

    tritCarrierBridge :
      TCB.TritCarrierBridge 1

    candidateNewTheorem :
      CRTTritMonodromyCandidateObligation

    firstMissingAfterConnectionCandidate :
      DET.DiscreteEinsteinTensorFirstMissingCondition

    firstMissingAfterConnectionCandidateIsRicci :
      firstMissingAfterConnectionCandidate
      ≡
      DET.missingCurvatureToRicciContraction

    residualObligations :
      List DiscreteConnectionCandidateResidualObligation

    candidateBoundary :
      List String

canonicalDiscreteConnectionCandidateFromCRT :
  DiscreteConnectionCandidateFromCRT
canonicalDiscreteConnectionCandidateFromCRT =
  record
    { status =
        typedCRTConnectionCandidateNoEinsteinPromotion
    ; Carrier =
        RTC.Carrier 1
    ; carrierIsOneTrit =
        refl
    ; connection =
        CRTMonodromyConnection
    ; connectionIsCRTMonodromyRotation =
        refl
    ; holonomyElement =
        CRTHolonomyElement
    ; holonomyElementIsCRT =
        refl
    ; identity =
        identityHolonomy
    ; monodromy =
        crtMonodromyHolonomy
    ; tritHolonomy =
        crtHolonomyFromTrit
    ; tritHolonomyIsCRT =
        refl
    ; nonFlatWitness =
        tritNonZeroImpliesNonFlatHolonomy
    ; nonFlatWitnessName =
        "tritNonZeroImpliesNonFlatHolonomy"
    ; crtMoonshineCoupling =
        CRTJ.sspMoonshineCouplingSurface
    ; tritCarrierBridge =
        TCB.tritCarrierBridgeSurface 1
    ; candidateNewTheorem =
        candidateTritCRTMonodromyCompatibility
    ; firstMissingAfterConnectionCandidate =
        DET.missingCurvatureToRicciContraction
    ; firstMissingAfterConnectionCandidateIsRicci =
        refl
    ; residualObligations =
        missingFullCRTJToTritCosetIsomorphism
        ∷ missingCurvatureToRicciFromCRTMonodromy
        ∷ missingBianchiIdentityForCRTMonodromy
        ∷ missingEinsteinTensorLawForCRTMonodromy
        ∷ missingStressEnergySourceCouplingForCRTMonodromy
        ∷ missingContinuumLimitForCRTMonodromy
        ∷ []
    ; candidateBoundary =
        "Typed candidate only: CRT monodromy is represented as rotTrit on RTC.Carrier 1"
        ∷ "tritNonZeroImpliesNonFlatHolonomy is inhabited by constructor separation for neg/pos versus identity"
        ∷ "The mathematical bridge from CRT/J monodromy to the trit coset is recorded as candidateTritCRTMonodromyCompatibility"
        ∷ "This advances past the missing non-flat connection/shift diagnostic to a typed candidate"
        ∷ "It does not construct Ricci contraction, Bianchi identity, Einstein tensor law, stress-energy coupling, or continuum GR recovery"
        ∷ []
    }

discreteConnectionCandidateFromCRTStatusIsTypedCandidate :
  DiscreteConnectionCandidateFromCRT.status
    canonicalDiscreteConnectionCandidateFromCRT
  ≡
  typedCRTConnectionCandidateNoEinsteinPromotion
discreteConnectionCandidateFromCRTStatusIsTypedCandidate = refl

discreteConnectionCandidateFromCRTFirstMissingIsRicci :
  DiscreteConnectionCandidateFromCRT.firstMissingAfterConnectionCandidate
    canonicalDiscreteConnectionCandidateFromCRT
  ≡
  DET.missingCurvatureToRicciContraction
discreteConnectionCandidateFromCRTFirstMissingIsRicci = refl

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
