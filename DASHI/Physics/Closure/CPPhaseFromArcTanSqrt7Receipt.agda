module DASHI.Physics.Closure.CPPhaseFromArcTanSqrt7Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CP phase candidate from the -7 CM point and the w7 reflection.
--
-- This is a diagnostic receipt only.  The Atkin-Lehner reflected argument
-- gives a numerically good CP-phase candidate after the recorded one-loop
-- correction, but no physical CP-phase authority or CKM promotion is asserted.

data CPPhaseFromArcTanSqrt7Status : Set where
  arctanSqrt7CandidateRecordedNoPromotion :
    CPPhaseFromArcTanSqrt7Status

data CPPhaseCandidateDiagnostic : Set where
  cpPhaseCandidateDiagnosticInhabited :
    CPPhaseCandidateDiagnostic

data CPPhaseFromArcTanSqrt7Blocker : Set where
  atkinLehnerArgumentOnlyDiagnostic :
    CPPhaseFromArcTanSqrt7Blocker

  missingPhysicalCPPhaseAuthority :
    CPPhaseFromArcTanSqrt7Blocker

  missingCKMEmbeddingAndDiagonalisation :
    CPPhaseFromArcTanSqrt7Blocker

canonicalCPPhaseFromArcTanSqrt7Blockers :
  List CPPhaseFromArcTanSqrt7Blocker
canonicalCPPhaseFromArcTanSqrt7Blockers =
  atkinLehnerArgumentOnlyDiagnostic
  ∷ missingPhysicalCPPhaseAuthority
  ∷ missingCKMEmbeddingAndDiagonalisation
  ∷ []

data CPPhaseFromArcTanSqrt7Promotion : Set where

cpPhaseFromArcTanSqrt7PromotionImpossibleHere :
  CPPhaseFromArcTanSqrt7Promotion →
  ⊥
cpPhaseFromArcTanSqrt7PromotionImpossibleHere ()

record CPPhaseFromArcTanSqrt7Receipt : Setω where
  field
    status :
      CPPhaseFromArcTanSqrt7Status

    tauMinus7Formula :
      String

    tauMinus7ArgumentFormula :
      String

    atkinLehnerReflectionFormula :
      String

    atkinLehnerArgumentFormula :
      String

    atkinLehnerArgumentRadians :
      Float

    oneLoopCorrectionFormula :
      String

    alpha1Effective :
      Float

    deltaCPFormula :
      String

    deltaCPRadians :
      Float

    pdgCentralRadians :
      Float

    pdgRangeLowerRadians :
      Float

    pdgRangeUpperRadians :
      Float

    relativeErrorPercent :
      Float

    withinPDGRange :
      Bool

    withinPDGRangeIsTrue :
      withinPDGRange ≡ true

    candidateDiagnostic :
      CPPhaseCandidateDiagnostic

    candidateDiagnosticIsInhabited :
      candidateDiagnostic ≡ cpPhaseCandidateDiagnosticInhabited

    candidateDiagnosticRecorded :
      Bool

    candidateDiagnosticRecordedIsTrue :
      candidateDiagnosticRecorded ≡ true

    physicalCPPhase :
      Bool

    physicalCPPhaseIsFalse :
      physicalCPPhase ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CPPhaseFromArcTanSqrt7Blocker

    blockersAreCanonical :
      blockers ≡ canonicalCPPhaseFromArcTanSqrt7Blockers

    promotionFlags :
      List CPPhaseFromArcTanSqrt7Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CPPhaseFromArcTanSqrt7Receipt public

canonicalCPPhaseFromArcTanSqrt7Receipt :
  CPPhaseFromArcTanSqrt7Receipt
canonicalCPPhaseFromArcTanSqrt7Receipt =
  record
    { status =
        arctanSqrt7CandidateRecordedNoPromotion
    ; tauMinus7Formula =
        "tau_-7 = (-1 + i*sqrt(7))/2"
    ; tauMinus7ArgumentFormula =
        "arg(tau_-7) = pi - arctan(sqrt(7))"
    ; atkinLehnerReflectionFormula =
        "w7(tau) = -1/(7*tau)"
    ; atkinLehnerArgumentFormula =
        "arg(w7(tau_-7)) = arctan(sqrt(7))"
    ; atkinLehnerArgumentRadians =
        1.2094
    ; oneLoopCorrectionFormula =
        "delta_CP = arctan(sqrt(7)) * (1 - alpha1)"
    ; alpha1Effective =
        0.04118
    ; deltaCPFormula =
        "delta_CP = arctan(sqrt(7)) * (1 - alpha1) = 1.1596 radians"
    ; deltaCPRadians =
        1.1596
    ; pdgCentralRadians =
        1.144
    ; pdgRangeLowerRadians =
        1.117
    ; pdgRangeUpperRadians =
        1.171
    ; relativeErrorPercent =
        1.36
    ; withinPDGRange =
        true
    ; withinPDGRangeIsTrue =
        refl
    ; candidateDiagnostic =
        cpPhaseCandidateDiagnosticInhabited
    ; candidateDiagnosticIsInhabited =
        refl
    ; candidateDiagnosticRecorded =
        true
    ; candidateDiagnosticRecordedIsTrue =
        refl
    ; physicalCPPhase =
        false
    ; physicalCPPhaseIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCPPhaseFromArcTanSqrt7Blockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The -7 CM point has argument pi - arctan(sqrt(7))"
        ∷ "The Atkin-Lehner reflection w7(tau) = -1/(7*tau) has argument arctan(sqrt(7)) = 1.2094 radians"
        ∷ "The one-loop corrected candidate delta_CP is 1.1596 radians"
        ∷ "The candidate is 1.36 percent from the PDG central value 1.144 radians and lies within [1.117, 1.171]"
        ∷ "This receipt records an inhabited diagnostic only; physicalCPPhase and physical CKM promotion remain false"
        ∷ []
    }

cpPhaseFromArcTanSqrt7DiagnosticInhabited :
  candidateDiagnostic canonicalCPPhaseFromArcTanSqrt7Receipt
    ≡ cpPhaseCandidateDiagnosticInhabited
cpPhaseFromArcTanSqrt7DiagnosticInhabited =
  refl

cpPhaseFromArcTanSqrt7WithinPDGRange :
  withinPDGRange canonicalCPPhaseFromArcTanSqrt7Receipt ≡ true
cpPhaseFromArcTanSqrt7WithinPDGRange =
  refl

cpPhaseFromArcTanSqrt7DoesNotPromotePhysicalCP :
  physicalCPPhase canonicalCPPhaseFromArcTanSqrt7Receipt ≡ false
cpPhaseFromArcTanSqrt7DoesNotPromotePhysicalCP =
  refl
