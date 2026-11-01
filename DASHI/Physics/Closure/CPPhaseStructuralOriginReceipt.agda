module DASHI.Physics.Closure.CPPhaseStructuralOriginReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Structural-origin receipt for the arctan(sqrt(7)) CP-phase candidate.
--
-- The receipt records the non-promoting structural hypothesis:
-- Atkin-Lehner w7 on X0(49) sends the generation-3 CM point tau_-7 to an
-- image whose argument is arctan(sqrt(7)).  This is treated only as a carrier
-- charge-conjugation candidate and a CM-point misalignment candidate, not as a
-- physical CP-phase promotion.

data CPPhaseStructuralOriginStatus : Set where
  atkinLehnerCMPointMisalignmentCandidateRecorded :
    CPPhaseStructuralOriginStatus

data CandidateStatus : Set where
  candidate :
    CandidateStatus

data CPPhaseStructuralOriginBlocker : Set where
  missingAtkinLehnerToPhysicalCPAuthority :
    CPPhaseStructuralOriginBlocker

  missingYukawaEigenbasisEmbedding :
    CPPhaseStructuralOriginBlocker

  missingCKMObservableCalibration :
    CPPhaseStructuralOriginBlocker

canonicalCPPhaseStructuralOriginBlockers :
  List CPPhaseStructuralOriginBlocker
canonicalCPPhaseStructuralOriginBlockers =
  missingAtkinLehnerToPhysicalCPAuthority
  ∷ missingYukawaEigenbasisEmbedding
  ∷ missingCKMObservableCalibration
  ∷ []

data CPPhasePhysicalPromotion : Set where

cpPhasePhysicalPromotionImpossibleHere :
  CPPhasePhysicalPromotion →
  ⊥
cpPhasePhysicalPromotionImpossibleHere ()

record CPPhaseStructuralOriginReceipt : Set where
  field
    status :
      CPPhaseStructuralOriginStatus

    modularCurve :
      String

    conductorLevel :
      Nat

    conductorLevelIsFortyNine :
      conductorLevel ≡ 49

    atkinLehnerOperator :
      String

    atkinLehnerPrime :
      Nat

    atkinLehnerPrimeIsSeven :
      atkinLehnerPrime ≡ 7

    generationCMPoint :
      String

    generationIndex :
      Nat

    generationIndexIsThree :
      generationIndex ≡ 3

    imageArgumentFormula :
      String

    candidatePhaseRadians :
      Float

    candidatePhaseRadiansLabel :
      String

    cpPhaseFromAtkinLehnerRotation :
      CandidateStatus

    cpPhaseFromAtkinLehnerRotationIsCandidate :
      cpPhaseFromAtkinLehnerRotation ≡ candidate

    atkinLehnerIsCarrierChargeConjugation :
      CandidateStatus

    atkinLehnerIsCarrierChargeConjugationIsCandidate :
      atkinLehnerIsCarrierChargeConjugation ≡ candidate

    cpViolationFromCMPointMisalignment :
      CandidateStatus

    cpViolationFromCMPointMisalignmentIsCandidate :
      cpViolationFromCMPointMisalignment ≡ candidate

    structuralOriginRecorded :
      Bool

    structuralOriginRecordedIsTrue :
      structuralOriginRecorded ≡ true

    physicalCPPhasePromoted :
      Bool

    physicalCPPhasePromotedIsFalse :
      physicalCPPhasePromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CPPhaseStructuralOriginBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCPPhaseStructuralOriginBlockers

    physicalPromotionTokens :
      List CPPhasePhysicalPromotion

    physicalPromotionTokensAreEmpty :
      physicalPromotionTokens ≡ []

    receiptBoundary :
      List String

open CPPhaseStructuralOriginReceipt public

canonicalCPPhaseStructuralOriginReceipt :
  CPPhaseStructuralOriginReceipt
canonicalCPPhaseStructuralOriginReceipt =
  record
    { status =
        atkinLehnerCMPointMisalignmentCandidateRecorded
    ; modularCurve =
        "X0(49)"
    ; conductorLevel =
        49
    ; conductorLevelIsFortyNine =
        refl
    ; atkinLehnerOperator =
        "w7"
    ; atkinLehnerPrime =
        7
    ; atkinLehnerPrimeIsSeven =
        refl
    ; generationCMPoint =
        "tau_-7"
    ; generationIndex =
        3
    ; generationIndexIsThree =
        refl
    ; imageArgumentFormula =
        "arg(w7(tau_-7)) = arctan(sqrt(7))"
    ; candidatePhaseRadians =
        1.2094292028881888
    ; candidatePhaseRadiansLabel =
        "arctan(sqrt(7)) ~= 1.2094292028881888 radians"
    ; cpPhaseFromAtkinLehnerRotation =
        candidate
    ; cpPhaseFromAtkinLehnerRotationIsCandidate =
        refl
    ; atkinLehnerIsCarrierChargeConjugation =
        candidate
    ; atkinLehnerIsCarrierChargeConjugationIsCandidate =
        refl
    ; cpViolationFromCMPointMisalignment =
        candidate
    ; cpViolationFromCMPointMisalignmentIsCandidate =
        refl
    ; structuralOriginRecorded =
        true
    ; structuralOriginRecordedIsTrue =
        refl
    ; physicalCPPhasePromoted =
        false
    ; physicalCPPhasePromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCPPhaseStructuralOriginBlockers
    ; blockersAreCanonical =
        refl
    ; physicalPromotionTokens =
        []
    ; physicalPromotionTokensAreEmpty =
        refl
    ; receiptBoundary =
        "Atkin-Lehner w7 on X0(49) is recorded as the structural rotation source"
        ∷ "The generation-3 CM point tau_-7 has candidate image argument arctan(sqrt(7))"
        ∷ "w7 is treated as a carrier charge-conjugation candidate only"
        ∷ "CP violation is recorded as CM-point misalignment candidate only"
        ∷ "No physical CP-phase or CKM promotion is asserted"
        ∷ []
    }

cpPhaseFromAtkinLehnerRotationIsCandidateReceipt :
  cpPhaseFromAtkinLehnerRotation canonicalCPPhaseStructuralOriginReceipt
  ≡ candidate
cpPhaseFromAtkinLehnerRotationIsCandidateReceipt =
  refl

atkinLehnerCarrierChargeConjugationIsCandidateReceipt :
  atkinLehnerIsCarrierChargeConjugation canonicalCPPhaseStructuralOriginReceipt
  ≡ candidate
atkinLehnerCarrierChargeConjugationIsCandidateReceipt =
  refl

cpViolationFromCMPointMisalignmentIsCandidateReceipt :
  cpViolationFromCMPointMisalignment canonicalCPPhaseStructuralOriginReceipt
  ≡ candidate
cpViolationFromCMPointMisalignmentIsCandidateReceipt =
  refl

cpPhaseStructuralOriginDoesNotPromotePhysicalCP :
  physicalCPPhasePromoted canonicalCPPhaseStructuralOriginReceipt ≡ false
cpPhaseStructuralOriginDoesNotPromotePhysicalCP =
  refl
