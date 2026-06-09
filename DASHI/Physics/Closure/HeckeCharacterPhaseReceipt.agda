module DASHI.Physics.Closure.HeckeCharacterPhaseReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Hecke-character phase diagnostic for the p2-p5 CKM phase lane.

data HeckeCharacterPhaseStatus : Set where
  pTwentyNinePhaseDiagnosticRecorded :
    HeckeCharacterPhaseStatus

data HeckeCharacterPhaseBlocker : Set where
  missingCanonicalPrimeChoiceProof :
    HeckeCharacterPhaseBlocker

  missingHeckeCharacterAuthorityBinding :
    HeckeCharacterPhaseBlocker

  phaseMismatchWithPDG :
    HeckeCharacterPhaseBlocker

canonicalHeckeCharacterPhaseBlockers :
  List HeckeCharacterPhaseBlocker
canonicalHeckeCharacterPhaseBlockers =
  missingCanonicalPrimeChoiceProof
  ∷ missingHeckeCharacterAuthorityBinding
  ∷ phaseMismatchWithPDG
  ∷ []

data HeckeCharacterPhasePromotion : Set where

heckeCharacterPhasePromotionImpossibleHere :
  HeckeCharacterPhasePromotion →
  ⊥
heckeCharacterPhasePromotionImpossibleHere ()

record HeckeCharacterPhaseReceipt : Set where
  field
    status :
      HeckeCharacterPhaseStatus

    rationalPrime :
      Nat

    rationalPrimeIsTwentyNine :
      rationalPrime ≡ 29

    splitConditionLabel :
      String

    psiMinusFourLabel :
      String

    psiMinusSevenNormEquation :
      String

    psiMinusSevenLabel :
      String

    phaseFormula :
      String

    candidatePhaseRadians :
      Float

    candidatePhaseRadiansLabel :
      String

    candidatePhaseDegreesLabel :
      String

    pdgPhaseTargetRadians :
      Float

    pdgPhaseTargetLabel :
      String

    absolutePhaseResidualLabel :
      String

    heckePhaseDiagnosticRecorded :
      Bool

    heckePhaseDiagnosticRecordedIsTrue :
      heckePhaseDiagnosticRecorded ≡ true

    phaseMatchesPDG :
      Bool

    phaseMatchesPDGIsFalse :
      phaseMatchesPDG ≡ false

    physicalCPPhaseDerived :
      Bool

    physicalCPPhaseDerivedIsFalse :
      physicalCPPhaseDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List HeckeCharacterPhaseBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHeckeCharacterPhaseBlockers

    promotionFlags :
      List HeckeCharacterPhasePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open HeckeCharacterPhaseReceipt public

canonicalHeckeCharacterPhaseReceipt :
  HeckeCharacterPhaseReceipt
canonicalHeckeCharacterPhaseReceipt =
  record
    { status =
        pTwentyNinePhaseDiagnosticRecorded
    ; rationalPrime =
        29
    ; rationalPrimeIsTwentyNine =
        refl
    ; splitConditionLabel =
        "29 splits in both Q(i) and Q(sqrt(-7)); 29 == 1 mod 4 and 29 == 1 mod 7"
    ; psiMinusFourLabel =
        "psi_-4(p) = 5 + 2 i"
    ; psiMinusSevenNormEquation =
        "a^2 + a*b + 2*b^2 = 29 has solution a=-1,b=4, giving 1 + 2*sqrt(-7)"
    ; psiMinusSevenLabel =
        "psi_-7(p) = 1 + 2 i sqrt(7)"
    ; phaseFormula =
        "delta_29 = arg((1 + 2 i sqrt(7)) / (5 + 2 i))"
    ; candidatePhaseRadians =
        1.003510488600938
    ; candidatePhaseRadiansLabel =
        "delta_29 ~= 1.003510488600938 radians"
    ; candidatePhaseDegreesLabel =
        "delta_29 ~= 57.49691569394486 degrees"
    ; pdgPhaseTargetRadians =
        1.196
    ; pdgPhaseTargetLabel =
        "PDG-sized CKM phase comparison target ~= 1.196 radians"
    ; absolutePhaseResidualLabel =
        "|delta_29 - 1.196| ~= 0.19249 radians; diagnostic mismatch"
    ; heckePhaseDiagnosticRecorded =
        true
    ; heckePhaseDiagnosticRecordedIsTrue =
        refl
    ; phaseMatchesPDG =
        false
    ; phaseMatchesPDGIsFalse =
        refl
    ; physicalCPPhaseDerived =
        false
    ; physicalCPPhaseDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalHeckeCharacterPhaseBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The p=29 Hecke-character phase is a concrete diagnostic"
        ∷ "It does not match the PDG-sized CKM phase target under this convention"
        ∷ "No physical CP-phase or CKM promotion is asserted"
        ∷ []
    }

heckePhaseDiagnosticIsRecorded :
  heckePhaseDiagnosticRecorded canonicalHeckeCharacterPhaseReceipt ≡ true
heckePhaseDiagnosticIsRecorded =
  refl

heckePhaseDoesNotDerivePhysicalCP :
  physicalCPPhaseDerived canonicalHeckeCharacterPhaseReceipt ≡ false
heckePhaseDoesNotDerivePhysicalCP =
  refl

