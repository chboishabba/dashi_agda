module DASHI.Physics.Closure.NSTriadCycleFamilyLowerBoundBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed NS Wall 1 cycle-family quadratic lower-bound boundary.
--
-- This receipt separates the one-cycle quantitative law from the family law
-- on the shell carrier.  It records the target shape
--
--   d^T (C W^-1 C^T)^dagger d
--
-- as the family-level quadratic lower-bound surface, while keeping the
-- uniform c0 > 0 floor explicitly false.  No uniform family bound, Wall 1
-- closure, full NS theorem, or Clay promotion is claimed.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadCycleFamilyLowerBoundStatus : Set where
  triadCycleFamilyLowerBoundBoundaryRecorded :
    NSTriadCycleFamilyLowerBoundStatus

data NSTriadCycleFamilyLowerBoundRow : Set where
  oneCycleLawRecorded :
    NSTriadCycleFamilyLowerBoundRow
  familyLawRecorded :
    NSTriadCycleFamilyLowerBoundRow
  targetShapeRecorded :
    NSTriadCycleFamilyLowerBoundRow
  shellCarrierWall1Recorded :
    NSTriadCycleFamilyLowerBoundRow
  uniformC0FloorStillOpen :
    NSTriadCycleFamilyLowerBoundRow
  familyToFrameGapStillOpen :
    NSTriadCycleFamilyLowerBoundRow
  failClosedPromotionWallRecorded :
    NSTriadCycleFamilyLowerBoundRow

canonicalNSTriadCycleFamilyLowerBoundRows :
  List NSTriadCycleFamilyLowerBoundRow
canonicalNSTriadCycleFamilyLowerBoundRows =
  oneCycleLawRecorded
  ∷ familyLawRecorded
  ∷ targetShapeRecorded
  ∷ shellCarrierWall1Recorded
  ∷ uniformC0FloorStillOpen
  ∷ familyToFrameGapStillOpen
  ∷ failClosedPromotionWallRecorded
  ∷ []

nstriadCycleFamilyLowerBoundRowCount : Nat
nstriadCycleFamilyLowerBoundRowCount =
  listLength canonicalNSTriadCycleFamilyLowerBoundRows

nstriadCycleFamilyLowerBoundRowCountIs7 :
  nstriadCycleFamilyLowerBoundRowCount ≡ 7
nstriadCycleFamilyLowerBoundRowCountIs7 =
  refl

data NSTriadCycleFamilyLowerBoundGap : Set where
  oneCycleLawIsNotTheFamilyLaw :
    NSTriadCycleFamilyLowerBoundGap
  targetShapeDoesNotYetYieldUniformFloor :
    NSTriadCycleFamilyLowerBoundGap
  uniformC0GreaterThanZeroStillFalse :
    NSTriadCycleFamilyLowerBoundGap
  shellCarrierInstantiatedOnlyAsCandidate :
    NSTriadCycleFamilyLowerBoundGap
  theoremAndClayPromotionRemainFalse :
    NSTriadCycleFamilyLowerBoundGap

canonicalNSTriadCycleFamilyLowerBoundGaps :
  List NSTriadCycleFamilyLowerBoundGap
canonicalNSTriadCycleFamilyLowerBoundGaps =
  oneCycleLawIsNotTheFamilyLaw
  ∷ targetShapeDoesNotYetYieldUniformFloor
  ∷ uniformC0GreaterThanZeroStillFalse
  ∷ shellCarrierInstantiatedOnlyAsCandidate
  ∷ theoremAndClayPromotionRemainFalse
  ∷ []

nstriadCycleFamilyLowerBoundGapCount : Nat
nstriadCycleFamilyLowerBoundGapCount =
  listLength canonicalNSTriadCycleFamilyLowerBoundGaps

nstriadCycleFamilyLowerBoundGapCountIs5 :
  nstriadCycleFamilyLowerBoundGapCount ≡ 5
nstriadCycleFamilyLowerBoundGapCountIs5 =
  refl

data NSTriadCycleFamilyLowerBoundPromotion : Set where

nsTriadCycleFamilyLowerBoundPromotionImpossibleHere :
  NSTriadCycleFamilyLowerBoundPromotion → ⊥
nsTriadCycleFamilyLowerBoundPromotionImpossibleHere ()

canonicalTargetShapeText : String
canonicalTargetShapeText =
  "family-level quadratic lower-bound target shape: d^T (C W^-1 C^T)^dagger d"

canonicalOText : String
canonicalOText =
  "O: record the Wall 1 shell carrier as a candidate-only cycle-family lower-bound boundary."

canonicalRText : String
canonicalRText =
  "R: distinguish the one-cycle law from the family law and record the d^T (C W^-1 C^T)^dagger d target shape."

canonicalCText : String
canonicalCText =
  "C: expose the exact target-shape string and canonical false-floor fields in a fail-closed receipt."

canonicalSText : String
canonicalSText =
  "S: the one-cycle law is recorded separately from the family law, while uniform c0 > 0 remains false."

canonicalLText : String
canonicalLText =
  "L: one-cycle law -> family law -> quadratic target shape -> shell carrier -> false uniform floor -> no promotion."

canonicalPText : String
canonicalPText =
  "P: keep the family lower-bound target candidate-only; do not promote Wall 1, theorem, or Clay status."

canonicalGText : String
canonicalGText =
  "G: govern as fail-closed and do not treat the one-cycle law as a uniform family bound."

canonicalFText : String
canonicalFText =
  "F: the missing evidence is a uniform c0 > 0 floor on the shell carrier family; that floor is still false."

record NSTriadCycleFamilyLowerBoundORCSLPGF : Set where
  constructor mkNSTriadCycleFamilyLowerBoundORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ canonicalOText
    R : String
    RIsCanonical : R ≡ canonicalRText
    C : String
    CIsCanonical : C ≡ canonicalCText
    S : String
    SIsCanonical : S ≡ canonicalSText
    L : String
    LIsCanonical : L ≡ canonicalLText
    P : String
    PIsCanonical : P ≡ canonicalPText
    G : String
    GIsCanonical : G ≡ canonicalGText
    F : String
    FIsCanonical : F ≡ canonicalFText

open NSTriadCycleFamilyLowerBoundORCSLPGF public

canonicalNSTriadCycleFamilyLowerBoundORCSLPGF :
  NSTriadCycleFamilyLowerBoundORCSLPGF
canonicalNSTriadCycleFamilyLowerBoundORCSLPGF =
  mkNSTriadCycleFamilyLowerBoundORCSLPGF
    canonicalOText
    refl
    canonicalRText
    refl
    canonicalCText
    refl
    canonicalSText
    refl
    canonicalLText
    refl
    canonicalPText
    refl
    canonicalGText
    refl
    canonicalFText
    refl

record NSTriadCycleFamilyLowerBoundBoundary : Setω where
  constructor mkNSTriadCycleFamilyLowerBoundBoundary
  field
    status :
      NSTriadCycleFamilyLowerBoundStatus
    statusIsCanonical :
      status ≡ triadCycleFamilyLowerBoundBoundaryRecorded

    rows :
      List NSTriadCycleFamilyLowerBoundRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadCycleFamilyLowerBoundRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nstriadCycleFamilyLowerBoundRowCount

    gaps :
      List NSTriadCycleFamilyLowerBoundGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadCycleFamilyLowerBoundGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nstriadCycleFamilyLowerBoundGapCount

    targetShape :
      String
    targetShapeIsCanonical :
      targetShape ≡ canonicalTargetShapeText

    oneCycleLawRecordedHere :
      Bool
    oneCycleLawRecordedHereIsTrue :
      oneCycleLawRecordedHere ≡ true

    familyLawRecordedHere :
      Bool
    familyLawRecordedHereIsTrue :
      familyLawRecordedHere ≡ true

    uniformC0GreaterThanZeroProved :
      Bool
    uniformC0GreaterThanZeroProvedIsFalse :
      uniformC0GreaterThanZeroProved ≡ false

    shellCarrierWall1Closed :
      Bool
    shellCarrierWall1ClosedIsFalse :
      shellCarrierWall1Closed ≡ false

    familyToFrameGapClosed :
      Bool
    familyToFrameGapClosedIsFalse :
      familyToFrameGapClosed ≡ false

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionFlags :
      List NSTriadCycleFamilyLowerBoundPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSTriadCycleFamilyLowerBoundORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadCycleFamilyLowerBoundORCSLPGF

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only Wall 1 cycle-family lower-bound boundary: the one-cycle law is distinct from the family law, the target shape d^T (C W^-1 C^T)^dagger d is recorded, and uniform c0 > 0 remains false."

open NSTriadCycleFamilyLowerBoundBoundary public

