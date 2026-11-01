module DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Correction receipt 1: Q(sqrt(-7)) splitting over the 15 SSP primes.
--
-- This receipt records the literal CM-field splitting table separately
-- from the 7+7+1 atom grammar.  The CM table is a quadratic-arithmetic
-- correction; it does not promote a Clay theorem or identify the atom
-- grammar with the CM-field theorem.

data SSP15CMFieldSplittingCorrectionStatus : Set where
  qsqrtMinusSevenSSP15SplittingCorrectionRecorded :
    SSP15CMFieldSplittingCorrectionStatus

data CMPrimeSplittingClass : Set where
  split :
    CMPrimeSplittingClass

  inert :
    CMPrimeSplittingClass

  ramified :
    CMPrimeSplittingClass

data FrameImplicationComponent : Set where
  splitPrimesContributeTwoOMinusSevenComponents :
    FrameImplicationComponent

  inertPrimesRequireDegreeTwoPhaseInfo :
    FrameImplicationComponent

  sevenIsStructuralCMRamifiedPrime :
    FrameImplicationComponent

canonicalSSP15Primes :
  List Nat
canonicalSSP15Primes =
  2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19 ∷ 23 ∷ 29 ∷ 31 ∷ 41 ∷ 47 ∷ 59 ∷ 71 ∷ []

canonicalQsqrtMinusSevenSplitPrimes :
  List Nat
canonicalQsqrtMinusSevenSplitPrimes =
  2 ∷ 11 ∷ 23 ∷ 29 ∷ 71 ∷ []

canonicalQsqrtMinusSevenInertPrimes :
  List Nat
canonicalQsqrtMinusSevenInertPrimes =
  3 ∷ 5 ∷ 13 ∷ 17 ∷ 19 ∷ 31 ∷ 41 ∷ 47 ∷ 59 ∷ []

canonicalQsqrtMinusSevenRamifiedPrimes :
  List Nat
canonicalQsqrtMinusSevenRamifiedPrimes =
  7 ∷ []

canonicalFrameImplicationComponents :
  List FrameImplicationComponent
canonicalFrameImplicationComponents =
  splitPrimesContributeTwoOMinusSevenComponents
  ∷ inertPrimesRequireDegreeTwoPhaseInfo
  ∷ sevenIsStructuralCMRamifiedPrime
  ∷ []

cmFieldTableStatement :
  String
cmFieldTableStatement =
  "Q(sqrt(-7)) over the 15 SSP primes has split {2,11,23,29,71}, inert {3,5,13,17,19,31,41,47,59}, and ramified {7}."

atomGrammarBoundaryStatement :
  String
atomGrammarBoundaryStatement =
  "The 7+7+1 atom grammar is not the CM-field splitting theorem; the two receipts record distinct structures."

frameImplicationStatement :
  String
frameImplicationStatement =
  "Frame implication: 5 split, 9 inert, 1 ramified; split primes give two O_-7 components, inert primes require degree-2/phase information, and p=7 is structural CM ramified."

data SSP15CMFieldSplittingCorrectionPromotion : Set where

ssp15CMFieldSplittingCorrectionPromotionImpossibleHere :
  SSP15CMFieldSplittingCorrectionPromotion →
  ⊥
ssp15CMFieldSplittingCorrectionPromotionImpossibleHere ()

record SSP15CMFieldSplittingCorrectionReceipt : Setω where
  field
    status :
      SSP15CMFieldSplittingCorrectionStatus

    statusIsCanonical :
      status ≡ qsqrtMinusSevenSSP15SplittingCorrectionRecorded

    cmField :
      String

    cmFieldIsQsqrtMinusSeven :
      cmField ≡ "Q(sqrt(-7))"

    ssp15Primes :
      List Nat

    ssp15PrimesAreCanonical :
      ssp15Primes ≡ canonicalSSP15Primes

    splitPrimes :
      List Nat

    splitPrimesAreCanonical :
      splitPrimes ≡ canonicalQsqrtMinusSevenSplitPrimes

    splitCount :
      Nat

    splitCountIsFive :
      splitCount ≡ 5

    inertPrimes :
      List Nat

    inertPrimesAreCanonical :
      inertPrimes ≡ canonicalQsqrtMinusSevenInertPrimes

    inertCount :
      Nat

    inertCountIsNine :
      inertCount ≡ 9

    ramifiedPrimes :
      List Nat

    ramifiedPrimesAreCanonical :
      ramifiedPrimes ≡ canonicalQsqrtMinusSevenRamifiedPrimes

    ramifiedCount :
      Nat

    ramifiedCountIsOne :
      ramifiedCount ≡ 1

    p71SplittingClass :
      CMPrimeSplittingClass

    p71SplittingClassIsSplit :
      p71SplittingClass ≡ split

    p71SplitsNotInert :
      Bool

    p71SplitsNotInertIsTrue :
      p71SplitsNotInert ≡ true

    p71IsSplitAndLargestSSPPrime :
      Bool

    p71IsSplitAndLargestSSPPrimeIsTrue :
      p71IsSplitAndLargestSSPPrime ≡ true

    sevenSplittingClass :
      CMPrimeSplittingClass

    sevenSplittingClassIsRamified :
      sevenSplittingClass ≡ ramified

    sevenPlusSevenPlusOneIsAtomGrammarNotCMField :
      Bool

    sevenPlusSevenPlusOneIsAtomGrammarNotCMFieldIsTrue :
      sevenPlusSevenPlusOneIsAtomGrammarNotCMField ≡ true

    cmFieldTheoremDistinctFromAtomGrammar :
      Bool

    cmFieldTheoremDistinctFromAtomGrammarIsTrue :
      cmFieldTheoremDistinctFromAtomGrammar ≡ true

    frameBoundDecomposesAs_5split_9inert_1ramified :
      Bool

    frameBoundDecomposesAs_5split_9inert_1ramifiedIsTrue :
      frameBoundDecomposesAs_5split_9inert_1ramified ≡ true

    frameImplicationComponents :
      List FrameImplicationComponent

    frameImplicationComponentsAreCanonical :
      frameImplicationComponents ≡ canonicalFrameImplicationComponents

    splitPrimeComponentCount :
      Nat

    splitPrimeComponentCountIsTwoPerSplitPrime :
      splitPrimeComponentCount ≡ 2

    inertPrimeRequiresDegreeTwoPhaseInfo :
      Bool

    inertPrimeRequiresDegreeTwoPhaseInfoIsTrue :
      inertPrimeRequiresDegreeTwoPhaseInfo ≡ true

    p7IsStructuralCMRamifiedPrime :
      Bool

    p7IsStructuralCMRamifiedPrimeIsTrue :
      p7IsStructuralCMRamifiedPrime ≡ true

    cmFieldTableBoundary :
      String

    cmFieldTableBoundaryIsCanonical :
      cmFieldTableBoundary ≡ cmFieldTableStatement

    atomGrammarBoundary :
      String

    atomGrammarBoundaryIsCanonical :
      atomGrammarBoundary ≡ atomGrammarBoundaryStatement

    frameImplicationBoundary :
      String

    frameImplicationBoundaryIsCanonical :
      frameImplicationBoundary ≡ frameImplicationStatement

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionFlags :
      List SSP15CMFieldSplittingCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    promotionImpossibleHere :
      SSP15CMFieldSplittingCorrectionPromotion →
      ⊥

open SSP15CMFieldSplittingCorrectionReceipt public

canonicalSSP15CMFieldSplittingCorrectionReceipt :
  SSP15CMFieldSplittingCorrectionReceipt
canonicalSSP15CMFieldSplittingCorrectionReceipt =
  record
    { status =
        qsqrtMinusSevenSSP15SplittingCorrectionRecorded
    ; statusIsCanonical =
        refl
    ; cmField =
        "Q(sqrt(-7))"
    ; cmFieldIsQsqrtMinusSeven =
        refl
    ; ssp15Primes =
        canonicalSSP15Primes
    ; ssp15PrimesAreCanonical =
        refl
    ; splitPrimes =
        canonicalQsqrtMinusSevenSplitPrimes
    ; splitPrimesAreCanonical =
        refl
    ; splitCount =
        5
    ; splitCountIsFive =
        refl
    ; inertPrimes =
        canonicalQsqrtMinusSevenInertPrimes
    ; inertPrimesAreCanonical =
        refl
    ; inertCount =
        9
    ; inertCountIsNine =
        refl
    ; ramifiedPrimes =
        canonicalQsqrtMinusSevenRamifiedPrimes
    ; ramifiedPrimesAreCanonical =
        refl
    ; ramifiedCount =
        1
    ; ramifiedCountIsOne =
        refl
    ; p71SplittingClass =
        split
    ; p71SplittingClassIsSplit =
        refl
    ; p71SplitsNotInert =
        true
    ; p71SplitsNotInertIsTrue =
        refl
    ; p71IsSplitAndLargestSSPPrime =
        true
    ; p71IsSplitAndLargestSSPPrimeIsTrue =
        refl
    ; sevenSplittingClass =
        ramified
    ; sevenSplittingClassIsRamified =
        refl
    ; sevenPlusSevenPlusOneIsAtomGrammarNotCMField =
        true
    ; sevenPlusSevenPlusOneIsAtomGrammarNotCMFieldIsTrue =
        refl
    ; cmFieldTheoremDistinctFromAtomGrammar =
        true
    ; cmFieldTheoremDistinctFromAtomGrammarIsTrue =
        refl
    ; frameBoundDecomposesAs_5split_9inert_1ramified =
        true
    ; frameBoundDecomposesAs_5split_9inert_1ramifiedIsTrue =
        refl
    ; frameImplicationComponents =
        canonicalFrameImplicationComponents
    ; frameImplicationComponentsAreCanonical =
        refl
    ; splitPrimeComponentCount =
        2
    ; splitPrimeComponentCountIsTwoPerSplitPrime =
        refl
    ; inertPrimeRequiresDegreeTwoPhaseInfo =
        true
    ; inertPrimeRequiresDegreeTwoPhaseInfoIsTrue =
        refl
    ; p7IsStructuralCMRamifiedPrime =
        true
    ; p7IsStructuralCMRamifiedPrimeIsTrue =
        refl
    ; cmFieldTableBoundary =
        cmFieldTableStatement
    ; cmFieldTableBoundaryIsCanonical =
        refl
    ; atomGrammarBoundary =
        atomGrammarBoundaryStatement
    ; atomGrammarBoundaryIsCanonical =
        refl
    ; frameImplicationBoundary =
        frameImplicationStatement
    ; frameImplicationBoundaryIsCanonical =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; promotionImpossibleHere =
        ssp15CMFieldSplittingCorrectionPromotionImpossibleHere
    }
