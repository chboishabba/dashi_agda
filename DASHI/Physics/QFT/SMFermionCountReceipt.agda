module DASHI.Physics.QFT.SMFermionCountReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.NoFourthGenerationFromHeegnerExhaustionReceipt as NoFourth
import DASHI.Physics.QFT.SMContentSummaryReceipt as Summary

------------------------------------------------------------------------
-- Standard Model fermion count aggregate receipt.
--
-- This QFT aggregate records the initial lane-count problem only.  The
-- current content map has three quark-lane candidates and three lepton-lane
-- candidates, but an exact Standard-Model fermion count requires additional
-- structure: SU(2) doublets and up/down splitting.  It therefore fails closed
-- and does not claim the exact fermion count.  A separate exact-count receipt
-- may refine this surface without conflict.

data SMFermionCountStatus : Set where
  qftAggregateInitialLaneCountProblem :
    SMFermionCountStatus

data SMFermionCountBlocker : Set where
  laneCountDoesNotEqualExactFermionCount :
    SMFermionCountBlocker

  su2DoubletSplittingRequired :
    SMFermionCountBlocker

  upDownSplittingRequired :
    SMFermionCountBlocker

  chiralityAndAntiparticleAccountingRequired :
    SMFermionCountBlocker

  exactCountReceiptNotConsumedHere :
    SMFermionCountBlocker

canonicalSMFermionCountBlockers :
  List SMFermionCountBlocker
canonicalSMFermionCountBlockers =
  laneCountDoesNotEqualExactFermionCount
  ∷ su2DoubletSplittingRequired
  ∷ upDownSplittingRequired
  ∷ chiralityAndAntiparticleAccountingRequired
  ∷ exactCountReceiptNotConsumedHere
  ∷ []

data SMFermionCountPromotion : Set where

smFermionCountPromotionImpossibleHere :
  SMFermionCountPromotion →
  ⊥
smFermionCountPromotionImpossibleHere ()

smFermionCountBoundaryLabel : String
smFermionCountBoundaryLabel =
  "QFT aggregate records the initial six-lane count problem only; SU(2) doublet and up/down splitting are required before any exact SM fermion count promotion"

record InitialLaneCountProblem : Set where
  field
    quarkLaneCandidateCount :
      Nat

    quarkLaneCandidateCountIsThree :
      quarkLaneCandidateCount ≡ 3

    leptonLaneCandidateCount :
      Nat

    leptonLaneCandidateCountIsThree :
      leptonLaneCandidateCount ≡ 3

    totalMatterLaneCandidateCount :
      Nat

    totalMatterLaneCandidateCountIsSix :
      totalMatterLaneCandidateCount ≡ 6

    laneCountIsOnlyInitialProblem :
      Bool

    laneCountIsOnlyInitialProblemIsTrue :
      laneCountIsOnlyInitialProblem ≡ true

open InitialLaneCountProblem public

canonicalInitialLaneCountProblem :
  InitialLaneCountProblem
canonicalInitialLaneCountProblem =
  record
    { quarkLaneCandidateCount =
        3
    ; quarkLaneCandidateCountIsThree =
        refl
    ; leptonLaneCandidateCount =
        3
    ; leptonLaneCandidateCountIsThree =
        refl
    ; totalMatterLaneCandidateCount =
        6
    ; totalMatterLaneCandidateCountIsSix =
        refl
    ; laneCountIsOnlyInitialProblem =
        true
    ; laneCountIsOnlyInitialProblemIsTrue =
        refl
    }

record SMFermionCountReceipt : Setω where
  field
    smContentSummaryReceipt :
      Summary.SMContentSummaryReceipt

    smContentSummaryReceiptIsCanonical :
      smContentSummaryReceipt
      ≡
      Summary.canonicalSMContentSummaryReceipt

    noFourthGenerationCandidateReceipt :
      NoFourth.NoFourthGenerationFromHeegnerExhaustionReceipt

    noFourthGenerationCandidateReceiptSelectedCanonical :
      Bool

    noFourthGenerationCandidateReceiptSelectedCanonicalIsTrue :
      noFourthGenerationCandidateReceiptSelectedCanonical ≡ true

    status :
      SMFermionCountStatus

    statusIsQFTAggregateInitialLaneCountProblem :
      status ≡ qftAggregateInitialLaneCountProblem

    initialLaneCountProblem :
      InitialLaneCountProblem

    initialLaneCountProblemIsCanonical :
      initialLaneCountProblem ≡ canonicalInitialLaneCountProblem

    qftAggregateOnly :
      Bool

    qftAggregateOnlyIsTrue :
      qftAggregateOnly ≡ true

    su2DoubletSplittingRequiredFlag :
      Bool

    su2DoubletSplittingRequiredFlagIsTrue :
      su2DoubletSplittingRequiredFlag ≡ true

    upDownSplittingRequiredFlag :
      Bool

    upDownSplittingRequiredFlagIsTrue :
      upDownSplittingRequiredFlag ≡ true

    exactSMFermionCountPromoted :
      Bool

    exactSMFermionCountPromotedIsFalse :
      exactSMFermionCountPromoted ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    failClosed :
      Bool

    failClosedIsTrue :
      failClosed ≡ true

    promotionFlags :
      List SMFermionCountPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List SMFermionCountBlocker

    blockersAreCanonical :
      blockers ≡ canonicalSMFermionCountBlockers

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ smFermionCountBoundaryLabel

    auditTrail :
      List String

open SMFermionCountReceipt public

canonicalSMFermionCountReceipt :
  SMFermionCountReceipt
canonicalSMFermionCountReceipt =
  record
    { smContentSummaryReceipt =
        Summary.canonicalSMContentSummaryReceipt
    ; smContentSummaryReceiptIsCanonical =
        refl
    ; noFourthGenerationCandidateReceipt =
        NoFourth.canonicalNoFourthGenerationFromHeegnerExhaustionReceipt
    ; noFourthGenerationCandidateReceiptSelectedCanonical =
        true
    ; noFourthGenerationCandidateReceiptSelectedCanonicalIsTrue =
        refl
    ; status =
        qftAggregateInitialLaneCountProblem
    ; statusIsQFTAggregateInitialLaneCountProblem =
        refl
    ; initialLaneCountProblem =
        canonicalInitialLaneCountProblem
    ; initialLaneCountProblemIsCanonical =
        refl
    ; qftAggregateOnly =
        true
    ; qftAggregateOnlyIsTrue =
        refl
    ; su2DoubletSplittingRequiredFlag =
        true
    ; su2DoubletSplittingRequiredFlagIsTrue =
        refl
    ; upDownSplittingRequiredFlag =
        true
    ; upDownSplittingRequiredFlagIsTrue =
        refl
    ; exactSMFermionCountPromoted =
        false
    ; exactSMFermionCountPromotedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; failClosed =
        true
    ; failClosedIsTrue =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalSMFermionCountBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        smFermionCountBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        "Initial matter-lane count recorded: three quark candidates plus three lepton candidates"
        ∷ "The six-lane aggregate is not an exact Standard Model fermion count"
        ∷ "SU(2) doublet splitting is required"
        ∷ "Up/down splitting is required"
        ∷ "This QFT aggregate fails closed and leaves exact count promotion false"
        ∷ []
    }

smFermionCountRequiresSU2DoubletSplitting :
  su2DoubletSplittingRequiredFlag canonicalSMFermionCountReceipt
  ≡
  true
smFermionCountRequiresSU2DoubletSplitting =
  refl

smFermionCountRequiresUpDownSplitting :
  upDownSplittingRequiredFlag canonicalSMFermionCountReceipt
  ≡
  true
smFermionCountRequiresUpDownSplitting =
  refl

smFermionCountKeepsExactCountFalse :
  exactSMFermionCountPromoted canonicalSMFermionCountReceipt
  ≡
  false
smFermionCountKeepsExactCountFalse =
  refl

smFermionCountFailsClosed :
  failClosed canonicalSMFermionCountReceipt
  ≡
  true
smFermionCountFailsClosed =
  refl
