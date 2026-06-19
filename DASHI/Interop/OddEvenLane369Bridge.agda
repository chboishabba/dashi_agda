module DASHI.Interop.OddEvenLane369Bridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.ParityLaneOperatorCore as Parity
import DASHI.Interop.PNFHyperfabric369 as H369

------------------------------------------------------------------------
-- Odd/even/unresolved lane bridge for the 369 presentation surface.
--
-- This module is candidate-only.  It records a presentation bridge from
-- odd/even/unresolved lane classification to 3/6/9 labels, with a 6-face
-- probe/measure surface and a 9-cell receipt grid.  The bridge uses the
-- existing 369 hyperfabric dimensions where that is structurally safe:
-- H369.nonaryDimension and H369.dialecticDiscussionAtomDimension.
--
-- It does not prove supergeometry, and it does not carry authority.

data LaneClassification : Set where
  oddLaneClass :
    LaneClassification

  evenLaneClass :
    LaneClassification

  unresolvedLaneClass :
    LaneClassification

data LanePresentationLabel369 : Set where
  presentationLabel3 :
    LanePresentationLabel369

  presentationLabel6 :
    LanePresentationLabel369

  presentationLabel9 :
    LanePresentationLabel369

data ProbeMeasureFace : Set where
  oddProbeFace :
    ProbeMeasureFace

  oddMeasureFace :
    ProbeMeasureFace

  evenProbeFace :
    ProbeMeasureFace

  evenMeasureFace :
    ProbeMeasureFace

  unresolvedProbeFace :
    ProbeMeasureFace

  unresolvedMeasureFace :
    ProbeMeasureFace

data ReceiptGridCell : Set where
  oddPresentation3Cell :
    ReceiptGridCell

  oddPresentation6Cell :
    ReceiptGridCell

  oddPresentation9Cell :
    ReceiptGridCell

  evenPresentation3Cell :
    ReceiptGridCell

  evenPresentation6Cell :
    ReceiptGridCell

  evenPresentation9Cell :
    ReceiptGridCell

  unresolvedPresentation3Cell :
    ReceiptGridCell

  unresolvedPresentation6Cell :
    ReceiptGridCell

  unresolvedPresentation9Cell :
    ReceiptGridCell

laneClassToPresentationLabel369 :
  LaneClassification →
  LanePresentationLabel369
laneClassToPresentationLabel369 oddLaneClass =
  presentationLabel3
laneClassToPresentationLabel369 evenLaneClass =
  presentationLabel6
laneClassToPresentationLabel369 unresolvedLaneClass =
  presentationLabel9

faceToPresentationLabel369 :
  ProbeMeasureFace →
  LanePresentationLabel369
faceToPresentationLabel369 oddProbeFace =
  presentationLabel3
faceToPresentationLabel369 oddMeasureFace =
  presentationLabel3
faceToPresentationLabel369 evenProbeFace =
  presentationLabel6
faceToPresentationLabel369 evenMeasureFace =
  presentationLabel6
faceToPresentationLabel369 unresolvedProbeFace =
  presentationLabel9
faceToPresentationLabel369 unresolvedMeasureFace =
  presentationLabel9

receiptCellToLaneClassification :
  ReceiptGridCell →
  LaneClassification
receiptCellToLaneClassification oddPresentation3Cell =
  oddLaneClass
receiptCellToLaneClassification oddPresentation6Cell =
  oddLaneClass
receiptCellToLaneClassification oddPresentation9Cell =
  oddLaneClass
receiptCellToLaneClassification evenPresentation3Cell =
  evenLaneClass
receiptCellToLaneClassification evenPresentation6Cell =
  evenLaneClass
receiptCellToLaneClassification evenPresentation9Cell =
  evenLaneClass
receiptCellToLaneClassification unresolvedPresentation3Cell =
  unresolvedLaneClass
receiptCellToLaneClassification unresolvedPresentation6Cell =
  unresolvedLaneClass
receiptCellToLaneClassification unresolvedPresentation9Cell =
  unresolvedLaneClass

receiptCellToPresentationLabel369 :
  ReceiptGridCell →
  LanePresentationLabel369
receiptCellToPresentationLabel369 oddPresentation3Cell =
  presentationLabel3
receiptCellToPresentationLabel369 oddPresentation6Cell =
  presentationLabel6
receiptCellToPresentationLabel369 oddPresentation9Cell =
  presentationLabel9
receiptCellToPresentationLabel369 evenPresentation3Cell =
  presentationLabel3
receiptCellToPresentationLabel369 evenPresentation6Cell =
  presentationLabel6
receiptCellToPresentationLabel369 evenPresentation9Cell =
  presentationLabel9
receiptCellToPresentationLabel369 unresolvedPresentation3Cell =
  presentationLabel3
receiptCellToPresentationLabel369 unresolvedPresentation6Cell =
  presentationLabel6
receiptCellToPresentationLabel369 unresolvedPresentation9Cell =
  presentationLabel9

canonicalLaneClassifications : List LaneClassification
canonicalLaneClassifications =
  oddLaneClass
  ∷ evenLaneClass
  ∷ unresolvedLaneClass
  ∷ []

canonicalProbeMeasureFaces : List ProbeMeasureFace
canonicalProbeMeasureFaces =
  oddProbeFace
  ∷ oddMeasureFace
  ∷ evenProbeFace
  ∷ evenMeasureFace
  ∷ unresolvedProbeFace
  ∷ unresolvedMeasureFace
  ∷ []

canonicalReceiptGrid : List ReceiptGridCell
canonicalReceiptGrid =
  oddPresentation3Cell
  ∷ oddPresentation6Cell
  ∷ oddPresentation9Cell
  ∷ evenPresentation3Cell
  ∷ evenPresentation6Cell
  ∷ evenPresentation9Cell
  ∷ unresolvedPresentation3Cell
  ∷ unresolvedPresentation6Cell
  ∷ unresolvedPresentation9Cell
  ∷ []

laneClassCount : Nat
laneClassCount = 3

probeMeasureFaceCount : Nat
probeMeasureFaceCount = 6

receiptGridCount : Nat
receiptGridCount = H369.nonaryDimension

receiptPresentationAtomCount : Nat
receiptPresentationAtomCount = H369.dialecticDiscussionAtomDimension

laneClassCountIsThree :
  laneClassCount ≡ 3
laneClassCountIsThree =
  refl

probeMeasureFaceCountIsSix :
  probeMeasureFaceCount ≡ 6
probeMeasureFaceCountIsSix =
  refl

receiptGridCountIsNine :
  receiptGridCount ≡ 9
receiptGridCountIsNine =
  H369.nonaryDimensionIsNine

receiptPresentationAtomCountIsTwentySeven :
  receiptPresentationAtomCount ≡ 27
receiptPresentationAtomCountIsTwentySeven =
  H369.dialecticDiscussionAtomDimensionIsTwentySeven

laneClassOddLabelIs3 :
  laneClassToPresentationLabel369 oddLaneClass ≡ presentationLabel3
laneClassOddLabelIs3 =
  refl

laneClassEvenLabelIs6 :
  laneClassToPresentationLabel369 evenLaneClass ≡ presentationLabel6
laneClassEvenLabelIs6 =
  refl

laneClassUnresolvedLabelIs9 :
  laneClassToPresentationLabel369 unresolvedLaneClass ≡ presentationLabel9
laneClassUnresolvedLabelIs9 =
  refl

oddProbeFaceLabelIs3 :
  faceToPresentationLabel369 oddProbeFace ≡ presentationLabel3
oddProbeFaceLabelIs3 =
  refl

oddMeasureFaceLabelIs3 :
  faceToPresentationLabel369 oddMeasureFace ≡ presentationLabel3
oddMeasureFaceLabelIs3 =
  refl

evenProbeFaceLabelIs6 :
  faceToPresentationLabel369 evenProbeFace ≡ presentationLabel6
evenProbeFaceLabelIs6 =
  refl

evenMeasureFaceLabelIs6 :
  faceToPresentationLabel369 evenMeasureFace ≡ presentationLabel6
evenMeasureFaceLabelIs6 =
  refl

unresolvedProbeFaceLabelIs9 :
  faceToPresentationLabel369 unresolvedProbeFace ≡ presentationLabel9
unresolvedProbeFaceLabelIs9 =
  refl

unresolvedMeasureFaceLabelIs9 :
  faceToPresentationLabel369 unresolvedMeasureFace ≡ presentationLabel9
unresolvedMeasureFaceLabelIs9 =
  refl

record OddEvenLane369Receipt : Set where
  constructor oddEvenLane369Receipt
  field
    receiptLabel :
      String

    laneClassifications :
      List LaneClassification

    laneClassificationsAreCanonical :
      laneClassifications ≡ canonicalLaneClassifications

    probeMeasureFaces :
      List ProbeMeasureFace

    probeMeasureFacesAreCanonical :
      probeMeasureFaces ≡ canonicalProbeMeasureFaces

    receiptGrid :
      List ReceiptGridCell

    receiptGridAreCanonical :
      receiptGrid ≡ canonicalReceiptGrid

    laneClassCountWitness :
      Nat

    laneClassCountWitnessIsThree :
      laneClassCountWitness ≡ laneClassCount

    probeMeasureFaceCountWitness :
      Nat

    probeMeasureFaceCountWitnessIsSix :
      probeMeasureFaceCountWitness ≡ probeMeasureFaceCount

    receiptGridCountWitness :
      Nat

    receiptGridCountWitnessIsNine :
      receiptGridCountWitness ≡ receiptGridCount

    presentationAtomCountWitness :
      Nat

    presentationAtomCountWitnessIsTwentySeven :
      presentationAtomCountWitness ≡ receiptPresentationAtomCount

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    authority :
      Bool

    authorityIsFalse :
      authority ≡ false

    supergeometryProved :
      Bool

    supergeometryProvedIsFalse :
      supergeometryProved ≡ false

    presentationReading :
      String

    receiptStatement :
      String

open OddEvenLane369Receipt public

canonicalOddEvenLane369Receipt : OddEvenLane369Receipt
canonicalOddEvenLane369Receipt =
  oddEvenLane369Receipt
    "odd-even-unresolved 369 presentation receipt"
    canonicalLaneClassifications
    refl
    canonicalProbeMeasureFaces
    refl
    canonicalReceiptGrid
    refl
    laneClassCount
    refl
    probeMeasureFaceCount
    refl
    receiptGridCount
    refl
    receiptPresentationAtomCount
    refl
    true
    refl
    false
    refl
    false
    refl
    "369 presentation reads odd, even, and unresolved lanes as 3 labels, 6 probe/measure faces, and 9 receipt cells"
    "Candidate-only bridge surface; authority is false and supergeometry is not proved here"

canonicalReceiptLabel :
  receiptLabel canonicalOddEvenLane369Receipt
  ≡
  "odd-even-unresolved 369 presentation receipt"
canonicalReceiptLabel =
  refl

canonicalReceiptCandidateOnlyIsTrue :
  candidateOnly canonicalOddEvenLane369Receipt ≡ true
canonicalReceiptCandidateOnlyIsTrue =
  refl

canonicalReceiptAuthorityIsFalse :
  authority canonicalOddEvenLane369Receipt ≡ false
canonicalReceiptAuthorityIsFalse =
  refl

canonicalReceiptSupergeometryIsFalse :
  supergeometryProved canonicalOddEvenLane369Receipt ≡ false
canonicalReceiptSupergeometryIsFalse =
  refl

canonicalReceiptLaneClassesAreCanonical :
  laneClassifications canonicalOddEvenLane369Receipt
  ≡
  canonicalLaneClassifications
canonicalReceiptLaneClassesAreCanonical =
  refl

canonicalReceiptProbeMeasureFacesAreCanonical :
  probeMeasureFaces canonicalOddEvenLane369Receipt
  ≡
  canonicalProbeMeasureFaces
canonicalReceiptProbeMeasureFacesAreCanonical =
  refl

canonicalReceiptGridIsCanonical :
  receiptGrid canonicalOddEvenLane369Receipt
  ≡
  canonicalReceiptGrid
canonicalReceiptGridIsCanonical =
  refl

canonicalReceiptPresentationAtomCountIsTwentySeven :
  presentationAtomCountWitness canonicalOddEvenLane369Receipt
  ≡
  receiptPresentationAtomCount
canonicalReceiptPresentationAtomCountIsTwentySeven =
  refl

receiptStatementIsCanonical :
  receiptStatement canonicalOddEvenLane369Receipt
  ≡
  "Candidate-only bridge surface; authority is false and supergeometry is not proved here"
receiptStatementIsCanonical =
  refl

laneClassPresentationReading :
  String
laneClassPresentationReading =
  "3 lane classes, 6 probe/measure faces, 9 receipt cells"

laneClassPresentationReadingIsCanonical :
  laneClassPresentationReading
  ≡
  "3 lane classes, 6 probe/measure faces, 9 receipt cells"
laneClassPresentationReadingIsCanonical =
  refl

receipt369PresentationUsesSafeDimensions :
  Nat
receipt369PresentationUsesSafeDimensions =
  H369.nonaryDimension + H369.dialecticDiscussionAtomDimension

receipt369PresentationUsesSafeDimensionsIsCanonical :
  receipt369PresentationUsesSafeDimensions
  ≡
  H369.nonaryDimension + H369.dialecticDiscussionAtomDimension
receipt369PresentationUsesSafeDimensionsIsCanonical =
  refl

receipt369PresentationDimensionNotes : List String
receipt369PresentationDimensionNotes =
  "nonaryDimension anchors the 9-cell grid"
  ∷ "dialecticDiscussionAtomDimension anchors the 27-token presentation atom budget"
  ∷ "authority stays false"
  ∷ "supergeometry is not proved"
  ∷ []

receipt369PresentationDimensionNotesAreCanonical :
  receipt369PresentationDimensionNotes
  ≡
  ( "nonaryDimension anchors the 9-cell grid"
    ∷ "dialecticDiscussionAtomDimension anchors the 27-token presentation atom budget"
    ∷ "authority stays false"
    ∷ "supergeometry is not proved"
    ∷ []
  )
receipt369PresentationDimensionNotesAreCanonical =
  refl

------------------------------------------------------------------------
-- Canonical bridge summary.

canonicalOddEvenLane369BridgeSummary : String
canonicalOddEvenLane369BridgeSummary =
  "Odd/even/unresolved lane classification is presented through 3 labels, 6 probe/measure faces, and a 9-cell receipt grid; the bridge is candidate-only and does not prove supergeometry."

canonicalOddEvenLane369BridgeSummaryIsCanonical :
  canonicalOddEvenLane369BridgeSummary
  ≡
  "Odd/even/unresolved lane classification is presented through 3 labels, 6 probe/measure faces, and a 9-cell receipt grid; the bridge is candidate-only and does not prove supergeometry."
canonicalOddEvenLane369BridgeSummaryIsCanonical =
  refl
