module DASHI.Physics.Closure.NSTriadCoherenceDeficitFloorBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed NS triad coherence-deficit floor boundary.
--
-- This receipt records only the positive theorem shape:
--
--   if continuous coherence capacity cap_N <= kappa < 1
--   then Wall 1 floor >= (1 - kappa) / 2
--
-- No proof is claimed.  The Schur-complement / frame-gap route is kept
-- separate from this floor theorem ledger, and all promotion flags remain
-- false.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadCoherenceDeficitFloorBoundaryRow : Set where
  positiveTheoremShapeRecorded :
    NSTriadCoherenceDeficitFloorBoundaryRow
  continuousCoherenceCapacityConditionRecorded :
    NSTriadCoherenceDeficitFloorBoundaryRow
  wall1FloorLowerBoundTargetRecorded :
    NSTriadCoherenceDeficitFloorBoundaryRow
  schurFrameGapRouteKeptSeparateRecorded :
    NSTriadCoherenceDeficitFloorBoundaryRow
  failClosedPromotionWallRecorded :
    NSTriadCoherenceDeficitFloorBoundaryRow

rowStatement :
  NSTriadCoherenceDeficitFloorBoundaryRow → String
rowStatement positiveTheoremShapeRecorded =
  "Target: record the positive theorem shape cap_N <= kappa < 1 -> Wall 1 floor >= (1 - kappa) / 2."
rowStatement continuousCoherenceCapacityConditionRecorded =
  "Target: keep the continuous coherence capacity condition cap_N <= kappa < 1 explicit."
rowStatement wall1FloorLowerBoundTargetRecorded =
  "Target: keep the Wall 1 floor lower-bound target visible without promoting a proof."
rowStatement schurFrameGapRouteKeptSeparateRecorded =
  "Target: keep the Schur-complement / frame-gap route separate from the floor theorem."
rowStatement failClosedPromotionWallRecorded =
  "Target: keep theorem, full-NS, and Clay promotion walls closed."

record NSTriadCoherenceDeficitFloorBoundaryRowRecord : Set where
  field
    key :
      NSTriadCoherenceDeficitFloorBoundaryRow
    statement :
      String
    statementIsCanonical :
      statement ≡ rowStatement key

canonicalNSTriadCoherenceDeficitFloorBoundaryRows :
  List NSTriadCoherenceDeficitFloorBoundaryRowRecord
canonicalNSTriadCoherenceDeficitFloorBoundaryRows =
  record
    { key = positiveTheoremShapeRecorded
    ; statement = rowStatement positiveTheoremShapeRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = continuousCoherenceCapacityConditionRecorded
    ; statement = rowStatement continuousCoherenceCapacityConditionRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = wall1FloorLowerBoundTargetRecorded
    ; statement = rowStatement wall1FloorLowerBoundTargetRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = schurFrameGapRouteKeptSeparateRecorded
    ; statement = rowStatement schurFrameGapRouteKeptSeparateRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = failClosedPromotionWallRecorded
    ; statement = rowStatement failClosedPromotionWallRecorded
    ; statementIsCanonical = refl
    }
  ∷ []

nstriadCoherenceDeficitFloorBoundaryRowCount : Nat
nstriadCoherenceDeficitFloorBoundaryRowCount =
  listLength canonicalNSTriadCoherenceDeficitFloorBoundaryRows

nstriadCoherenceDeficitFloorBoundaryRowCountIs5 :
  nstriadCoherenceDeficitFloorBoundaryRowCount ≡ 5
nstriadCoherenceDeficitFloorBoundaryRowCountIs5 =
  refl

data NSTriadCoherenceDeficitFloorBoundaryGap : Set where
  theoremShapeOnlyRecorded :
    NSTriadCoherenceDeficitFloorBoundaryGap
  noProofClaimedRecorded :
    NSTriadCoherenceDeficitFloorBoundaryGap
  schurFrameGapRouteSeparateRecorded :
    NSTriadCoherenceDeficitFloorBoundaryGap
  wall1FloorPromotionFalseRecorded :
    NSTriadCoherenceDeficitFloorBoundaryGap
  theoremAndClayPromotionRemainFalse :
    NSTriadCoherenceDeficitFloorBoundaryGap

canonicalNSTriadCoherenceDeficitFloorBoundaryGaps :
  List NSTriadCoherenceDeficitFloorBoundaryGap
canonicalNSTriadCoherenceDeficitFloorBoundaryGaps =
  theoremShapeOnlyRecorded
  ∷ noProofClaimedRecorded
  ∷ schurFrameGapRouteSeparateRecorded
  ∷ wall1FloorPromotionFalseRecorded
  ∷ theoremAndClayPromotionRemainFalse
  ∷ []

nstriadCoherenceDeficitFloorBoundaryGapCount : Nat
nstriadCoherenceDeficitFloorBoundaryGapCount =
  listLength canonicalNSTriadCoherenceDeficitFloorBoundaryGaps

nstriadCoherenceDeficitFloorBoundaryGapCountIs5 :
  nstriadCoherenceDeficitFloorBoundaryGapCount ≡ 5
nstriadCoherenceDeficitFloorBoundaryGapCountIs5 =
  refl

canonicalTheoremShapeText : String
canonicalTheoremShapeText =
  "If continuous coherence capacity cap_N <= kappa < 1, then Wall 1 floor >= (1 - kappa) / 2."

canonicalOText : String
canonicalOText =
  "O: record the active NS triad coherence-deficit floor boundary as a fail-closed receipt."

canonicalRText : String
canonicalRText =
  "R: isolate the positive theorem shape, the continuous coherence capacity condition, and the Wall 1 floor target without claiming a proof."

canonicalCText : String
canonicalCText =
  "C: expose canonical rows, gaps, the theorem-shape string, and explicit false promotion gates."

canonicalSText : String
canonicalSText =
  "S: the cap_N <= kappa < 1 hypothesis and the Wall 1 floor target are recorded as shape only, while proof remains unclaimed."

canonicalLText : String
canonicalLText =
  "L: continuous coherence capacity cap_N -> kappa < 1 hypothesis -> Wall 1 floor target -> separate Schur/frame-gap ledger -> only then any further route."

canonicalPText : String
canonicalPText =
  "P: keep the floor theorem candidate-only and do not promote the theorem, full-NS, or Clay status."

canonicalGText : String
canonicalGText =
  "G: theorem, full-NS, and Clay promotion remain false."

canonicalFText : String
canonicalFText =
  "F: the missing evidence is a proof of the positive floor implication; the Schur/frame-gap route is not the same claim."

record NSTriadCoherenceDeficitFloorBoundaryORCSLPGF : Set where
  constructor mkNSTriadCoherenceDeficitFloorBoundaryORCSLPGF
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

open NSTriadCoherenceDeficitFloorBoundaryORCSLPGF public

canonicalNSTriadCoherenceDeficitFloorBoundaryORCSLPGF :
  NSTriadCoherenceDeficitFloorBoundaryORCSLPGF
canonicalNSTriadCoherenceDeficitFloorBoundaryORCSLPGF =
  mkNSTriadCoherenceDeficitFloorBoundaryORCSLPGF
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

record NSTriadCoherenceDeficitFloorBoundary : Setω where
  constructor mkNSTriadCoherenceDeficitFloorBoundary
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadCoherenceDeficitFloorBoundary"

    theoremShape :
      String
    theoremShapeIsCanonical :
      theoremShape ≡ canonicalTheoremShapeText

    rows :
      List NSTriadCoherenceDeficitFloorBoundaryRowRecord
    rowsAreCanonical :
      rows ≡ canonicalNSTriadCoherenceDeficitFloorBoundaryRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nstriadCoherenceDeficitFloorBoundaryRowCount

    gaps :
      List NSTriadCoherenceDeficitFloorBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadCoherenceDeficitFloorBoundaryGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nstriadCoherenceDeficitFloorBoundaryGapCount

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    positiveTheoremShapeRecordedHere :
      Bool
    positiveTheoremShapeRecordedHereIsTrue :
      positiveTheoremShapeRecordedHere ≡ true

    positiveFloorProofClaimed :
      Bool
    positiveFloorProofClaimedIsFalse :
      positiveFloorProofClaimed ≡ false

    schurFrameGapClaimedHere :
      Bool
    schurFrameGapClaimedHereIsFalse :
      schurFrameGapClaimedHere ≡ false

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    orcslpgf :
      NSTriadCoherenceDeficitFloorBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadCoherenceDeficitFloorBoundaryORCSLPGF

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only coherence-deficit floor boundary: the theorem shape cap_N <= kappa < 1 -> Wall 1 floor >= (1 - kappa) / 2 is recorded, but no proof is claimed and the Schur/frame-gap route stays separate."

open NSTriadCoherenceDeficitFloorBoundary public

canonicalNSTriadCoherenceDeficitFloorBoundary :
  NSTriadCoherenceDeficitFloorBoundary
canonicalNSTriadCoherenceDeficitFloorBoundary =
  mkNSTriadCoherenceDeficitFloorBoundary
    "NSTriadCoherenceDeficitFloorBoundary"
    refl
    canonicalTheoremShapeText
    refl
    canonicalNSTriadCoherenceDeficitFloorBoundaryRows
    refl
    nstriadCoherenceDeficitFloorBoundaryRowCount
    refl
    canonicalNSTriadCoherenceDeficitFloorBoundaryGaps
    refl
    nstriadCoherenceDeficitFloorBoundaryGapCount
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalNSTriadCoherenceDeficitFloorBoundaryORCSLPGF
    refl
    "Candidate-only coherence-deficit floor boundary: the theorem shape cap_N <= kappa < 1 -> Wall 1 floor >= (1 - kappa) / 2 is recorded, but no proof is claimed and the Schur/frame-gap route stays separate."
    refl
