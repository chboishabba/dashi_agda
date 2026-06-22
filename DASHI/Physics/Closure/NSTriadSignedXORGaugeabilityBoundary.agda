module DASHI.Physics.Closure.NSTriadSignedXORGaugeabilityBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed Wall 1a signed mod-2 gaugeability boundary.
--
-- This receipt records the current Wall 1a route as a signed XOR
-- gaugeability boundary.  It separates the empirical sign-balance cue from
-- the actual obstruction surface:
--
--   sign balance does not imply frustration
--   gaugeable signed XOR is satisfiable
--   non-gaugeable signed XOR is the obstruction surface
--   weighted distance d_W(b, im B₂) is the quantitative target
--
-- No theorem, full-NS, or Clay promotion is claimed here.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadSignedXORGaugeabilityBoundaryStatus : Set where
  wall1aSignedXORGaugeabilityBoundaryRecorded :
    NSTriadSignedXORGaugeabilityBoundaryStatus

data NSTriadSignedXORGaugeabilityBoundaryRow : Set where
  signBalanceDoesNotImplyFrustrationRecorded :
    NSTriadSignedXORGaugeabilityBoundaryRow
  gaugeableSignedXORSatisfiableRecorded :
    NSTriadSignedXORGaugeabilityBoundaryRow
  nonGaugeableSignedXORIsActualObstructionSurfaceRecorded :
    NSTriadSignedXORGaugeabilityBoundaryRow
  weightedDistanceTargetRecorded :
    NSTriadSignedXORGaugeabilityBoundaryRow
  failClosedPromotionWallRecorded :
    NSTriadSignedXORGaugeabilityBoundaryRow

canonicalNSTriadSignedXORGaugeabilityBoundaryRows :
  List NSTriadSignedXORGaugeabilityBoundaryRow
canonicalNSTriadSignedXORGaugeabilityBoundaryRows =
  signBalanceDoesNotImplyFrustrationRecorded
  ∷ gaugeableSignedXORSatisfiableRecorded
  ∷ nonGaugeableSignedXORIsActualObstructionSurfaceRecorded
  ∷ weightedDistanceTargetRecorded
  ∷ failClosedPromotionWallRecorded
  ∷ []

nSTriadSignedXORGaugeabilityBoundaryRowCount : Nat
nSTriadSignedXORGaugeabilityBoundaryRowCount =
  listLength canonicalNSTriadSignedXORGaugeabilityBoundaryRows

nSTriadSignedXORGaugeabilityBoundaryRowCountIs5 :
  nSTriadSignedXORGaugeabilityBoundaryRowCount ≡ 5
nSTriadSignedXORGaugeabilityBoundaryRowCountIs5 = refl

data NSTriadSignedXORGaugeabilityBoundaryGap : Set where
  signBalanceDoesNotForceFrustration :
    NSTriadSignedXORGaugeabilityBoundaryGap
  gaugeableSignedXORStillNeedsWitness :
    NSTriadSignedXORGaugeabilityBoundaryGap
  nonGaugeableSignedXORIsTheActualObstructionSurface :
    NSTriadSignedXORGaugeabilityBoundaryGap
  weightedDistanceTargetNotYetProved :
    NSTriadSignedXORGaugeabilityBoundaryGap
  theoremFullNSClayPromotionRemainFalse :
    NSTriadSignedXORGaugeabilityBoundaryGap

canonicalNSTriadSignedXORGaugeabilityBoundaryGaps :
  List NSTriadSignedXORGaugeabilityBoundaryGap
canonicalNSTriadSignedXORGaugeabilityBoundaryGaps =
  signBalanceDoesNotForceFrustration
  ∷ gaugeableSignedXORStillNeedsWitness
  ∷ nonGaugeableSignedXORIsTheActualObstructionSurface
  ∷ weightedDistanceTargetNotYetProved
  ∷ theoremFullNSClayPromotionRemainFalse
  ∷ []

nSTriadSignedXORGaugeabilityBoundaryGapCount : Nat
nSTriadSignedXORGaugeabilityBoundaryGapCount =
  listLength canonicalNSTriadSignedXORGaugeabilityBoundaryGaps

nSTriadSignedXORGaugeabilityBoundaryGapCountIs5 :
  nSTriadSignedXORGaugeabilityBoundaryGapCount ≡ 5
nSTriadSignedXORGaugeabilityBoundaryGapCountIs5 = refl

canonicalWeightedDistanceTargetText : String
canonicalWeightedDistanceTargetText =
  "d_W(b, im B₂)"

canonicalOText : String
canonicalOText =
  "O: record the Wall 1a signed mod-2 gaugeability boundary as a fail-closed receipt."

canonicalRText : String
canonicalRText =
  "R: separate sign balance from frustration, record satisfiable gaugeable signed XOR, and isolate non-gaugeable signed XOR as the actual obstruction surface."

canonicalCText : String
canonicalCText =
  "C: export canonical rows, gaps, and false promotion gates with the weighted-distance target d_W(b, im B₂) in view."

canonicalSText : String
canonicalSText =
  "S: sign balance does not imply frustration; gaugeable signed XOR is satisfiable; the non-gaugeable signed XOR obstruction surface remains empirical."

canonicalLText : String
canonicalLText =
  "L: sign balance -> gaugeable signed XOR satisfiable -> non-gaugeable signed XOR obstruction surface -> weighted distance d_W(b, im B₂) -> fail-closed Wall 1a gate."

canonicalPText : String
canonicalPText =
  "P: keep the Wall 1a signed-XOR route candidate-only; do not promote theorem, full-NS, or Clay status."

canonicalGText : String
canonicalGText =
  "G: theorem, full-NS, and Clay promotion remain false."

canonicalFText : String
canonicalFText =
  "F: the missing evidence is a proof that the weighted distance d_W(b, im B₂) vanishes only on gaugeable signed XOR data."

record NSTriadSignedXORGaugeabilityBoundaryORCSLPGF : Set where
  constructor mkNSTriadSignedXORGaugeabilityBoundaryORCSLPGF
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

open NSTriadSignedXORGaugeabilityBoundaryORCSLPGF public

canonicalNSTriadSignedXORGaugeabilityBoundaryORCSLPGF :
  NSTriadSignedXORGaugeabilityBoundaryORCSLPGF
canonicalNSTriadSignedXORGaugeabilityBoundaryORCSLPGF =
  mkNSTriadSignedXORGaugeabilityBoundaryORCSLPGF
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

data NSTriadSignedXORGaugeabilityBoundaryPromotion : Set where

promotionImpossibleHere :
  NSTriadSignedXORGaugeabilityBoundaryPromotion → ⊥
promotionImpossibleHere ()

record NSTriadSignedXORGaugeabilityBoundary : Setω where
  constructor mkNSTriadSignedXORGaugeabilityBoundary
  field
    status :
      NSTriadSignedXORGaugeabilityBoundaryStatus
    statusIsCanonical :
      status ≡ wall1aSignedXORGaugeabilityBoundaryRecorded

    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadSignedXORGaugeabilityBoundary"

    weightedDistanceTarget :
      String
    weightedDistanceTargetIsCanonical :
      weightedDistanceTarget ≡ canonicalWeightedDistanceTargetText

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    signBalanceDoesNotImplyFrustration :
      Bool
    signBalanceDoesNotImplyFrustrationIsTrue :
      signBalanceDoesNotImplyFrustration ≡ true

    gaugeableSignedXORSatisfiable :
      Bool
    gaugeableSignedXORSatisfiableIsTrue :
      gaugeableSignedXORSatisfiable ≡ true

    nonGaugeableSignedXORIsActualObstructionSurface :
      Bool
    nonGaugeableSignedXORIsActualObstructionSurfaceIsTrue :
      nonGaugeableSignedXORIsActualObstructionSurface ≡ true

    weightedDistanceTargetIsQuantitative :
      Bool
    weightedDistanceTargetIsQuantitativeIsTrue :
      weightedDistanceTargetIsQuantitative ≡ true

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

    promotionWitness :
      NSTriadSignedXORGaugeabilityBoundaryPromotion → ⊥

    orcslpgf :
      NSTriadSignedXORGaugeabilityBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadSignedXORGaugeabilityBoundaryORCSLPGF

    rows :
      List NSTriadSignedXORGaugeabilityBoundaryRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadSignedXORGaugeabilityBoundaryRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nSTriadSignedXORGaugeabilityBoundaryRowCount

    gaps :
      List NSTriadSignedXORGaugeabilityBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadSignedXORGaugeabilityBoundaryGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nSTriadSignedXORGaugeabilityBoundaryGapCount

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only Wall 1a signed mod-2 gaugeability boundary: sign balance does not imply frustration, gaugeable signed XOR is satisfiable, non-gaugeable signed XOR is the obstruction surface, and the quantitative target is d_W(b, im B₂); theorem/full-NS/Clay flags stay false."

canonicalNSTriadSignedXORGaugeabilityBoundary :
  NSTriadSignedXORGaugeabilityBoundary
canonicalNSTriadSignedXORGaugeabilityBoundary =
  mkNSTriadSignedXORGaugeabilityBoundary
    wall1aSignedXORGaugeabilityBoundaryRecorded
    refl
    "NSTriadSignedXORGaugeabilityBoundary"
    refl
    canonicalWeightedDistanceTargetText
    refl
    true
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
    promotionImpossibleHere
    canonicalNSTriadSignedXORGaugeabilityBoundaryORCSLPGF
    refl
    canonicalNSTriadSignedXORGaugeabilityBoundaryRows
    refl
    nSTriadSignedXORGaugeabilityBoundaryRowCount
    refl
    canonicalNSTriadSignedXORGaugeabilityBoundaryGaps
    refl
    nSTriadSignedXORGaugeabilityBoundaryGapCount
    refl
    "Candidate-only Wall 1a signed mod-2 gaugeability boundary: sign balance does not imply frustration, gaugeable signed XOR is satisfiable, non-gaugeable signed XOR is the obstruction surface, and the quantitative target is d_W(b, im B₂); theorem/full-NS/Clay flags stay false."
    refl
