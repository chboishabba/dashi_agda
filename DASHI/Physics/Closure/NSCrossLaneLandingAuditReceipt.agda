module DASHI.Physics.Closure.NSCrossLaneLandingAuditReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes cross-lane landing audit receipt.
--
-- This receipt records the finite low-band cross-lane landing audit for
-- carrier primes {2,3,7} and bands j,l <= 5.  A landing means that a
-- difference |p^j - q^l| from two distinct carrier lanes is again one of
-- the audited carrier powers.  The listed low-band hits are finite data.
--
-- The number-theoretic theorem used here is Thue-Mahler: for fixed target
-- c, the equation |p^j - q^l| = c has finitely many solutions.  Therefore
-- cross-lane forcing at each fixed band is a finite sum.  This is a finite
-- forcing audit only, not a feedback or closure promotion.
--
-- No Clay Navier-Stokes, global regularity, or terminal promotion is made.

data NSCrossLaneLandingAuditStatus : Set where
  lowBandCarrierPrimeAuditRecorded :
    NSCrossLaneLandingAuditStatus

  explicitLowBandLandingHitsRecorded :
    NSCrossLaneLandingAuditStatus

  thueMahlerFiniteFixedTargetApplied :
    NSCrossLaneLandingAuditStatus

  finiteCrossLaneForcingNotFeedback :
    NSCrossLaneLandingAuditStatus

  noClayOrGlobalTerminalPromotion :
    NSCrossLaneLandingAuditStatus

canonicalNSCrossLaneLandingAuditStatus :
  List NSCrossLaneLandingAuditStatus
canonicalNSCrossLaneLandingAuditStatus =
  lowBandCarrierPrimeAuditRecorded
  ∷ explicitLowBandLandingHitsRecorded
  ∷ thueMahlerFiniteFixedTargetApplied
  ∷ finiteCrossLaneForcingNotFeedback
  ∷ noClayOrGlobalTerminalPromotion
  ∷ []

data CarrierPrime : Set where
  p2 :
    CarrierPrime

  p3 :
    CarrierPrime

  p7 :
    CarrierPrime

data CarrierLandingHit : Set where
  landing :
    (leftPrime : CarrierPrime) →
    (leftBand : Nat) →
    (rightPrime : CarrierPrime) →
    (rightBand : Nat) →
    (targetPrime : CarrierPrime) →
    (targetBand : Nat) →
    (difference : Nat) →
    CarrierLandingHit

landing2-1-3-2-to7-1 :
  CarrierLandingHit
landing2-1-3-2-to7-1 =
  landing p2 1 p3 2 p7 1 7

landing2-4-3-2-to7-1 :
  CarrierLandingHit
landing2-4-3-2-to7-1 =
  landing p2 4 p3 2 p7 1 7

landing2-5-3-4-to7-2 :
  CarrierLandingHit
landing2-5-3-4-to7-2 =
  landing p2 5 p3 4 p7 2 49

landing2-2-7-1-to3-1 :
  CarrierLandingHit
landing2-2-7-1-to3-1 =
  landing p2 2 p7 1 p3 1 3

landing2-4-7-1-to3-2 :
  CarrierLandingHit
landing2-4-7-1-to3-2 =
  landing p2 4 p7 1 p3 2 9

landing3-1-7-1-to2-2 :
  CarrierLandingHit
landing3-1-7-1-to2-2 =
  landing p3 1 p7 1 p2 2 4

landing3-2-7-1-to2-1 :
  CarrierLandingHit
landing3-2-7-1-to2-1 =
  landing p3 2 p7 1 p2 1 2

landing3-4-7-2-to2-5 :
  CarrierLandingHit
landing3-4-7-2-to2-5 =
  landing p3 4 p7 2 p2 5 32

canonicalLowBandLandingHits :
  List CarrierLandingHit
canonicalLowBandLandingHits =
  landing2-1-3-2-to7-1
  ∷ landing2-4-3-2-to7-1
  ∷ landing2-5-3-4-to7-2
  ∷ landing2-2-7-1-to3-1
  ∷ landing2-4-7-1-to3-2
  ∷ landing3-1-7-1-to2-2
  ∷ landing3-2-7-1-to2-1
  ∷ landing3-4-7-2-to2-5
  ∷ []

carrierPrimeSet :
  List CarrierPrime
carrierPrimeSet =
  p2 ∷ p3 ∷ p7 ∷ []

maxAuditedBand :
  Nat
maxAuditedBand =
  5

explicitLowBandLandingTableText :
  List String
explicitLowBandLandingTableText =
  "|2^1-3^2|=7=7^1"
  ∷ "|2^4-3^2|=7=7^1"
  ∷ "|2^5-3^4|=49=7^2"
  ∷ "|2^2-7^1|=3=3^1"
  ∷ "|2^4-7^1|=9=3^2"
  ∷ "|3^1-7^1|=4=2^2"
  ∷ "|3^2-7^1|=2=2^1"
  ∷ "|3^4-7^2|=32=2^5"
  ∷ []

thueMahlerTheoremStatement :
  String
thueMahlerTheoremStatement =
  "Thue-Mahler theorem: for fixed target c, |p^j-q^l|=c has finitely many solutions; hence cross-lane forcing at each fixed band is a finite sum."

crossLaneLandingAuditStatement :
  String
crossLaneLandingAuditStatement =
  "For carrier primes {2,3,7} and bands j,l <= 5, the explicit cross-lane landing hits are finite low-band data. Thue-Mahler gives finite solution sets for each fixed target c, so the cross-lane contribution is finite forcing per band, not feedback or global closure."

data NSCrossLaneLandingPromotion : Set where

nsCrossLaneLandingPromotionImpossibleHere :
  NSCrossLaneLandingPromotion →
  ⊥
nsCrossLaneLandingPromotionImpossibleHere ()

record NSCrossLaneLandingAuditReceipt : Setω where
  field
    status :
      List NSCrossLaneLandingAuditStatus

    statusIsCanonical :
      status ≡ canonicalNSCrossLaneLandingAuditStatus

    auditedCarrierPrimes :
      List CarrierPrime

    auditedCarrierPrimesAreCanonical :
      auditedCarrierPrimes ≡ carrierPrimeSet

    auditedBandBound :
      Nat

    auditedBandBoundIsFive :
      auditedBandBound ≡ maxAuditedBand

    lowBandLandingHits :
      List CarrierLandingHit

    lowBandLandingHitsAreCanonical :
      lowBandLandingHits ≡ canonicalLowBandLandingHits

    explicitLowBandLandingTable :
      List String

    explicitLowBandLandingTableIsCanonical :
      explicitLowBandLandingTable ≡ explicitLowBandLandingTableText

    crossLaneLandingsFinitePerBand :
      Bool

    crossLaneLandingsFinitePerBandIsTrue :
      crossLaneLandingsFinitePerBand ≡ true

    thueMahlerTheoremApplied :
      Bool

    thueMahlerTheoremAppliedIsTrue :
      thueMahlerTheoremApplied ≡ true

    thueMahlerTheorem :
      String

    thueMahlerTheoremIsCanonical :
      thueMahlerTheorem ≡ thueMahlerTheoremStatement

    crossLaneIsFiniteForcingNotFeedback :
      Bool

    crossLaneIsFiniteForcingNotFeedbackIsTrue :
      crossLaneIsFiniteForcingNotFeedback ≡ true

    finiteSumAtEachFixedBand :
      Bool

    finiteSumAtEachFixedBandIsTrue :
      finiteSumAtEachFixedBand ≡ true

    feedbackClosurePromoted :
      Bool

    feedbackClosurePromotedIsFalse :
      feedbackClosurePromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List NSCrossLaneLandingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ crossLaneLandingAuditStatement

    receiptBoundary :
      List String

open NSCrossLaneLandingAuditReceipt public

canonicalNSCrossLaneLandingAuditReceipt :
  NSCrossLaneLandingAuditReceipt
canonicalNSCrossLaneLandingAuditReceipt =
  record
    { status =
        canonicalNSCrossLaneLandingAuditStatus
    ; statusIsCanonical =
        refl
    ; auditedCarrierPrimes =
        carrierPrimeSet
    ; auditedCarrierPrimesAreCanonical =
        refl
    ; auditedBandBound =
        maxAuditedBand
    ; auditedBandBoundIsFive =
        refl
    ; lowBandLandingHits =
        canonicalLowBandLandingHits
    ; lowBandLandingHitsAreCanonical =
        refl
    ; explicitLowBandLandingTable =
        explicitLowBandLandingTableText
    ; explicitLowBandLandingTableIsCanonical =
        refl
    ; crossLaneLandingsFinitePerBand =
        true
    ; crossLaneLandingsFinitePerBandIsTrue =
        refl
    ; thueMahlerTheoremApplied =
        true
    ; thueMahlerTheoremAppliedIsTrue =
        refl
    ; thueMahlerTheorem =
        thueMahlerTheoremStatement
    ; thueMahlerTheoremIsCanonical =
        refl
    ; crossLaneIsFiniteForcingNotFeedback =
        true
    ; crossLaneIsFiniteForcingNotFeedbackIsTrue =
        refl
    ; finiteSumAtEachFixedBand =
        true
    ; finiteSumAtEachFixedBandIsTrue =
        refl
    ; feedbackClosurePromoted =
        false
    ; feedbackClosurePromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        crossLaneLandingAuditStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Audit scope: carrier primes {2,3,7}; source bands j,l <= 5"
        ∷ "Explicit hits include |2^1-3^2|=7, |2^4-3^2|=7, |2^5-3^4|=49, and |3^4-7^2|=32"
        ∷ "All listed low-band landings are finite table data, not a recurrence or feedback closure"
        ∷ "Thue-Mahler is applied only as fixed-target finiteness for |p^j-q^l|=c"
        ∷ "crossLaneLandingsFinitePerBand=true"
        ∷ "crossLaneIsFiniteForcingNotFeedback=true"
        ∷ "No Clay Navier-Stokes, global regularity, or terminal promotion is made"
        ∷ []
    }

nsCrossLaneLandingsFinitePerBand :
  crossLaneLandingsFinitePerBand canonicalNSCrossLaneLandingAuditReceipt
  ≡
  true
nsCrossLaneLandingsFinitePerBand =
  refl

nsCrossLaneLandingThueMahlerApplied :
  thueMahlerTheoremApplied canonicalNSCrossLaneLandingAuditReceipt
  ≡
  true
nsCrossLaneLandingThueMahlerApplied =
  refl

nsCrossLaneLandingFiniteForcingNotFeedback :
  crossLaneIsFiniteForcingNotFeedback canonicalNSCrossLaneLandingAuditReceipt
  ≡
  true
nsCrossLaneLandingFiniteForcingNotFeedback =
  refl

nsCrossLaneLandingDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSCrossLaneLandingAuditReceipt
  ≡
  false
nsCrossLaneLandingDoesNotPromoteClay =
  refl

nsCrossLaneLandingDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSCrossLaneLandingAuditReceipt
  ≡
  false
nsCrossLaneLandingDoesNotPromoteGlobalRegularity =
  refl

nsCrossLaneLandingDoesNotPromoteTerminalClay :
  terminalClayClaimPromoted canonicalNSCrossLaneLandingAuditReceipt
  ≡
  false
nsCrossLaneLandingDoesNotPromoteTerminalClay =
  refl
