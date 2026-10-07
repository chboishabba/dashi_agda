module DASHI.Governance.BoloBoloOWSSpokesRateShiftExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact as Transition

------------------------------------------------------------------------
-- DEVELOPMENT-ONLY PRE/POST RATE-SHIFT RECEIPT.
--
-- Raw totals are not directly comparable because there are 35 development GA
-- records before the inaugural Spokes Council and only 3 after it in the
-- frozen corpus window.  For each lexical coordinate we therefore compare
-- rates by exact cross-products:
--
--   postCount / 3  versus  preCount / 35
--
-- using postCount*35 and preCount*3.  No protected holdout is consumed.
------------------------------------------------------------------------

data RateDirection : Set where
  higherAfterSpokes : RateDirection
  lowerAfterSpokes : RateDirection
  sameRate : RateDirection

record RateShiftRow : Set where
  constructor rateShiftRow
  field
    coordinateLabel : String
    preCount : Nat
    postCount : Nat
    postCrossProduct : Nat
    preCrossProduct : Nat
    direction : RateDirection

open RateShiftRow public

reportBackRateShift : RateShiftRow
reportBackRateShift = rateShiftRow "report-back" 24 3 105 72 higherAfterSpokes

delegateRateShift : RateShiftRow
delegateRateShift = rateShiftRow "delegate/delegation" 2 4 140 6 higherAfterSpokes

spokesRateShift : RateShiftRow
spokesRateShift = rateShiftRow "spokes" 65 6 210 195 higherAfterSpokes

liaisonRateShift : RateShiftRow
liaisonRateShift = rateShiftRow "liaison" 4 0 0 12 lowerAfterSpokes

interGroupRateShift : RateShiftRow
interGroupRateShift = rateShiftRow "inter-group" 2 0 0 6 lowerAfterSpokes

mediationRateShift : RateShiftRow
mediationRateShift = rateShiftRow "mediation" 19 1 35 57 lowerAfterSpokes

tabledRateShift : RateShiftRow
tabledRateShift = rateShiftRow "tabled" 15 1 35 45 lowerAfterSpokes

workingGroupRateShift : RateShiftRow
workingGroupRateShift = rateShiftRow "working group" 331 49 1715 993 higherAfterSpokes

canonicalRateShiftRows : List RateShiftRow
canonicalRateShiftRows =
  reportBackRateShift
  ∷ delegateRateShift
  ∷ spokesRateShift
  ∷ liaisonRateShift
  ∷ interGroupRateShift
  ∷ mediationRateShift
  ∷ tabledRateShift
  ∷ workingGroupRateShift
  ∷ []

record DurationDescriptiveSnapshot : Set where
  constructor durationDescriptiveSnapshot
  field
    preDurationRowCount : Nat
    preDurationMeanMinutes : Nat
    preDurationMedianMinutes : Nat
    postDurationRowCount : Nat
    solePostDurationMinutes : Nat

open DurationDescriptiveSnapshot public

canonicalDurationDescriptiveSnapshot : DurationDescriptiveSnapshot
canonicalDurationDescriptiveSnapshot = durationDescriptiveSnapshot 5 231 140 1 220

record RateShiftBoundary : Set where
  constructor rateShiftBoundary
  field
    protectedHoldoutConsumed : Bool
    normalizedLexicalShiftSupportsStructuralTransitionDetection : Bool
    normalizedLexicalShiftIsCoordinationCostEffect : Bool
    directionAfterSpokesIsStatisticallyEstimatedEffect : Bool
    onePostDurationEstablishesDurationChange : Bool
    postWindowIndependentOfEvictionShock : Bool
    lexicalUptakeCanGuidePrimarySpokesMinuteExtraction : Bool

open RateShiftBoundary public

canonicalRateShiftBoundary : RateShiftBoundary
canonicalRateShiftBoundary =
  rateShiftBoundary false true false false false false true

canonicalOWSSpokesRateShiftReceipt : GenericReceipt.GenericReceipt
canonicalOWSSpokesRateShiftReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS Spokes development-only normalized lexical transition receipt"
    "DASHI.Governance.BoloBoloOWSSpokesRateShiftExact"
    "canonicalRateShiftRows / canonicalDurationDescriptiveSnapshot / canonicalRateShiftBoundary"
    "normalizes the 35 pre-Spokes and 3 post-Spokes development GA records by exact cross-products: report-back, delegate/delegation, spokes and working-group vocabulary are denser in the short post-transition window, while liaison, inter-group, mediation and tabled vocabulary are lower; the five pre duration rows average 231 minutes with median 140, versus a sole 220-minute post row"
    "these are DASHI text/descriptive measurements used to verify that the organizational vocabulary changed around the Spokes transition; they are not causal effect estimates, cost reductions, statistical rate estimates or evidence that the post period is free of eviction/time-trend confounding, and the protected 8 November GA holdout remains untouched"
    "agda -i . DASHI/Governance/BoloBoloOWSSpokesRateShiftRegression.agda"
