module DASHI.Analysis.RiemannG2GammaMatchedQuantitativeGainLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- QUANTITATIVE MATCHED GAMMA/POLE RATIO GAIN
--
-- Companion Lean retains quantitative slack that the earlier H1 proof relaxed
-- to the common qualitative factor 3.
--
-- Across matched canonical coordinates u -> u + pi/t:
--
--   phase ratio gain:
--     (317/100) A_in < A_out
--
--   hyperbolic denominator growth:
--     H_out <= (161/59) H_in
--
-- Hence, throughout the canonical inner window and for t >= 18,
--
--   (2603/16100) R_t(u)
--      < R_t(u + pi/t) - R_t(u).
--
-- This is on the SAME matched affine-bump coordinate used by the integrated
-- H1 theorem.  It is therefore the correct quantitative route to an explicit
-- high-height Gamma margin; no endpoint-gap substitution is asserted here.
------------------------------------------------------------------------

record GammaMatchedQuantitativeGainReceipt : Set where
  constructor gamma-matched-quantitative-gain-receipt
  field
    repository : String
    branch : String
    path : String
    commit : String
    rootWiringCommit : String

open GammaMatchedQuantitativeGainReceipt public

currentGammaMatchedQuantitativeGainReceipt :
  GammaMatchedQuantitativeGainReceipt
currentGammaMatchedQuantitativeGainReceipt =
  gamma-matched-quantitative-gain-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannGammaMatchedQuantitativeGain.lean"
    "c588ba9e00f56138e5a6e72b31bbe2e46b7644af"
    "22a2e3bd0ac117a67de6b59cb405d3be56c2ccd5"

record GammaMatchedQuantitativeGainBoundary : Set where
  constructor gamma-matched-quantitative-gain-boundary
  field
    phaseGain317Over100SourceWritten : Bool
    hyperbolicGrowth161Over59SourceWritten : Bool
    matchedRelativeGain2603Over16100SourceWritten : Bool

    matchedInnerRatioAbsoluteLowerBoundPaid : Bool
    innerPoleMagnitudeUniformOneOverTLowerBoundPaid : Bool
    explicitUniformGammaMarginLowerBoundPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    rhDerivedHere : Bool

open GammaMatchedQuantitativeGainBoundary public

canonicalGammaMatchedQuantitativeGainBoundary :
  GammaMatchedQuantitativeGainBoundary
canonicalGammaMatchedQuantitativeGainBoundary =
  gamma-matched-quantitative-gain-boundary
    true
    true
    true

    false
    false
    false

    false
    false
    false
    false

matchedRelativeGammaGainNowSourceWritten :
  GammaMatchedQuantitativeGainBoundary.matchedRelativeGain2603Over16100SourceWritten
    canonicalGammaMatchedQuantitativeGainBoundary ≡ true
matchedRelativeGammaGainNowSourceWritten = refl

uniformGammaMarginStillNeedsAbsoluteScale :
  GammaMatchedQuantitativeGainBoundary.explicitUniformGammaMarginLowerBoundPaid
    canonicalGammaMatchedQuantitativeGainBoundary ≡ false
uniformGammaMarginStillNeedsAbsoluteScale = refl
