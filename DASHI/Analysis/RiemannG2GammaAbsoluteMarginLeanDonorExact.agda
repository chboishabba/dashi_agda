module DASHI.Analysis.RiemannG2GammaAbsoluteMarginLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ABSOLUTE CANONICAL GAMMA MARGIN
--
-- Companion Lean now closes G_abs on the literal canonical Gamma cone.
--
-- It proves:
--
--   - quantitativeInnerPole(t)
--       >= pi * unitBumpMass0 / (4 t),
--
--   canonicalGammaRatioGap(t)
--       >= pi * (2636149 / 17899520000) * t,
--
-- and therefore, for every t >= 18,
--
--   Q_Gamma(t)
--      <=
--   - pi^2 * unitBumpMass0
--       * (2636149 / 35799040000).
--
-- The right-hand side is a fixed strictly negative constant independent of t.
-- This theorem lands on the SAME literal gammaVec/evenConeFunctional consumer
-- already used by RiemannQuantitativeGammaDeficit.
------------------------------------------------------------------------

record GammaAbsoluteMarginReceipt : Set where
  constructor gamma-absolute-margin-receipt
  field
    repository : String
    branch : String
    innerPoleScalePath : String
    innerRatioScalePath : String
    endpointGapScalePath : String
    literalConeMarginPath : String
    innerPoleScaleCommit : String
    innerRatioScaleCommit : String
    endpointGapScaleCommit : String
    literalConeMarginCommit : String
    rootWiringCommit : String

open GammaAbsoluteMarginReceipt public

currentGammaAbsoluteMarginReceipt : GammaAbsoluteMarginReceipt
currentGammaAbsoluteMarginReceipt =
  gamma-absolute-margin-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannGammaInnerPoleAbsoluteScale.lean"
    "Synthesis/RiemannGammaInnerRatioAbsoluteScale.lean"
    "Synthesis/RiemannGammaEndpointGapAbsoluteScale.lean"
    "Synthesis/RiemannGammaConeAbsoluteMargin.lean"
    "6b383f17521ab02dce24d562a68afec2fe180c82"
    "3d5ce8aa47018b00f95a757b9f1dfbf5fd334500"
    "0367c4e9d5b1e8d476b03b4b85bd6e6e5ec7ee7d"
    "b2e1893b93f30e2568cf2f084aef176e395e065d"
    "ad0e53ef84ef99c7aa99aec38528d32a5a98fbe5"

record GammaAbsoluteMarginBoundary : Set where
  constructor gamma-absolute-margin-boundary
  field
    innerPoleOneOverTLowerBoundSourceWritten : Bool
    innerRatioLinearLowerBoundSourceWritten : Bool
    canonicalEndpointGapLinearLowerBoundSourceWritten : Bool
    literalGammaConeUniformAbsoluteDeficitSourceWritten : Bool
    gammaAbsoluteScaleProducerPaid : Bool

    rvMSmoothMainCancellationPaid : Bool
    rvMCumulativeDiscrepancyPaid : Bool
    aggregateOffBelowGammaPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open GammaAbsoluteMarginBoundary public

canonicalGammaAbsoluteMarginBoundary : GammaAbsoluteMarginBoundary
canonicalGammaAbsoluteMarginBoundary =
  gamma-absolute-margin-boundary
    true
    true
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
    false

gammaAbsoluteScaleNowPaidAtSource :
  GammaAbsoluteMarginBoundary.gammaAbsoluteScaleProducerPaid
    canonicalGammaAbsoluteMarginBoundary ≡ true
gammaAbsoluteScaleNowPaidAtSource = refl

rvMMainStillOpen :
  GammaAbsoluteMarginBoundary.rvMSmoothMainCancellationPaid
    canonicalGammaAbsoluteMarginBoundary ≡ false
rvMMainStillOpen = refl

rvMRemainderStillOpen :
  GammaAbsoluteMarginBoundary.rvMCumulativeDiscrepancyPaid
    canonicalGammaAbsoluteMarginBoundary ≡ false
rvMRemainderStillOpen = refl
