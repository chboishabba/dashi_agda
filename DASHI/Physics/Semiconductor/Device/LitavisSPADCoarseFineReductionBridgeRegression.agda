module DASHI.Physics.Semiconductor.Device.LitavisSPADCoarseFineReductionBridgeRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Semiconductor.Device.LitavisSPADCoarseFineReductionBridgeExact as Bridge

record LitavisCoarseFineReductionBridgeRegression : Set₁ where
  constructor litavis-coarse-fine-reduction-bridge-regression
  field
    coarsePlusResidualReopensFineState :
      Bridge.CoarseFineReopeningReceipt
    coarseDynamicsCloseForDeclaredModeAction :
      Bridge.DeclaredModeDynamicsReceipt
    histogramConsumerFactorsThroughCoarseSurface :
      Bridge.HistogramConsumerReceipt
    exactTimestampConsumerRefutesCoarseOnlyReduction :
      Bridge.ExactTimestampFailureReceipt
    retainedResidualIsNotRequiredToBeDiscarded :
      Bridge.CoarseFineBridgeBoundary

canonicalLitavisCoarseFineReductionBridgeRegression :
  LitavisCoarseFineReductionBridgeRegression
canonicalLitavisCoarseFineReductionBridgeRegression =
  litavis-coarse-fine-reduction-bridge-regression
    Bridge.canonicalCoarseFineReopeningReceipt
    Bridge.canonicalDeclaredModeDynamicsReceipt
    Bridge.canonicalHistogramConsumerReceipt
    Bridge.canonicalExactTimestampFailureReceipt
    Bridge.canonicalCoarseFineBridgeBoundary
