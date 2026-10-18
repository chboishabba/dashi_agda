{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PreferredPresentCutSourceTest where

import DASHI.Physics.Foundations.CMP119CosmologyP1PreferredPresentCutSourceExact as P1

bc2Regression = P1.noIndependentBC2FirstVariationInPreferredPresentCut
linearityRegression = P1.round143LinearityCompiledFromPathDerivative
covarianceRegression = P1.signedR144CovarianceNowDownstreamCompilerOutput
