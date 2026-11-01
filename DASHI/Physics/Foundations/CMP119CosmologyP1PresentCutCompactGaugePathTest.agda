{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutCompactGaugePathTest where

import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutCompactGaugePathExact as P1

compilerRegression = P1.presentCutSourcePathCovarianceIsCompiled
remainingRegression = P1.remainingQ1LeafIsBC2DerivativeSemanticsPlusLiteralGroupGeometry
