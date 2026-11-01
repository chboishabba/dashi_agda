{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceTest where

import DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact as P1

localizedPotentialCovariantRegression =
  P1.localizedPotentialCovariant

effectivePotentialCovariantRegression =
  P1.effectivePotentialCovariant

noDerivativeCovarianceNeededRegression =
  P1.potentialCovarianceNeedsNoDerivativeCovariancePremise
