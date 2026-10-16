module DASHI.Analysis.CollatzSyracuseCoefficientStoppingBoundaryValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseCoefficientStoppingBoundaryExact as CST

orderingPaid :
  CST.CoefficientStoppingBoundary.coefficientHorizonAtMostDescentHorizonPaid
    CST.canonicalCoefficientStoppingBoundary
  ≡ 1
orderingPaid = refl

conditionalEqualityPaid :
  CST.CoefficientStoppingBoundary.correctionFitAtCoefficientHorizonImpliesEqualityPaid
    CST.canonicalCoefficientStoppingBoundary
  ≡ 1
conditionalEqualityPaid = refl

universalCSTOpen :
  CST.CoefficientStoppingBoundary.universalCoefficientStoppingEqualityPaid
    CST.canonicalCoefficientStoppingBoundary
  ≡ 0
universalCSTOpen = refl

noLiteraturePromotion :
  CST.CoefficientStoppingBoundary.externalCSTLiteratureCreatesAgdaProof
    CST.canonicalCoefficientStoppingBoundary
  ≡ 0
noLiteraturePromotion = refl
