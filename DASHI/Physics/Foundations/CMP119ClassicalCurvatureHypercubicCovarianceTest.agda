{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalCurvatureHypercubicCovarianceTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119ClassicalCurvatureHypercubicCovarianceExact as C

finiteCovarianceClosed : C.classicalCurvatureMetricVariationIsSignedB4Covariant ≡ true
finiteCovarianceClosed = refl

u1FiniteAlgebraClosed : C.remainingU1DebtIsRenormalizedSourceInheritanceNotFiniteTensorAlgebra ≡ true
u1FiniteAlgebraClosed = refl
