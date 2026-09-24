module DASHI.Analysis.BishopComplexAlgebraValidation where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as P

powCongruenceRegression :
  ∀ {left right : Complex.BishopComplex} →
  Complex._≈C_ left right →
  ∀ n →
  Complex._≈C_ (P.powC left n) (P.powC right n)
powCongruenceRegression = P.powCCongruent

scaleCongruenceRegression :
  ∀ {left right : Complex.BishopComplex} →
  Complex._≈C_ left right →
  ∀ n →
  Complex._≈C_ (P.scaleNatC n left) (P.scaleNatC n right)
scaleCongruenceRegression = P.scaleNatCCongruent

scalarCongruenceRegression :
  ∀ {left right : Complex.BishopComplex} →
  Complex._≈C_ left right →
  ∀ scalar →
  Complex._≈C_ (P.scaleC scalar left) (P.scaleC scalar right)
scalarCongruenceRegression = P.scaleCCongruent
