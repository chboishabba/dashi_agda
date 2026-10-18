module DASHI.Analysis.BishopComplexSeriesConvergenceValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as P

zeroTerms : Nat -> P.BishopComplex
zeroTerms _ = P.complex BishopReal.0ℝ BishopReal.0ℝ

componentProjectionRe :
  (n : Nat) -> P.realTerms zeroTerms n BishopReal.≃ BishopReal.0ℝ
componentProjectionRe n = BishopProperties.≃-refl

componentProjectionIm :
  (n : Nat) -> P.imagTerms zeroTerms n BishopReal.≃ BishopReal.0ℝ
componentProjectionIm n = BishopProperties.≃-refl

complexSetoidReflexive :
  (z : P.BishopComplex) -> P._≈C_ z z
complexSetoidReflexive = P.≈C-refl
