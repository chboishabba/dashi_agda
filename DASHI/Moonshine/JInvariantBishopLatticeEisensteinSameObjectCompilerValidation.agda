module DASHI.Moonshine.JInvariantBishopLatticeEisensteinSameObjectCompilerValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.SetoidEisensteinTransformationExact as Setoid
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinSameObjectCompilerExact as P
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Legacy

setoidReindexingRegression :
  (M : Setoid.SetoidEisensteinAnalyticModel) →
  (weight : Nat) →
  (g : Legacy.SL2Z) →
  (tau : Setoid.Parameter M) →
  Setoid._≈ˢ_ M
    (Setoid.SetoidEisensteinSeries M weight
      (Setoid.actParameter M g tau))
    (Setoid._*ˢ_ M
      (Setoid.power M (Setoid.denominator M g tau) weight)
      (Setoid.SetoidEisensteinSeries M weight tau))
setoidReindexingRegression =
  Setoid.setoidEisensteinTransformation

bishopE4TransportRegression :
  (M : P.BishopLatticeEisensteinModel) →
  (qE4 qE6 : P.Parameter M → Complex.BishopComplex) →
  (same : P.BishopQSeriesLatticeSameObject M qE4 qE6) →
  (g : Legacy.SL2Z) →
  (tau : P.Parameter M) →
  Complex._≈C_
    (qE4 (P.actParameter M g tau))
    (Algebra._*C_
      (Algebra.powC (P.denominator M g tau) 4)
      (qE4 tau))
bishopE4TransportRegression =
  P.qSeriesE4Transformation

bishopE6TransportRegression :
  (M : P.BishopLatticeEisensteinModel) →
  (qE4 qE6 : P.Parameter M → Complex.BishopComplex) →
  (same : P.BishopQSeriesLatticeSameObject M qE4 qE6) →
  (g : Legacy.SL2Z) →
  (tau : P.Parameter M) →
  Complex._≈C_
    (qE6 (P.actParameter M g tau))
    (Algebra._*C_
      (Algebra.powC (P.denominator M g tau) 6)
      (qE6 tau))
bishopE6TransportRegression =
  P.qSeriesE6Transformation

setoidBridgePaidRegression :
  P.setoidNativeReindexingTheoremExact
    P.canonicalBishopLatticeEisensteinCrossPollinationFrontier
  ≡ true
setoidBridgePaidRegression = refl

sameObjectStillOpenRegression :
  P.qSeriesEqualsLatticeE4E6PaidHere
    P.canonicalBishopLatticeEisensteinCrossPollinationFrontier
  ≡ false
sameObjectStillOpenRegression = refl
