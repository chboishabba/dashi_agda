module DASHI.Moonshine.QuadraticSignedApproximationValidation where

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.QuadraticIrrationalSignedApproximationFibreExact as Quad
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.GoldenRatioFibonacci369SheetVoxelBridgeExact as Fib369

open import Agda.Builtin.Equality using (_≡_; refl)

checkDecimalDirection :
  Quad.sqrtThreeHalfTrit Quad.decimal866025Defect
  ≡ Triadic.negativeTrit
checkDecimalDirection = refl

checkPhiNormOne :
  Quad.goldenRatioTrit Quad.phi34Over21
  ≡ Triadic.positiveTrit
checkPhiNormOne = refl

checkFibComparisonNegative :
  Fib369.fibComparison Triadic.negativeTrit
  ≡ (Triadic.negativeTrit , Triadic.positiveTrit)
checkFibComparisonNegative = refl

checkFibComparisonCentre :
  Triadic.quotientNine (Fib369.fibComparison Triadic.zeroTrit)
  ≡ Triadic.zeroOrbit
checkFibComparisonCentre = refl

checkFibVoxelRestoresAfterTwoSteps :
  Fib369.fibVoxel (Fib369.fibTritStep (Fib369.fibTritStep Triadic.positiveTrit))
  ≡ Fib369.fibVoxel Triadic.positiveTrit
checkFibVoxelRestoresAfterTwoSteps = refl
