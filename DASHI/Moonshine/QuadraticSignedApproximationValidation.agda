module DASHI.Moonshine.QuadraticSignedApproximationValidation where

import DASHI.Moonshine.QuadraticIrrationalSignedApproximationFibreExact as Quad
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)

checkDecimalDirection :
  Quad.sqrtThreeHalfTrit Quad.decimal866025Defect
  ≡
  DASHI.Biology.TriadicKernelLiftQuotientExact.negativeTrit
checkDecimalDirection = refl

checkPhiNormOne :
  Quad.goldenRatioTrit Quad.phi34Over21
  ≡
  DASHI.Biology.TriadicKernelLiftQuotientExact.positiveTrit
checkPhiNormOne = refl
