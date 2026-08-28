module DASHI.Physics.Closure.NSTriadKNHHAntiParallelEndpointZeroRound164Exact where

------------------------------------------------------------------------
-- ROUND164 / EXACT ZERO OF THE HH HELICITY-SLOT KERNEL AT ANTI-PARALLELITY
--
-- Round145 factors the p/q normalized-curl slot kernel through Sigma=P+Q.
-- This closes the endpoint Sigma=0 exactly on the same C3 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145

bilinearDot3ZeroLeft :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.bilinearDot3 (C3.complex3Zero F) v ≡ C3.complexZero F
bilinearDot3ZeroLeft {F = F} (C3.complex3 vx vy vz)
  rewrite Field.complexMultiplyZeroLeft vx
        | Field.complexMultiplyZeroLeft vy
        | Field.complexMultiplyZeroLeft vz
        | Field.complexAddZeroLeft (C3.complexZero F)
        | Field.complexAddZeroLeft (C3.complexZero F) = refl

bilinearDot3ZeroRight :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.bilinearDot3 v (C3.complex3Zero F) ≡ C3.complexZero F
bilinearDot3ZeroRight {F = F} (C3.complex3 vx vy vz)
  rewrite Field.complexMultiplyZeroRight vx
        | Field.complexMultiplyZeroRight vy
        | Field.complexMultiplyZeroRight vz
        | Field.complexAddZeroLeft (C3.complexZero F)
        | Field.complexAddZeroLeft (C3.complexZero F) = refl

slotKernelZeroAtAntiParallelEndpoint :
  ∀ {r} {F : C3.RealField r}
    (P Q a b : C3.Complex3 F) →
  R145.TransverseHighPair P Q a b →
  R145.antiParallelDefect P Q ≡ C3.complex3Zero F →
  R145.slotKernel P Q a b ≡ C3.complex3Zero F
slotKernelZeroAtAntiParallelEndpoint {F = F} P Q a b T defectZero =
  trans
    (R145.slotKernelFactorsThroughAntiParallelDefect P Q a b T)
    endpoint
  where
  endpoint :
    C3.complex3Subtract
      (C3.complex3Add
        (C3.complex3Scale
          (C3.bilinearDot3 (R145.antiParallelDefect P Q) b) a)
        (C3.complex3Scale
          (C3.bilinearDot3 a (R145.antiParallelDefect P Q)) b))
      (C3.complex3Scale
        (C3.bilinearDot3 a b)
        (R145.antiParallelDefect P Q))
    ≡ C3.complex3Zero F
  endpoint rewrite defectZero
                   | bilinearDot3ZeroLeft b
                   | bilinearDot3ZeroRight a
                   | R106.complex3ScaleZeroScalar a
                   | R106.complex3ScaleZeroScalar b
                   | R106.complex3ScaleZeroVector (C3.bilinearDot3 a b)
                   | Field.complex3AddZeroRight (C3.complex3Zero F)
                   | R106.complex3SubtractSelf (C3.complex3Zero F) = refl

round164AntiParallelEndpointZeroNormalizationClosed : Bool
round164AntiParallelEndpointZeroNormalizationClosed = true

round164UsesAbsoluteValue : Bool
round164UsesAbsoluteValue = false

round164HHIntraShellSignedL2AggregationClosed : Bool
round164HHIntraShellSignedL2AggregationClosed = false

round164PackageAClosed : Bool
round164PackageAClosed = false

round164AntiParallelEndpointZeroNormalizationClosedIsTrue :
  round164AntiParallelEndpointZeroNormalizationClosed ≡ true
round164AntiParallelEndpointZeroNormalizationClosedIsTrue = refl

round164PackageAClosedIsFalse : round164PackageAClosed ≡ false
round164PackageAClosedIsFalse = refl
