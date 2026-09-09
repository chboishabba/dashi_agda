module DASHI.Physics.Closure.NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact where

------------------------------------------------------------------------
-- ROUND529 / EXACT PERIODIC Z^3 FOURIER-MODE -> TERNARY-27 SIGN CHART
--
-- R528 correctly scheduled the periodic sign chart first.  The repo already
-- owns the literal periodic Fourier carrier `NSIntegerFourierLattice.FourierMode`
-- with integer coordinates, so this coordinate does not require new analysis.
-- We classify each integer coordinate by negative / zero / positive and prove
-- exact covariance under the three coordinate reflections.
--
-- This pays only the local sign-observation coordinate.  It does not identify
-- Z^3 counting measure with the R^3 continuum measure and does not transport
-- the literal R406 signed-cross functional between domains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; -_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNTorusEuclideanTernary27IntersectionRound526Exact as R526
import DASHI.Physics.Closure.NSTriadKNTorusEuclideanR406MeasureBridgeBoundaryRound528Exact as R528

integerSign529 : ℤ → SSP.SSPTrit
integerSign529 (+ zero) = SSP.sspZero
integerSign529 (+ (suc n)) = SSP.sspPosOne
integerSign529 (-[1+ n ]) = SSP.sspNegOne

integerSignNeg529 : (z : ℤ) → integerSign529 (- z) ≡
  (let open import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact in negateTrit (integerSign529 z))
integerSignNeg529 (+ zero) = refl
integerSignNeg529 (+ (suc n)) = refl
integerSignNeg529 (-[1+ n ]) = refl

observePeriodicMode529 : Z3.FourierMode → G.Ternary27Point
observePeriodicMode529 (Z3.mode x y z) =
  G.ternary27Point (integerSign529 x) (integerSign529 y) (integerSign529 z)

reflectPeriodicX529 : Z3.FourierMode → Z3.FourierMode
reflectPeriodicX529 (Z3.mode x y z) = Z3.mode (- x) y z

reflectPeriodicY529 : Z3.FourierMode → Z3.FourierMode
reflectPeriodicY529 (Z3.mode x y z) = Z3.mode x (- y) z

reflectPeriodicZ529 : Z3.FourierMode → Z3.FourierMode
reflectPeriodicZ529 (Z3.mode x y z) = Z3.mode x y (- z)

import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed

reflectPeriodicXObserved529 : (k : Z3.FourierMode) →
  observePeriodicMode529 (reflectPeriodicX529 k)
  ≡ Signed.flipX (observePeriodicMode529 k)
reflectPeriodicXObserved529 (Z3.mode (+ zero) y z) = refl
reflectPeriodicXObserved529 (Z3.mode (+ (suc n)) y z) = refl
reflectPeriodicXObserved529 (Z3.mode (-[1+ n ]) y z) = refl

reflectPeriodicYObserved529 : (k : Z3.FourierMode) →
  observePeriodicMode529 (reflectPeriodicY529 k)
  ≡ Signed.flipY (observePeriodicMode529 k)
reflectPeriodicYObserved529 (Z3.mode x (+ zero) z) = refl
reflectPeriodicYObserved529 (Z3.mode x (+ (suc n)) z) = refl
reflectPeriodicYObserved529 (Z3.mode x (-[1+ n ]) z) = refl

reflectPeriodicZObserved529 : (k : Z3.FourierMode) →
  observePeriodicMode529 (reflectPeriodicZ529 k)
  ≡ Signed.flipZ (observePeriodicMode529 k)
reflectPeriodicZObserved529 (Z3.mode x y (+ zero)) = refl
reflectPeriodicZObserved529 (Z3.mode x y (+ (suc n))) = refl
reflectPeriodicZObserved529 (Z3.mode x y (-[1+ n ])) = refl

periodicFrequencySignChart529 : R526.FrequencySignChart526 Z3.FourierMode
periodicFrequencySignChart529 =
  R526.frequency-sign-chart-526
    observePeriodicMode529
    reflectPeriodicX529
    reflectPeriodicY529
    reflectPeriodicZ529
    reflectPeriodicXObserved529
    reflectPeriodicYObserved529
    reflectPeriodicZObserved529

-- After paying the first R528 coordinate, exact Euclidean-frequency sign-chart
-- realization becomes the next representation demand.
afterPeriodicChart529 : R528.DomainBridgeState528
afterPeriodicChart529 =
  R528.domain-bridge-state-528
    R528.missingEuclideanSignChart528
    R528.instantiateEuclideanFrequencyChart528
    refl

round529PeriodicIntegerSignChartClosed : Bool
round529PeriodicIntegerSignChartClosed = true
round529PeriodicReflectionEquivarianceClosed : Bool
round529PeriodicReflectionEquivarianceClosed = true
round529EuclideanSignChartClosed : Bool
round529EuclideanSignChartClosed = false
round529MeasureBridgeClosed : Bool
round529MeasureBridgeClosed = false
round529ClayPromotion : Bool
round529ClayPromotion = false

round529PeriodicIntegerSignChartClosedIsTrue : round529PeriodicIntegerSignChartClosed ≡ true
round529PeriodicIntegerSignChartClosedIsTrue = refl
round529PeriodicReflectionEquivarianceClosedIsTrue : round529PeriodicReflectionEquivarianceClosed ≡ true
round529PeriodicReflectionEquivarianceClosedIsTrue = refl
round529EuclideanSignChartClosedIsFalse : round529EuclideanSignChartClosed ≡ false
round529EuclideanSignChartClosedIsFalse = refl
round529MeasureBridgeClosedIsFalse : round529MeasureBridgeClosed ≡ false
round529MeasureBridgeClosedIsFalse = refl
round529ClayPromotionIsFalse : round529ClayPromotion ≡ false
round529ClayPromotionIsFalse = refl
