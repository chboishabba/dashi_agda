module DASHI.Geometry.NonconstantWarpedLorentzianModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Base369 using (TriTruth)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Geometry.CausalRelationalMetricSelector as Selector
import DASHI.Geometry.FlatLorentzianModel as Flat

------------------------------------------------------------------------
-- Finite nonconstant FLRW-like local metric.
--
-- Three ordered slices carry spatial log-scale depths 0, 1, 2.  Metric signs
-- are selected by the typed causal/relational frame.  First differences,
-- normalized Christoffel coefficients, and curvature are computed from the
-- changing metric profile.
--
-- This is an exact finite symbolic model, not a smooth continuum FLRW theorem.


data TimeSlice : Set where
  pastSlice : TimeSlice
  presentSlice : TimeSlice
  futureSlice : TimeSlice


data TimeEdge : Set where
  pastToPresent : TimeEdge
  presentToFuture : TimeEdge


edgeStart : TimeEdge → TimeSlice
edgeStart pastToPresent = pastSlice
edgeStart presentToFuture = presentSlice


edgeEnd : TimeEdge → TimeSlice
edgeEnd pastToPresent = presentSlice
edgeEnd presentToFuture = futureSlice


spatialLogScale : TimeSlice → Nat
spatialLogScale pastSlice = zero
spatialLogScale presentSlice = suc zero
spatialLogScale futureSlice = suc (suc zero)


metricLogScale : TimeSlice → Flat.Axis4 → Flat.Axis4 → Nat
metricLogScale slice Flat.timeAxis Flat.timeAxis = zero
metricLogScale slice Flat.timeAxis Flat.xAxis = zero
metricLogScale slice Flat.timeAxis Flat.yAxis = zero
metricLogScale slice Flat.timeAxis Flat.zAxis = zero
metricLogScale slice Flat.xAxis Flat.timeAxis = zero
metricLogScale slice Flat.xAxis Flat.xAxis = spatialLogScale slice
metricLogScale slice Flat.xAxis Flat.yAxis = zero
metricLogScale slice Flat.xAxis Flat.zAxis = zero
metricLogScale slice Flat.yAxis Flat.timeAxis = zero
metricLogScale slice Flat.yAxis Flat.xAxis = zero
metricLogScale slice Flat.yAxis Flat.yAxis = spatialLogScale slice
metricLogScale slice Flat.yAxis Flat.zAxis = zero
metricLogScale slice Flat.zAxis Flat.timeAxis = zero
metricLogScale slice Flat.zAxis Flat.xAxis = zero
metricLogScale slice Flat.zAxis Flat.yAxis = zero
metricLogScale slice Flat.zAxis Flat.zAxis = spatialLogScale slice


record LocalMetricEntry : Set where
  constructor mkLocalMetricEntry
  field
    metricSign : TriTruth
    logarithmicScaleDepth : Nat

open LocalMetricEntry public


localMetricEntry : TimeSlice → Flat.Axis4 → Flat.Axis4 → LocalMetricEntry
localMetricEntry slice a b =
  mkLocalMetricEntry
    (Selector.selectedMetricEntry Selector.canonicalMetricSelectionData a b)
    (metricLogScale slice a b)


data DepthChange : Nat → Nat → Set where
  zeroToOne : DepthChange zero (suc zero)
  oneToTwo : DepthChange (suc zero) (suc (suc zero))


pastPresentMetricChanges :
  DepthChange
    (logarithmicScaleDepth
      (localMetricEntry pastSlice Flat.xAxis Flat.xAxis))
    (logarithmicScaleDepth
      (localMetricEntry presentSlice Flat.xAxis Flat.xAxis))
pastPresentMetricChanges = zeroToOne


presentFutureMetricChanges :
  DepthChange
    (logarithmicScaleDepth
      (localMetricEntry presentSlice Flat.zAxis Flat.zAxis))
    (logarithmicScaleDepth
      (localMetricEntry futureSlice Flat.zAxis Flat.zAxis))
presentFutureMetricChanges = oneToTwo

------------------------------------------------------------------------
-- Metric-derived first differences.


data UnitCoefficient : Set where
  negativeUnit : UnitCoefficient
  zeroUnit : UnitCoefficient
  positiveUnit : UnitCoefficient


negateUnit : UnitCoefficient → UnitCoefficient
negateUnit negativeUnit = positiveUnit
negateUnit zeroUnit = zeroUnit
negateUnit positiveUnit = negativeUnit


compareDepth : Nat → Nat → UnitCoefficient
compareDepth zero zero = zeroUnit
compareDepth zero (suc n) = positiveUnit
compareDepth (suc n) zero = negativeUnit
compareDepth (suc m) (suc n) = compareDepth m n


hubbleCoefficient : TimeEdge → UnitCoefficient
hubbleCoefficient edge =
  compareDepth
    (spatialLogScale (edgeStart edge))
    (spatialLogScale (edgeEnd edge))


pastHubblePositive : hubbleCoefficient pastToPresent ≡ positiveUnit
pastHubblePositive = refl


futureHubblePositive : hubbleCoefficient presentToFuture ≡ positiveUnit
futureHubblePositive = refl


unitDifference : UnitCoefficient → UnitCoefficient → UnitCoefficient
unitDifference negativeUnit negativeUnit = zeroUnit
unitDifference negativeUnit zeroUnit = positiveUnit
unitDifference negativeUnit positiveUnit = positiveUnit
unitDifference zeroUnit negativeUnit = negativeUnit
unitDifference zeroUnit zeroUnit = zeroUnit
unitDifference zeroUnit positiveUnit = positiveUnit
unitDifference positiveUnit negativeUnit = negativeUnit
unitDifference positiveUnit zeroUnit = negativeUnit
unitDifference positiveUnit positiveUnit = zeroUnit


hubbleDerivative : UnitCoefficient
hubbleDerivative =
  unitDifference
    (hubbleCoefficient pastToPresent)
    (hubbleCoefficient presentToFuture)


constantHubbleReceipt : hubbleDerivative ≡ zeroUnit
constantHubbleReceipt = refl

------------------------------------------------------------------------
-- Normalized Levi-Civita coefficient table computed from metric gradients.


data LowerPairClass : Set where
  timeXPair : LowerPairClass
  timeYPair : LowerPairClass
  timeZPair : LowerPairClass
  xxPair : LowerPairClass
  yyPair : LowerPairClass
  zzPair : LowerPairClass
  otherPair : LowerPairClass


lowerPairClass : Flat.Axis4 → Flat.Axis4 → LowerPairClass
lowerPairClass Flat.timeAxis Flat.timeAxis = otherPair
lowerPairClass Flat.timeAxis Flat.xAxis = timeXPair
lowerPairClass Flat.timeAxis Flat.yAxis = timeYPair
lowerPairClass Flat.timeAxis Flat.zAxis = timeZPair
lowerPairClass Flat.xAxis Flat.timeAxis = timeXPair
lowerPairClass Flat.xAxis Flat.xAxis = xxPair
lowerPairClass Flat.xAxis Flat.yAxis = otherPair
lowerPairClass Flat.xAxis Flat.zAxis = otherPair
lowerPairClass Flat.yAxis Flat.timeAxis = timeYPair
lowerPairClass Flat.yAxis Flat.xAxis = otherPair
lowerPairClass Flat.yAxis Flat.yAxis = yyPair
lowerPairClass Flat.yAxis Flat.zAxis = otherPair
lowerPairClass Flat.zAxis Flat.timeAxis = timeZPair
lowerPairClass Flat.zAxis Flat.xAxis = otherPair
lowerPairClass Flat.zAxis Flat.yAxis = otherPair
lowerPairClass Flat.zAxis Flat.zAxis = zzPair


lowerPairSymmetric :
  (a b : Flat.Axis4) → lowerPairClass a b ≡ lowerPairClass b a
lowerPairSymmetric Flat.timeAxis Flat.timeAxis = refl
lowerPairSymmetric Flat.timeAxis Flat.xAxis = refl
lowerPairSymmetric Flat.timeAxis Flat.yAxis = refl
lowerPairSymmetric Flat.timeAxis Flat.zAxis = refl
lowerPairSymmetric Flat.xAxis Flat.timeAxis = refl
lowerPairSymmetric Flat.xAxis Flat.xAxis = refl
lowerPairSymmetric Flat.xAxis Flat.yAxis = refl
lowerPairSymmetric Flat.xAxis Flat.zAxis = refl
lowerPairSymmetric Flat.yAxis Flat.timeAxis = refl
lowerPairSymmetric Flat.yAxis Flat.xAxis = refl
lowerPairSymmetric Flat.yAxis Flat.yAxis = refl
lowerPairSymmetric Flat.yAxis Flat.zAxis = refl
lowerPairSymmetric Flat.zAxis Flat.timeAxis = refl
lowerPairSymmetric Flat.zAxis Flat.xAxis = refl
lowerPairSymmetric Flat.zAxis Flat.yAxis = refl
lowerPairSymmetric Flat.zAxis Flat.zAxis = refl


gammaFromPair : TimeEdge → Flat.Axis4 → LowerPairClass → UnitCoefficient
gammaFromPair edge Flat.timeAxis xxPair = hubbleCoefficient edge
gammaFromPair edge Flat.timeAxis yyPair = hubbleCoefficient edge
gammaFromPair edge Flat.timeAxis zzPair = hubbleCoefficient edge
gammaFromPair edge Flat.xAxis timeXPair = hubbleCoefficient edge
gammaFromPair edge Flat.yAxis timeYPair = hubbleCoefficient edge
gammaFromPair edge Flat.zAxis timeZPair = hubbleCoefficient edge
gammaFromPair edge upper pair = zeroUnit


leviCivitaCoefficient :
  TimeEdge → Flat.Axis4 → Flat.Axis4 → Flat.Axis4 → UnitCoefficient
leviCivitaCoefficient edge upper lower₁ lower₂ =
  gammaFromPair edge upper (lowerPairClass lower₁ lower₂)


leviCivitaLowerSymmetric :
  (edge : TimeEdge) →
  (upper lower₁ lower₂ : Flat.Axis4) →
  leviCivitaCoefficient edge upper lower₁ lower₂
  ≡ leviCivitaCoefficient edge upper lower₂ lower₁
leviCivitaLowerSymmetric edge upper lower₁ lower₂ =
  cong (gammaFromPair edge upper) (lowerPairSymmetric lower₁ lower₂)


computedGammaTimeXX :
  leviCivitaCoefficient pastToPresent Flat.timeAxis Flat.xAxis Flat.xAxis
  ≡ hubbleCoefficient pastToPresent
computedGammaTimeXX = refl


computedGammaXTimeX :
  leviCivitaCoefficient presentToFuture Flat.xAxis Flat.timeAxis Flat.xAxis
  ≡ hubbleCoefficient presentToFuture
computedGammaXTimeX = refl


computedConnectionNonzero :
  leviCivitaCoefficient pastToPresent Flat.timeAxis Flat.xAxis Flat.xAxis
  ≡ positiveUnit
computedConnectionNonzero = refl


record ComputedWarpedLeviCivitaReceipt : Set where
  constructor mkComputedWarpedLeviCivitaReceipt
  field
    coefficientSourcePast :
      leviCivitaCoefficient pastToPresent Flat.timeAxis Flat.xAxis Flat.xAxis
      ≡ hubbleCoefficient pastToPresent
    coefficientSourceFuture :
      leviCivitaCoefficient presentToFuture Flat.xAxis Flat.timeAxis Flat.xAxis
      ≡ hubbleCoefficient presentToFuture
    torsionFreeLowerIndices :
      (edge : TimeEdge) →
      (upper lower₁ lower₂ : Flat.Axis4) →
      leviCivitaCoefficient edge upper lower₁ lower₂
      ≡ leviCivitaCoefficient edge upper lower₂ lower₁
    nonzeroCoefficient :
      leviCivitaCoefficient pastToPresent Flat.timeAxis Flat.xAxis Flat.xAxis
      ≡ positiveUnit
    receiptScope : String

open ComputedWarpedLeviCivitaReceipt public


computedWarpedLeviCivitaReceipt : ComputedWarpedLeviCivitaReceipt
computedWarpedLeviCivitaReceipt =
  mkComputedWarpedLeviCivitaReceipt
    computedGammaTimeXX
    computedGammaXTimeX
    leviCivitaLowerSymmetric
    computedConnectionNonzero
    "normalized finite FLRW-like coefficients computed from spatial log-scale differences"

------------------------------------------------------------------------
-- Curvature computed from H-dot and H squared.


data CurvatureCoefficient : Set where
  zeroCurvature : CurvatureCoefficient
  positiveCurvature : CurvatureCoefficient


squareUnit : UnitCoefficient → CurvatureCoefficient
squareUnit negativeUnit = positiveCurvature
squareUnit zeroUnit = zeroCurvature
squareUnit positiveUnit = positiveCurvature


warpedSectionalCurvature : CurvatureCoefficient
warpedSectionalCurvature = squareUnit (hubbleCoefficient pastToPresent)


computedPositiveCurvature : warpedSectionalCurvature ≡ positiveCurvature
computedPositiveCurvature = refl


record ComputedWarpedCurvatureReceipt : Set where
  constructor mkComputedWarpedCurvatureReceipt
  field
    firstGradient : hubbleCoefficient pastToPresent ≡ positiveUnit
    secondGradient : hubbleCoefficient presentToFuture ≡ positiveUnit
    derivativeVanishes : hubbleDerivative ≡ zeroUnit
    curvatureFromGradientSquare :
      warpedSectionalCurvature
      ≡ squareUnit (hubbleCoefficient pastToPresent)
    curvatureNonzero : warpedSectionalCurvature ≡ positiveCurvature
    curvatureScope : String

open ComputedWarpedCurvatureReceipt public


computedWarpedCurvatureReceipt : ComputedWarpedCurvatureReceipt
computedWarpedCurvatureReceipt =
  mkComputedWarpedCurvatureReceipt
    pastHubblePositive
    futureHubblePositive
    constantHubbleReceipt
    refl
    computedPositiveCurvature
    "positive finite warped curvature computed from a nonzero constant log-scale gradient"
