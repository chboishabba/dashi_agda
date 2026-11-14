module DASHI.Moonshine.AbelBishopLogOnePlusUpperDiskConvergenceExact where

------------------------------------------------------------------------
-- ACTUAL BISHOP LOG(1+u) SERIES ON A CLOSED UPPER-BOUND DISK.
--
-- Previous source accepted normSq(u) ~= ratio^2; the selected
-- principal-log neighbourhood provides normSq(u) <= ratio^2.
-- Reuse the new original BishopComplexNormSquareUpperPowerEnvelope
-- and the existing factorial log coefficients and Bishop geometric
-- comparison backend to prove absolute source convergence.
--
-- No radius-equality oracle and no inferred principal-branch inverse.
-- In particular, this constructs a log-series germ from literal
-- terms on arbitrary (<=) disk points, not a modular or Kneser proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Geom
import DASHI.Moonshine.AbelBishopGeometricPowerSeriesExact as Powers
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log
import DASHI.Moonshine.AbelBishopLogOnePlusCoefficientDominationExact as Coeff
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine
import DASHI.Moonshine.AbelBishopSelectedLogNormalizedDiskUpperExact as Normalized
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal

originalBishopLogUpperDiskComponentBounds :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Geom.OriginalBishopGeometricComponentBounds
    (Log.originalBishopLogOnePlusTerm w)
    ratio ratio
originalBishopLogUpperDiskComponentBounds {w} {ratio} interval disk =
  let
    envelope : Norm.BishopQPowerComponentEnvelope w ratio
    envelope = Upper.upperBoundBuildsOriginalPowerEnvelope disk

    realBound : ∀ n →
      BishopReal._≤_
        (BishopReal.∣ Complex.re
          (Log.originalBishopLogOnePlusTerm w n) ∣)
        (BishopReal._*_
          ratio (BishopReal.pow ratio n))
    realBound n =
      BishopP.≤-trans
        (Coeff.originalBishopScalarMagnitudeAtMostOne
          (Log.logCoefficient n)
          (Complex.re (Powers.originalBishopGeometricPowerTerm w n))
          (Coeff.originalBishopLogCoefficientMagnitudeAtMostOne n))
        (BishopP.≤-respʳ-≃
          (BishopP.*-comm (BishopReal.pow ratio n) ratio)
          (Norm.realPowerBound envelope n))

    imagBound : ∀ n →
      BishopReal._≤_
        (BishopReal.∣ Complex.im
          (Log.originalBishopLogOnePlusTerm w n) ∣)
        (BishopReal._*_
          ratio (BishopReal.pow ratio n))
    imagBound n =
      BishopP.≤-trans
        (Coeff.originalBishopScalarMagnitudeAtMostOne
          (Log.logCoefficient n)
          (Complex.im (Powers.originalBishopGeometricPowerTerm w n))
          (Coeff.originalBishopLogCoefficientMagnitudeAtMostOne n))
        (BishopP.≤-respʳ-≃
          (BishopP.*-comm (BishopReal.pow ratio n) ratio)
          (Norm.imagPowerBound envelope n))
  in
  record
    { Geom.geometricInputs =
        Powers.originalBishopPowerGeometricInputs interval
    ; Geom.realComponentBound = realBound
    ; Geom.imaginaryComponentBound = imagBound
    }

originalBishopLogUpperDiskAbsoluteConvergence :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  Upper.BishopComplexNormSquareUpperRadius w ratio →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (Log.originalBishopLogOnePlusTerm w)
originalBishopLogUpperDiskAbsoluteConvergence {w} {ratio} interval disk =
  Geom.originalBishopKoenigsComponentAbsoluteSummability
    (Log.originalBishopLogOnePlusTerm w)
    ratio ratio
    (originalBishopLogUpperDiskComponentBounds interval disk)

originalBishopLogUpperDiskCanonicalValue :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  Upper.BishopComplexNormSquareUpperRadius w ratio →
  Complex.BishopComplex
originalBishopLogUpperDiskCanonicalValue {w} interval disk =
  Log.originalBishopLogOnePlusSeriesValue w
    (originalBishopLogUpperDiskAbsoluteConvergence interval disk)

originalBishopLogUpperDiskCanonicalConverges :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Complex.ComplexSeriesConvergesTo
    (Log.originalBishopLogOnePlusTerm w)
    (originalBishopLogUpperDiskCanonicalValue interval disk)
originalBishopLogUpperDiskCanonicalConverges {w} interval disk =
  Log.originalBishopLogOnePlusSeriesConverges w
    (originalBishopLogUpperDiskAbsoluteConvergence interval disk)

originalBishopSelectedAffineUpperDiskLogGerm :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t ratio →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  BishopReal._≤_
    (Norm.normSqC t)
    (BishopReal._*_
      (Norm.square ratio)
      (Norm.normSqC p)) →
  Complex.BishopComplex
originalBishopSelectedAffineUpperDiskLogGerm p nz t ratio interval bound =
  Algebra._+C_ p
    (originalBishopLogUpperDiskCanonicalValue
      interval
      (record
        { Upper.radiusNonnegative =
            BishopP.0≤x⇒nonNegx (Unit.ratioNonnegative interval)
        ; Upper.normSqBelowRadiusSquare =
            Normalized.originalBishopNormalizedDisplacementUpperBound
              p nz t ratio bound
        }))
