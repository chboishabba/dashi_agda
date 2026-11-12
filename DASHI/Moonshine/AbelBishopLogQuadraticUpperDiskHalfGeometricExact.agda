module DASHI.Moonshine.AbelBishopLogQuadraticUpperDiskHalfGeometricExact where

------------------------------------------------------------------------
-- BISHOP LOG QUADRATIC TAIL: SOURCE HALF-COEFFICIENT AND LIMIT JOIN.
--
-- On the ORIGINAL Bishop closed disk normSq(w) <= r², 0<=r<1,
-- the shifted log(1+w) source coefficient has magnitude <= 1/2.
-- Hence the actual shifted real AND imaginary term streams are
-- dominated by C*r^n, where C=(1/2)*r*r.
--
-- This constructs the original componentwise ABSOLUTE convergence
-- from the vendored Bishop comparison theorem, then proves that its
-- canonical shifted-series limit agrees with the already-established
-- original upper-disk log value minus w. No extra convergence axiom,
-- alternative logarithm or exact-radius assumption appears.
--
-- It does NOT yet prove norm(R₂) <= norm(w)^2 / (2*(1-r)):
-- the latter needs the true norm(w)^2 factor and finite-sum/limit
-- triangle comparison; do not promote a componentwise fixed-radius
-- envelope into a complex-norm quadratic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact as Geom
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Absolute
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log
import DASHI.Moonshine.AbelBishopLogQuadraticHalfCoefficientExact as Half
import DASHI.Moonshine.AbelBishopLogQuadraticUpperDiskSeriesLimitExact as Tail

halfQuadraticGeometricConstant : BishopReal.ℝ → BishopReal.ℝ
halfQuadraticGeometricConstant ratio =
  BishopReal._*_
    (BishopReal._*_ Half.bishopHalf ratio) ratio

halfQuadraticGeometricConstantNonnegative :
  ∀ {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopReal._≤_ BishopReal.0ℝ
    (halfQuadraticGeometricConstant ratio)
halfQuadraticGeometricConstantNonnegative {ratio} interval =
  BishopP.nonNegx⇒0≤x
    (BishopP.nonNegx,y⇒nonNegx*y
      (BishopP.nonNegx,y⇒nonNegx*y
        Half.bishopHalfNonnegative
        (Unit.ratioNonnegativeWitness interval))
      (Unit.ratioNonnegativeWitness interval))

halfQuadraticGeometricTermEquality :
  ∀ ratio (n : Nat) →
  BishopReal._≃_
    (BishopReal._*_
      Half.bishopHalf
      (BishopReal.pow ratio (suc (suc n))))
    (Geom.scaledGeometricTerm
      (halfQuadraticGeometricConstant ratio) ratio n)
halfQuadraticGeometricTermEquality ratio n =
  let open BishopP.ℝ-Solver in
  solve 3
    (λ half r p →
      half ⊗ ((p ⊗ r) ⊗ r)
      ⊜ ((half ⊗ r) ⊗ r) ⊗ p)
    BishopP.≃-refl
    Half.bishopHalf ratio (BishopReal.pow ratio n)

originalBishopLogQuadraticHalfGeometricBounds :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Absolute.OriginalBishopGeometricComponentBounds
    (λ n → Log.originalBishopLogOnePlusTerm w (suc n))
    (halfQuadraticGeometricConstant ratio)
    ratio
originalBishopLogQuadraticHalfGeometricBounds {w} {ratio} interval disk =
  record
    { Absolute.geometricInputs = record
        { Geom.constantNonnegative =
            halfQuadraticGeometricConstantNonnegative interval
        ; Geom.ratioInputs = interval
        }
    ; Absolute.realComponentBound = λ n →
        BishopP.≤-respʳ-≃
          (halfQuadraticGeometricTermEquality ratio n)
          (Half.originalBishopLogQuadraticRealTermUpper disk n)
    ; Absolute.imaginaryComponentBound = λ n →
        BishopP.≤-respʳ-≃
          (halfQuadraticGeometricTermEquality ratio n)
          (Half.originalBishopLogQuadraticImagTermUpper disk n)
    }

originalBishopLogQuadraticUpperDiskAbsoluteHalf :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (λ n → Log.originalBishopLogOnePlusTerm w (suc n))
originalBishopLogQuadraticUpperDiskAbsoluteHalf {w} {ratio}
  interval disk =
  Absolute.originalBishopKoenigsComponentAbsoluteSummability
    (λ n → Log.originalBishopLogOnePlusTerm w (suc n))
    (halfQuadraticGeometricConstant ratio)
    ratio
    (originalBishopLogQuadraticHalfGeometricBounds interval disk)

originalBishopLogQuadraticUpperDiskHalfCanonicalValue :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Complex.BishopComplex
originalBishopLogQuadraticUpperDiskHalfCanonicalValue {w}
  interval disk =
  Complex.complexSeriesLimit
    (λ n → Log.originalBishopLogOnePlusTerm w (suc n))
    (originalBishopLogQuadraticUpperDiskAbsoluteHalf interval disk)

-- SAME original terms: two independent completion routes yield
-- the SAME Bishop complex value by source series-limit uniqueness.
originalBishopLogQuadraticHalfLimitEqualsUpperDiskRemainder :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Complex._≈C_
    (originalBishopLogQuadraticUpperDiskHalfCanonicalValue interval disk)
    (Tail.originalBishopUpperDiskQuadraticRemainder interval disk)
originalBishopLogQuadraticHalfLimitEqualsUpperDiskRemainder
    {w} interval disk =
  let
    shiftedConvergence =
      Tail.originalBishopUpperDiskQuadraticTailConverges interval disk
  in
  Complex.complexSeriesLimitUnique
    (λ n → Log.originalBishopLogOnePlusTerm w (suc n))
    (originalBishopLogQuadraticUpperDiskAbsoluteHalf interval disk)
    (Tail.originalBishopUpperDiskQuadraticRemainder interval disk)
    (Complex.complex-series-converges-to
      (Completion.realConverges shiftedConvergence)
      (Completion.imaginaryConverges shiftedConvergence))
