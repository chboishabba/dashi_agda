module DASHI.Analysis.RiemannG21TwoPointCovarianceShadowExact where

------------------------------------------------------------------------
-- Exact two-support covariance shadow of the G21 moment-ratio mechanism.
--
-- Let q0 and q0+dq be two ordered squared-radius scores.  Let (a0,a1) be
-- positive weights at the lower height and (b0,b1) weights at the higher
-- height.  Then the cross-multiplied weighted-mean difference is exactly
--
--   M2_b M0_a - M2_a M0_b
--     = dq * (b1*a0 - b0*a1).
--
-- Thus the moment ratio rises precisely when the higher-height weighting
-- relatively upweights the outer support point.  This is the finite algebraic
-- core of the covariance / monotone-likelihood-ratio argument suggested for
-- the actual cosh and sinh taper weights.
--
-- Literature neighbourhood only (not proof authority for the taper):
-- Z.-H. Yang and J.-F. Tian, "Monotonicity rules for the ratio of two Laplace
-- transforms with applications", JMAA 470 (2019), DOI
-- 10.1016/j.jmaa.2018.10.034; and the classical total-positivity framework of
-- Samuel Karlin.  The theorem below is proved directly by rational algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

m0 : ℚ → ℚ → ℚ
m0 w0 w1 = w0 + w1

m2 : ℚ → ℚ → ℚ → ℚ → ℚ
m2 q0 dq w0 w1 = q0 * w0 + (q0 + dq) * w1

twoPointMomentCrossProductDecomposition :
  (q0 dq a0 a1 b0 b1 : ℚ) →
  m2 q0 dq b0 b1 * m0 a0 a1
  ≡
  m2 q0 dq a0 a1 * m0 b0 b1
    + dq * (b1 * a0 - b0 * a1)
twoPointMomentCrossProductDecomposition q0 dq a0 a1 b0 b1 =
  solve (q0 ∷ dq ∷ a0 ∷ a1 ∷ b0 ∷ b1 ∷ [])

------------------------------------------------------------------------
-- Same algebra, named for the two G21 parity sectors.
------------------------------------------------------------------------

evenMomentCovarianceIdentity :
  (q0 dq coshA0 coshA1 coshP0 coshP1 : ℚ) →
  m2 q0 dq coshP0 coshP1 * m0 coshA0 coshA1
  ≡
  m2 q0 dq coshA0 coshA1 * m0 coshP0 coshP1
    + dq * (coshP1 * coshA0 - coshP0 * coshA1)
evenMomentCovarianceIdentity = twoPointMomentCrossProductDecomposition

oddMomentCovarianceIdentity :
  (q0 dq sinhA0 sinhA1 sinhP0 sinhP1 : ℚ) →
  m2 q0 dq sinhP0 sinhP1 * m0 sinhA0 sinhA1
  ≡
  m2 q0 dq sinhA0 sinhA1 * m0 sinhP0 sinhP1
    + dq * (sinhP1 * sinhA0 - sinhP0 * sinhA1)
oddMomentCovarianceIdentity = twoPointMomentCrossProductDecomposition

------------------------------------------------------------------------
-- Analytic bridge still required.
------------------------------------------------------------------------

record ActualTaperRelativeWeightMonotonicity : Set₁ where
  field
    Radius Height Weight : Set
    lowerRadius upperRadius : Radius
    offLineHeight poleHeight : Height

    evenWeight oddWeight : Height → Radius → Weight
    StrictPositive : Weight → Set
    RelativeOuterUpweight :
      Weight → Weight → Weight → Weight → Set

    evenWeightsPositive :
      StrictPositive (evenWeight offLineHeight lowerRadius)
      × StrictPositive (evenWeight offLineHeight upperRadius)
      × StrictPositive (evenWeight poleHeight lowerRadius)
      × StrictPositive (evenWeight poleHeight upperRadius)

    oddWeightsPositive :
      StrictPositive (oddWeight offLineHeight lowerRadius)
      × StrictPositive (oddWeight offLineHeight upperRadius)
      × StrictPositive (oddWeight poleHeight lowerRadius)
      × StrictPositive (oddWeight poleHeight upperRadius)

    evenHigherHeightRelativelyUpweightsOuterRadius :
      RelativeOuterUpweight
        (evenWeight offLineHeight lowerRadius)
        (evenWeight offLineHeight upperRadius)
        (evenWeight poleHeight lowerRadius)
        (evenWeight poleHeight upperRadius)

    oddHigherHeightRelativelyUpweightsOuterRadius :
      RelativeOuterUpweight
        (oddWeight offLineHeight lowerRadius)
        (oddWeight offLineHeight upperRadius)
        (oddWeight poleHeight lowerRadius)
        (oddWeight poleHeight upperRadius)

record CovarianceShadowBoundary : Set where
  field
    finiteTwoPointCovarianceIdentityDerived : Bool
    actualCoshRelativeWeightMonotonicityDerived : Bool
    actualSinhRelativeWeightMonotonicityDerived : Bool
    continuumMomentRatioTheoremDerived : Bool

covarianceShadowBoundary : CovarianceShadowBoundary
covarianceShadowBoundary = record
  { finiteTwoPointCovarianceIdentityDerived = true
  ; actualCoshRelativeWeightMonotonicityDerived = false
  ; actualSinhRelativeWeightMonotonicityDerived = false
  ; continuumMomentRatioTheoremDerived = false
  }
