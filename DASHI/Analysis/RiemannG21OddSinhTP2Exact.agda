module DASHI.Analysis.RiemannG21OddSinhTP2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.StrictKernelMomentRatioExact as TP2
import DASHI.Analysis.RiemannG21MathlibHyperbolicReceiptBoundary as Mathlib

------------------------------------------------------------------------
-- G21 odd-sector strict sign target.
--
-- For 0 < a < p and 0 < u < v, the desired atomic theorem is
--
--   sinh(p v) sinh(a u) > sinh(p u) sinh(a v).
--
-- Equivalently K(a,u)=sinh(a u) is strictly TP2 on the positive quadrant.
-- A standard route is G(x)=x coth x with
--
--   G'(x)=(sinh(2x)-2x)/(2 sinh(x)^2) > 0.
--
-- Mathlib already owns the atomic sinh inequalities used by that route, but
-- this Agda owner keeps cross-prover transport explicit.
------------------------------------------------------------------------

record SinhTP2AnalyticTarget : Set₁ where
  field
    Real : Set
    Positive : Real → Set
    StrictBelow StrictGreater : Real → Real → Set
    multiply : Real → Real → Real
    sinh : Real → Real

    a p u v : Real
    aPositive : Positive a
    pPositive : Positive p
    uPositive : Positive u
    vPositive : Positive v
    aBelowP : StrictBelow a p
    uBelowV : StrictBelow u v

    sinhTP2MinorPositive :
      StrictGreater
        (multiply (sinh (multiply p v)) (sinh (multiply a u)))
        (multiply (sinh (multiply p u)) (sinh (multiply a v)))

    targetReading : String

open SinhTP2AnalyticTarget public

record OddMomentStrictSignTarget : Set₁ where
  field
    Scalar : Set
    n1AtA n3AtA n1AtP n3AtP : Scalar
    multiply : Scalar → Scalar → Scalar
    StrictGreater : Scalar → Scalar → Set

    -- Positive-margin orientation:
    -- N1(a) N3(p) > N3(a) N1(p).
    positiveMargin :
      StrictGreater
        (multiply n1AtA n3AtP)
        (multiply n3AtA n1AtP)

    targetReading : String

open OddMomentStrictSignTarget public

------------------------------------------------------------------------
-- In the determinant orientation used earlier by G21,
--
--   N3(a) N1(p) - N1(a) N3(p) < 0.
--
-- The theorem name below is deliberately the final analytic target name.
------------------------------------------------------------------------

record G21OddOrientationBridge (target : OddMomentStrictSignTarget) : Set₁ where
  field
    StrictNegativeDifference : Scalar target → Scalar target → Set

    oddMomentDeterminantStrictNegative :
      StrictNegativeDifference
        (multiply target (n3AtA target) (n1AtP target))
        (multiply target (n1AtA target) (n3AtP target))

    bridgeReading : String

open G21OddOrientationBridge public

------------------------------------------------------------------------
-- Symmetrized continuum producer.  The intended identity is
--
-- N1(a)N3(p)-N3(a)N1(p)
--   = 1/2 ∫∫ u v phi(u)phi(v)(v^2-u^2)
--       [sinh(a u)sinh(p v)-sinh(p u)sinh(a v)] du dv.
--
-- On 0<u<v every nonzero factor is positive once sinh is strictly TP2.
------------------------------------------------------------------------

record OddMomentDoubleIntegralProducer : Set₁ where
  field
    Real Integral : Set
    StrictPositive : Real → Set
    StrictGreater : Integral → Integral → Set

    oddMomentMargin : Integral
    zeroIntegral : Integral

    symmetrizedDoubleIntegralIdentity : Set
    taperNonnegative : Set
    taperPositiveOnNontrivialInterval : Set
    orderedSupportFactorPositive : Set
    sinhKernelStrictTP2 : Set

    strictPositiveOddMomentMargin :
      StrictGreater oddMomentMargin zeroIntegral

    producerReading : String

------------------------------------------------------------------------
-- Mathlib theorem ownership is source-audited, not transported.
------------------------------------------------------------------------

mathlibAtomicReceiptBoundary : Mathlib.MathlibHyperbolicReceiptBoundary
mathlibAtomicReceiptBoundary = Mathlib.canonicalMathlibHyperbolicReceiptBoundary

genericStrictKernelBoundary : TP2.StrictKernelMomentRatioBoundary
genericStrictKernelBoundary = TP2.canonicalStrictKernelMomentRatioBoundary

record OddSinhTP2Boundary : Set where
  constructor oddSinhTP2Boundary
  field
    strictSinhTP2TargetExplicit : Bool
    strictSinhTP2TargetExplicitIsTrue : strictSinhTP2TargetExplicit ≡ true
    strictOddMomentSignTargetExplicit : Bool
    strictOddMomentSignTargetExplicitIsTrue : strictOddMomentSignTargetExplicit ≡ true
    exactNegativeOrientationTargetNamed : Bool
    exactNegativeOrientationTargetNamedIsTrue : exactNegativeOrientationTargetNamed ≡ true
    genericTP2MomentOwnerAvailable : Bool
    genericTP2MomentOwnerAvailableIsTrue : genericTP2MomentOwnerAvailable ≡ true
    mathlibAtomicSinhFactsLocated : Bool
    mathlibAtomicSinhFactsLocatedIsTrue : mathlibAtomicSinhFactsLocated ≡ true
    sinhTP2DerivedInAgda : Bool
    sinhTP2DerivedInAgdaIsFalse : sinhTP2DerivedInAgda ≡ false
    continuumOddMomentStrictSignDerived : Bool
    continuumOddMomentStrictSignDerivedIsFalse : continuumOddMomentStrictSignDerived ≡ false

canonicalOddSinhTP2Boundary : OddSinhTP2Boundary
canonicalOddSinhTP2Boundary =
  oddSinhTP2Boundary
    true refl true refl true refl true refl true refl false refl false refl
