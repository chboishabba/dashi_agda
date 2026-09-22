module DASHI.Moonshine.EisensteinUpperHalfPlaneQDiskExact where

------------------------------------------------------------------------
-- UPPER HALF-PLANE -> |q| < 1 REDUCTION
--
-- q(tau) = exp(2*pi*i*tau), tau = x + i y.
--
-- The algebraic target is
--
--   2*pi*i*tau = -2*pi*y + i(2*pi*x),
--
-- hence
--
--   |q(tau)| = exp(-2*pi*y).
--
-- For y>0 and pi>0, the exponent is negative, so strict monotonicity of exp
-- gives |q| < exp(0) = 1.
--
-- The generic ConstructedComplexPackage intentionally does not retain every
-- ordered-ring and polar law needed for this argument.  This owner isolates
-- exactly those laws and derives the disk conclusion without adding them to
-- the global spine.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q

private
  RealCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  RealCarrier C = Real.Real (Real.real (Complex.realPackage C))

  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C = Complex.ComplexPair (Real.real (Complex.realPackage C))

------------------------------------------------------------------------
-- 1. Upper-half-plane predicate.
------------------------------------------------------------------------

record UpperHalfPlanePoint
    (C : Complex.ConstructedComplexPackage)
    (tau : ComplexCarrier C) : Set where
  field
    imaginaryPositive :
      Real._<_ (Real.real (Complex.realPackage C))
        (Real.zero (Real.real (Complex.realPackage C)))
        (Complex.im tau)

open UpperHalfPlanePoint public

------------------------------------------------------------------------
-- 2. Exact Cartesian exponent and modulus laws required by q.
------------------------------------------------------------------------

record QDiskAnalyticLaws
    (C : Complex.ConstructedComplexPackage) : Set₁ where

  private
    R = Real.real (Complex.realPackage C)
    E = Real.exponential (Complex.realPackage C)
    CE = Complex.complexExponential C

  field
    twoPi : RealCarrier C

    twoPiDefinition :
      twoPi
      ≡ Real._+_ R (Complex.pi CE) (Complex.pi CE)

    twoPiPositive :
      Real._<_ R (Real.zero R) twoPi

    positiveProduct :
      ∀ {x y} →
      Real._<_ R (Real.zero R) x →
      Real._<_ R (Real.zero R) y →
      Real._<_ R (Real.zero R) (Real._*_ R x y)

    negativeOfPositiveIsNegative :
      ∀ {x} →
      Real._<_ R (Real.zero R) x →
      Real._<_ R (Real.neg R x) (Real.zero R)

    qExponentCartesian :
      (tau : ComplexCarrier C) →
      let
        exponent =
          Complex._*C_
            (Q.scaleNatC 2
              (Complex._*C_
                Complex.imaginaryUnit
                (Complex.complex (Complex.pi CE) (Real.zero R))))
            tau
      in
      exponent
      ≡ Complex.complex
          (Real.neg R (Real._*_ R twoPi (Complex.im tau)))
          (Real._*_ R twoPi (Complex.re tau))

    modulus : ComplexCarrier C → RealCarrier C

    modulusOfComplexExponential :
      (x y : RealCarrier C) →
      modulus
        (Complex.expC CE (Complex.complex x y))
      ≡ Real.exp E x

open QDiskAnalyticLaws public

------------------------------------------------------------------------
-- 3. The exponent has strictly negative real part on H.
------------------------------------------------------------------------

qDecayRatePositive :
  ∀ {C tau} →
  (laws : QDiskAnalyticLaws C) →
  UpperHalfPlanePoint C tau →
  Real._<_
    (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C)))
    (Real._*_
      (Real.real (Complex.realPackage C))
      (twoPi laws)
      (Complex.im tau))
qDecayRatePositive laws upper =
  positiveProduct laws
    (twoPiPositive laws)
    (imaginaryPositive upper)

qExponentRealNegative :
  ∀ {C tau} →
  (laws : QDiskAnalyticLaws C) →
  UpperHalfPlanePoint C tau →
  Real._<_
    (Real.real (Complex.realPackage C))
    (Real.neg
      (Real.real (Complex.realPackage C))
      (Real._*_
        (Real.real (Complex.realPackage C))
        (twoPi laws)
        (Complex.im tau)))
    (Real.zero (Real.real (Complex.realPackage C)))
qExponentRealNegative laws upper =
  negativeOfPositiveIsNegative laws
    (qDecayRatePositive laws upper)

------------------------------------------------------------------------
-- 4. Exact q modulus formula.
------------------------------------------------------------------------

qModulusFormula :
  ∀ {C tau} →
  (laws : QDiskAnalyticLaws C) →
  modulus laws (Q.qOf C tau)
  ≡
  Real.exp
    (Real.exponential (Complex.realPackage C))
    (Real.neg
      (Real.real (Complex.realPackage C))
      (Real._*_
        (Real.real (Complex.realPackage C))
        (twoPi laws)
        (Complex.im tau)))
qModulusFormula {C} {tau} laws =
  trans
    (cong
      (modulus laws)
      (cong
        (Complex.expC (Complex.complexExponential C))
        (qExponentCartesian laws tau)))
    (modulusOfComplexExponential laws
      (Real.neg
        (Real.real (Complex.realPackage C))
        (Real._*_
          (Real.real (Complex.realPackage C))
          (twoPi laws)
          (Complex.im tau)))
      (Real._*_
        (Real.real (Complex.realPackage C))
        (twoPi laws)
        (Complex.re tau)))

------------------------------------------------------------------------
-- 5. Main theorem: upper half plane implies |q| < 1.
------------------------------------------------------------------------

qInsideUnitDisk :
  ∀ {C tau} →
  (laws : QDiskAnalyticLaws C) →
  UpperHalfPlanePoint C tau →
  Real._<_
    (Real.real (Complex.realPackage C))
    (modulus laws (Q.qOf C tau))
    (Real.one (Real.real (Complex.realPackage C)))
qInsideUnitDisk {C} {tau} laws upper =
  let
    R = Real.real (Complex.realPackage C)
    E = Real.exponential (Complex.realPackage C)

    expStrict :
      Real._<_ R
        (Real.exp E
          (Real.neg R
            (Real._*_ R (twoPi laws) (Complex.im tau))))
        (Real.exp E (Real.zero R))
    expStrict =
      Real.expStrictMonotone E
        (qExponentRealNegative laws upper)
  in
  subst
    (λ left →
      Real._<_ R left (Real.one R))
    (sym (qModulusFormula laws))
    (subst
      (λ right →
        Real._<_ R
          (Real.exp E
            (Real.neg R
              (Real._*_ R (twoPi laws) (Complex.im tau))))
          right)
      (Real.expZero E)
      expStrict)

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

record EisensteinQDiskBoundary : Set where
  constructor eisenstein-q-disk-boundary
  field
    upperHalfPlanePredicateConcrete : Bool
    qExponentCartesianTargetExact : Bool
    qModulusReductionExact : Bool
    exponentialStrictMonotonicityAlreadyOwned : Bool
    upperHalfPlaneImpliesQInsideUnitDiskDerived : Bool

    qExponentCartesianInstantiatedForSelectedBackend : Bool
    modulusExponentialLawInstantiatedForSelectedBackend : Bool

    nextResidual : String

open EisensteinQDiskBoundary public

canonicalEisensteinQDiskBoundary : EisensteinQDiskBoundary
canonicalEisensteinQDiskBoundary =
  eisenstein-q-disk-boundary
    true true true true true
    false false
    "instantiate qExponentCartesian and modulusOfComplexExponential from the selected constructive-real ring/trigonometric laws; the abstract implication Im(tau)>0 -> |q(tau)|<1 is already compiled"
