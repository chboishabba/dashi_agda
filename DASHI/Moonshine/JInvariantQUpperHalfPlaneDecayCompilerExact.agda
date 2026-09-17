module DASHI.Moonshine.JInvariantQUpperHalfPlaneDecayCompilerExact where

------------------------------------------------------------------------
-- UPPER-HALF-PLANE -> q DECAY COMPILER
--
-- The previous owners have already paid two independent pieces:
--
--   * exact Cartesian normalization
--       Re((2*pi*i)tau) = -(2*pi*Im(tau));
--   * principal-strip modulus
--       |q(tau)| = exp(Re((2*pi*i)tau)),
--     with negative real part implying |q(tau)|<1.
--
-- This owner isolates exactly the strict-order structure missing from the bare
-- `ConstructedOrderedCompleteReal` record.  No stronger ordered-field package
-- is silently assumed.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as FiniteQ
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as QModulus
import DASHI.Moonshine.JInvariantQExponentCartesianNormalizationExact as Cartesian

record QUpperHalfPlaneOrderLaws
    (C : Complex.ConstructedComplexPackage) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
  field
    twoPiPositive :
      Real._<_ R (Real.zero R) (Cartesian.twoPi C)

    positiveProduct :
      ∀ x y →
      Real._<_ R (Real.zero R) x →
      Real._<_ R (Real.zero R) y →
      Real._<_ R (Real.zero R) (Real._*_ R x y)

    negativeOfPositiveIsNegative :
      ∀ x →
      Real._<_ R (Real.zero R) x →
      Real._<_ R (Real.neg R x) (Real.zero R)

open QUpperHalfPlaneOrderLaws public

upperHalfPlaneGivesNegativeQExponentRealPart :
  ∀ {C : Complex.ConstructedComplexPackage} →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  (O : QUpperHalfPlaneOrderLaws C) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C)))
    (Complex.im tau) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Complex.re (QModulus.qExponent C tau))
    (Real.zero (Real.real (Complex.realPackage C)))
upperHalfPlaneGivesNegativeQExponentRealPart {C} N O tau imPositive =
  let
    R = Real.real (Complex.realPackage C)
    productPositive =
      positiveProduct O
        (Cartesian.twoPi C)
        (Complex.im tau)
        (twoPiPositive O)
        imPositive
    normalizedNegative =
      negativeOfPositiveIsNegative O
        (Real._*_ R (Cartesian.twoPi C) (Complex.im tau))
        productPositive
  in
  subst
    (λ value → Real._<_ R value (Real.zero R))
    (sym (Cartesian.qExponentRealPartExact C N tau))
    normalizedNegative

upperHalfPlaneQBelowOneOnPrincipalStrip :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (N : Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C)))
    (O : QUpperHalfPlaneOrderLaws C)
    (polar : Polar.OrdinaryPolarData C D F)
    (branch : Polar.OrdinaryPrincipalBranchLaws C D F polar)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip polar (QModulus.qExponent C tau)) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C)))
    (Complex.im tau) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (FiniteQ.qOf C tau))
    (Real.one (Real.real (Complex.realPackage C)))
upperHalfPlaneQBelowOneOnPrincipalStrip N O polar branch tau strip imPositive =
  QModulus.qModulusBelowOneFromNegativeRealPart
    polar branch tau strip
    (upperHalfPlaneGivesNegativeQExponentRealPart N O tau imPositive)

------------------------------------------------------------------------
-- Frontier: all q-decay mathematics is now compiled except for inhabiting the
-- tiny order package on the selected concrete real/complex backend and proving
-- the q exponent lies in the polar principal strip for the selected tau chart.
------------------------------------------------------------------------

record QUpperHalfPlaneDecayBoundary : Set where
  constructor q-upper-half-plane-decay-boundary
  field
    exactCartesianNormalizationReused : Bool
    principalLogModulusRouteReused : Bool
    abstractSpinePretendsToBeOrderedField : Bool
    strictOrderCutsetExplicit : Bool
    upperHalfPlaneToNegativeExponentCompilerPaid : Bool
    negativeExponentToQBelowOneCompilerPaid : Bool
    concreteOrderCutsetInhabited : Bool
    principalStripFromTauChartInhabited : Bool
    reading : String

open QUpperHalfPlaneDecayBoundary public

canonicalQUpperHalfPlaneDecayBoundary : QUpperHalfPlaneDecayBoundary
canonicalQUpperHalfPlaneDecayBoundary =
  q-upper-half-plane-decay-boundary
    true true false true true true false false
    "upper-half-plane q decay is now a compiler from explicit two-pi positivity, positive-product, negation-order, and principal-strip evidence; the generic spine is not silently strengthened, and Pythagorean is absent from the route"
