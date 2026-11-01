module DASHI.Moonshine.EisensteinTruncationSeriesAlignmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q

private
  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C =
    Complex.ComplexPair (Real.real (Complex.realPackage C))

negC :
  ∀ {R} →
  Complex.ComplexPair R →
  Complex.ComplexPair R
negC {R} (Complex.complex x y) =
  Complex.complex (Real.neg R x) (Real.neg R y)

complexAddZeroRight :
  ∀ {R} →
  (z : Complex.ComplexPair R) →
  Complex._+C_ z Complex.zeroC ≡ z
complexAddZeroRight {R} (Complex.complex x y)
  rewrite Real.addZeroRight R x
        | Real.addZeroRight R y = refl

complexAddAssoc :
  ∀ {R} →
  (x y z : Complex.ComplexPair R) →
  Complex._+C_ (Complex._+C_ x y) z
  ≡
  Complex._+C_ x (Complex._+C_ y z)
complexAddAssoc {R}
  (Complex.complex xr xi)
  (Complex.complex yr yi)
  (Complex.complex zr zi)
  rewrite Real.addAssoc R xr yr zr
        | Real.addAssoc R xi yi zi = refl

complexSubAsAddNeg :
  ∀ {R} →
  Ring.ConstructedRealRingNormalisationLaws R →
  (x y : Complex.ComplexPair R) →
  Complex._-C_ x y
  ≡
  Complex._+C_ x (negC y)
complexSubAsAddNeg {R} laws
  (Complex.complex xr xi)
  (Complex.complex yr yi)
  rewrite Ring.subAsAddNeg laws xr yr
        | Ring.subAsAddNeg laws xi yi = refl

e4SeriesTerm :
  (C : Complex.ConstructedComplexPackage) →
  Q.DivisorPowerKernel →
  ComplexCarrier C →
  Nat →
  ComplexCarrier C
e4SeriesTerm C kernel tau zero = Complex.zeroC
e4SeriesTerm C kernel tau (suc n) =
  Q.scaleNatC
    (240 * Q.sigma3 kernel (suc n))
    (Q.powC (Q.qOf C tau) (suc n))

e6PositiveTerm :
  (C : Complex.ConstructedComplexPackage) →
  Q.DivisorPowerKernel →
  ComplexCarrier C →
  Nat →
  ComplexCarrier C
e6PositiveTerm C kernel tau zero = Complex.zeroC
e6PositiveTerm C kernel tau (suc n) =
  Q.scaleNatC
    (504 * Q.sigma5 kernel (suc n))
    (Q.powC (Q.qOf C tau) (suc n))

e6SeriesTerm :
  (C : Complex.ConstructedComplexPackage) →
  Q.DivisorPowerKernel →
  ComplexCarrier C →
  Nat →
  ComplexCarrier C
e6SeriesTerm C kernel tau zero = Complex.zeroC
e6SeriesTerm C kernel tau (suc n) =
  negC (e6PositiveTerm C kernel tau (suc n))

complexFiniteSumThrough :
  ∀ {C} →
  (Nat → ComplexCarrier C) →
  Nat →
  ComplexCarrier C
complexFiniteSumThrough term zero = term zero
complexFiniteSumThrough term (suc n) =
  Complex._+C_
    (complexFiniteSumThrough term n)
    (term (suc n))

e4TruncatedIsConstantPlusSeries :
  (C : Complex.ConstructedComplexPackage) →
  (kernel : Q.DivisorPowerKernel) →
  (tau : ComplexCarrier C) →
  (n : Nat) →
  Q.e4Truncated C kernel n tau
  ≡
  Complex._+C_
    Complex.oneC
    (complexFiniteSumThrough (e4SeriesTerm C kernel tau) n)
e4TruncatedIsConstantPlusSeries C kernel tau zero =
  sym (complexAddZeroRight Complex.oneC)
e4TruncatedIsConstantPlusSeries C kernel tau (suc n) =
  trans
    (cong
      (λ previous →
        Complex._+C_
          previous
          (e4SeriesTerm C kernel tau (suc n)))
      (e4TruncatedIsConstantPlusSeries C kernel tau n))
    (complexAddAssoc
      Complex.oneC
      (complexFiniteSumThrough (e4SeriesTerm C kernel tau) n)
      (e4SeriesTerm C kernel tau (suc n)))

e6TruncatedIsConstantPlusSeries :
  (C : Complex.ConstructedComplexPackage) →
  (laws :
    Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C))) →
  (kernel : Q.DivisorPowerKernel) →
  (tau : ComplexCarrier C) →
  (n : Nat) →
  Q.e6Truncated C kernel n tau
  ≡
  Complex._+C_
    Complex.oneC
    (complexFiniteSumThrough (e6SeriesTerm C kernel tau) n)
e6TruncatedIsConstantPlusSeries C laws kernel tau zero =
  sym (complexAddZeroRight Complex.oneC)
e6TruncatedIsConstantPlusSeries C laws kernel tau (suc n) =
  trans
    (complexSubAsAddNeg laws
      (Q.e6Truncated C kernel n tau)
      (e6PositiveTerm C kernel tau (suc n)))
    (trans
      (cong
        (λ previous →
          Complex._+C_
            previous
            (e6SeriesTerm C kernel tau (suc n)))
        (e6TruncatedIsConstantPlusSeries C laws kernel tau n))
      (complexAddAssoc
        Complex.oneC
        (complexFiniteSumThrough (e6SeriesTerm C kernel tau) n)
        (e6SeriesTerm C kernel tau (suc n))))

record EisensteinSeriesAlignmentBoundary : Set where
  constructor eisenstein-series-alignment-boundary
  field
    e4ZeroIndexTermExplicit : Bool
    e6ZeroIndexTermExplicit : Bool
    e6SubtractionNormalizedByExistingRingLaw : Bool
    e4TruncationAlignedWithAdditiveSeries : Bool
    e6TruncationAlignedWithAdditiveSeries : Bool

open import Agda.Builtin.Bool using (Bool; true)
open EisensteinSeriesAlignmentBoundary public

canonicalEisensteinSeriesAlignmentBoundary :
  EisensteinSeriesAlignmentBoundary
canonicalEisensteinSeriesAlignmentBoundary =
  eisenstein-series-alignment-boundary
    true true true true true
