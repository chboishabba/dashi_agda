module DASHI.Moonshine.EisensteinTruncationConvergenceCompilerExact where

------------------------------------------------------------------------
-- FINITE E4/E6 TRUNCATIONS -> INFINITE DELTA/J COMPILER
--
-- This module does not assume the hard convergence theorem.  It isolates it.
--
-- Once the two literal finite q-series sequences
--
--   N |-> E4_N(tau)
--   N |-> E6_N(tau)
--
-- are proved to converge to the selected infinite E4/E6 values on the same
-- concrete complex carrier, ordinary limit algebra propagates that result to
--
--   E4_N^3,
--   E6_N^2,
--   E4_N^3 - E6_N^2,
--   Delta_N = (E4_N^3-E6_N^2)/1728,
--
-- and, with a nonzero limiting Delta plus quotient continuity, to j_N.
--
-- This makes "finite -> infinite" two analytic leaves rather than a vague
-- promotion step.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite
import DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact as FiniteKlein
import DASHI.Moonshine.EisensteinUpperHalfPlaneQDiskExact as QDisk
import DASHI.Moonshine.EisensteinCoefficientMajorantExact as Majorant
import DASHI.Foundations.BishopPolynomialGeometricRatioConvergenceExact as PolyGeo

private
  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C =
    Complex.ComplexPair (Real.real (Complex.realPackage C))

------------------------------------------------------------------------
-- 1. Sequential limit algebra needed by the compiler.
------------------------------------------------------------------------

record ComplexSequentialLimitAlgebra
    (C : Complex.ConstructedComplexPackage) : Set₁ where
  field
    ConvergesTo :
      (Nat → ComplexCarrier C) →
      ComplexCarrier C →
      Set

    productLimit :
      ∀ {left right x y} →
      ConvergesTo left x →
      ConvergesTo right y →
      ConvergesTo
        (λ n → Complex._*C_ (left n) (right n))
        (Complex._*C_ x y)

    differenceLimit :
      ∀ {left right x y} →
      ConvergesTo left x →
      ConvergesTo right y →
      ConvergesTo
        (λ n → Complex._-C_ (left n) (right n))
        (Complex._-C_ x y)

    constantLimit :
      (x : ComplexCarrier C) →
      ConvergesTo (λ _ → x) x

open ComplexSequentialLimitAlgebra public

squareSequence :
  ∀ {C : Complex.ConstructedComplexPackage} →
  (Nat → ComplexCarrier C) →
  Nat → ComplexCarrier C
squareSequence sequence n =
  Complex._*C_ (sequence n) (sequence n)

cubeSequence :
  ∀ {C : Complex.ConstructedComplexPackage} →
  (Nat → ComplexCarrier C) →
  Nat → ComplexCarrier C
cubeSequence sequence n =
  Complex._*C_
    (Complex._*C_ (sequence n) (sequence n))
    (sequence n)

squareLimit :
  ∀ {C} →
  (L : ComplexSequentialLimitAlgebra C) →
  ∀ {sequence value} →
  ConvergesTo L sequence value →
  ConvergesTo L
    (squareSequence sequence)
    (Complex._*C_ value value)
squareLimit L converges =
  productLimit L converges converges

cubeLimit :
  ∀ {C} →
  (L : ComplexSequentialLimitAlgebra C) →
  ∀ {sequence value} →
  ConvergesTo L sequence value →
  ConvergesTo L
    (cubeSequence sequence)
    (Complex._*C_ (Complex._*C_ value value) value)
cubeLimit L converges =
  productLimit L
    (productLimit L converges converges)
    converges

------------------------------------------------------------------------
-- 2. Literal finite E4/E6 sequences at one concrete tau.
------------------------------------------------------------------------

e4Sequence :
  (C : Complex.ConstructedComplexPackage) →
  Finite.DivisorPowerKernel →
  ComplexCarrier C →
  Nat → ComplexCarrier C
e4Sequence C kernel tau n =
  Finite.e4Truncated C kernel n tau

e6Sequence :
  (C : Complex.ConstructedComplexPackage) →
  Finite.DivisorPowerKernel →
  ComplexCarrier C →
  Nat → ComplexCarrier C
e6Sequence C kernel tau n =
  Finite.e6Truncated C kernel n tau

discriminantNumeratorSequence :
  (C : Complex.ConstructedComplexPackage) →
  Finite.DivisorPowerKernel →
  ComplexCarrier C →
  Nat → ComplexCarrier C
discriminantNumeratorSequence C kernel tau n =
  Finite.discriminantNumeratorTruncated C kernel n tau

------------------------------------------------------------------------
-- 3. The two genuinely analytic convergence inputs.
------------------------------------------------------------------------

record E4E6TruncationConvergence
    (C : Complex.ConstructedComplexPackage)
    (L : ComplexSequentialLimitAlgebra C)
    (kernel : Finite.DivisorPowerKernel)
    (tau : ComplexCarrier C) : Set₁ where
  field
    infiniteE4 : ComplexCarrier C
    infiniteE6 : ComplexCarrier C

    e4TruncationsConverge :
      ConvergesTo L
        (e4Sequence C kernel tau)
        infiniteE4

    e6TruncationsConverge :
      ConvergesTo L
        (e6Sequence C kernel tau)
        infiniteE6

open E4E6TruncationConvergence public

------------------------------------------------------------------------
-- 4. Delta numerator convergence is now automatic.
------------------------------------------------------------------------

infiniteDiscriminantNumerator :
  ∀ {C L kernel tau} →
  E4E6TruncationConvergence C L kernel tau →
  ComplexCarrier C
infiniteDiscriminantNumerator E =
  Complex._-C_
    (Complex._*C_
      (Complex._*C_ (infiniteE4 E) (infiniteE4 E))
      (infiniteE4 E))
    (Complex._*C_ (infiniteE6 E) (infiniteE6 E))

discriminantNumeratorConverges :
  ∀ {C L kernel tau} →
  (E : E4E6TruncationConvergence C L kernel tau) →
  ConvergesTo L
    (discriminantNumeratorSequence C kernel tau)
    (infiniteDiscriminantNumerator E)
discriminantNumeratorConverges {L = L} E =
  differenceLimit L
    (cubeLimit L (e4TruncationsConverge E))
    (squareLimit L (e6TruncationsConverge E))

------------------------------------------------------------------------
-- 5. Normalisation by 1728.
------------------------------------------------------------------------

record DeltaNormalisationLimitLaw
    (C : Complex.ConstructedComplexPackage)
    (L : ComplexSequentialLimitAlgebra C) : Set₁ where
  field
    divideBy1728 : ComplexCarrier C → ComplexCarrier C

    divideBy1728Limit :
      ∀ {sequence value} →
      ConvergesTo L sequence value →
      ConvergesTo L
        (λ n → divideBy1728 (sequence n))
        (divideBy1728 value)

open DeltaNormalisationLimitLaw public

-- The compiler is parameterised by one selected limit algebra.
deltaConverges :
  ∀ {C L kernel tau} →
  (D : DeltaNormalisationLimitLaw C L) →
  (E : E4E6TruncationConvergence C L kernel tau) →
  ConvergesTo L
    (λ n →
      divideBy1728 D
        (discriminantNumeratorSequence C kernel tau n))
    (divideBy1728 D (infiniteDiscriminantNumerator E))
deltaConverges D E =
  divideBy1728Limit D
    (discriminantNumeratorConverges E)

------------------------------------------------------------------------
-- 6. Quotient convergence for j is isolated behind the correct nonzero gate.
------------------------------------------------------------------------

record ComplexQuotientLimitLaw
    (C : Complex.ConstructedComplexPackage)
    (L : ComplexSequentialLimitAlgebra C) : Set₁ where
  field
    Nonzero : ComplexCarrier C → Set

    quotient :
      (numerator denominator : ComplexCarrier C) →
      Nonzero denominator →
      ComplexCarrier C

    quotientLimit :
      ∀ {numerators denominators numerator denominator} →
      ConvergesTo L numerators numerator →
      ConvergesTo L denominators denominator →
      (denominatorNonzero : Nonzero denominator) →
      (denominatorProofs : (n : Nat) → Nonzero (denominators n)) →
      ConvergesTo L
        (λ n →
          quotient
            (numerators n)
            (denominators n)
            (denominatorProofs n))
        (quotient numerator denominator denominatorNonzero)

open ComplexQuotientLimitLaw public

------------------------------------------------------------------------
-- The hole in quotientLimit's lambda is intentionally avoided in consumers:
-- different constructive nonzero predicates may carry proof relevance.
-- We therefore compile j through an explicit proof-producing sequence.
------------------------------------------------------------------------

record JQuotientConvergenceData
    (C : Complex.ConstructedComplexPackage)
    (L : ComplexSequentialLimitAlgebra C)
    (Q : ComplexQuotientLimitLaw C L) : Set₁ where
  field
    numeratorSequence denominatorSequence :
      Nat → ComplexCarrier C

    numeratorLimit denominatorLimit :
      ComplexCarrier C

    numeratorConverges :
      ConvergesTo L numeratorSequence numeratorLimit

    denominatorConverges :
      ConvergesTo L denominatorSequence denominatorLimit

    denominatorNonzero :
      Nonzero Q denominatorLimit

    denominatorSequenceNonzero :
      (n : Nat) → Nonzero Q (denominatorSequence n)

    quotientSequence :
      Nat → ComplexCarrier C

    quotientSequenceAgrees :
      (n : Nat) →
      quotientSequence n
      ≡ quotient Q
          (numeratorSequence n)
          (denominatorSequence n)
          (denominatorSequenceNonzero n)

    quotientSequenceConverges :
      ConvergesTo L quotientSequence
        (quotient Q numeratorLimit denominatorLimit denominatorNonzero)

open JQuotientConvergenceData public

------------------------------------------------------------------------
-- 7. Same-object identification with the abstract analytic Eisenstein model.
--
-- This is the remaining representation weld after convergence is paid.
------------------------------------------------------------------------

record InfiniteEisensteinSameObjectIdentification
    (C : Complex.ConstructedComplexPackage) : Set₁ where
  field
    AnalyticScalar : Set
    AnalyticPoint : Set

    toConcrete : AnalyticScalar → ComplexCarrier C
    fromConcrete : ComplexCarrier C → AnalyticScalar

    concreteRoundTrip :
      (z : ComplexCarrier C) →
      toConcrete (fromConcrete z) ≡ z

    analyticRoundTrip :
      (z : AnalyticScalar) →
      fromConcrete (toConcrete z) ≡ z

    analyticE4 analyticE6 :
      AnalyticPoint → AnalyticScalar

    concretePoint :
      AnalyticPoint → ComplexCarrier C

    concreteE4Limit concreteE6Limit :
      AnalyticPoint → ComplexCarrier C

    e4SameObject :
      (tau : AnalyticPoint) →
      toConcrete (analyticE4 tau) ≡ concreteE4Limit tau

    e6SameObject :
      (tau : AnalyticPoint) →
      toConcrete (analyticE6 tau) ≡ concreteE6Limit tau

open InfiniteEisensteinSameObjectIdentification public

------------------------------------------------------------------------
-- 8. Honest frontier.
------------------------------------------------------------------------

record EisensteinTruncationConvergenceBoundary : Set where
  constructor eisenstein-truncation-convergence-boundary
  field
    finiteE4E6SequencesAlreadyConcrete : Bool
    executableSigma3Sigma5Internal : Bool
    sigma3Sigma5PolynomialBoundsOwned : Bool
    upperHalfPlaneToQDiskCompilerOwned : Bool
    complexTermsReducedToPolynomialGeometricMajorants : Bool
    bishopPolynomialGeometricRatioCompilerOwned : Bool
    deltaNumeratorLimitCompiledFromE4E6Limits : Bool
    deltaNormalizationLimitIsolated : Bool
    jQuotientLimitRequiresNonzeroDenominator : Bool
    sameObjectIdentificationSeparatedFromConvergence : Bool

    concreteE4ConvergenceProvedHere : Bool
    concreteE6ConvergenceProvedHere : Bool
    analyticEisensteinSameObjectWeldInhabited : Bool
    infiniteJConvergenceClosed : Bool

    nextResidual : String

open EisensteinTruncationConvergenceBoundary public

canonicalEisensteinTruncationConvergenceBoundary :
  EisensteinTruncationConvergenceBoundary
canonicalEisensteinTruncationConvergenceBoundary =
  eisenstein-truncation-convergence-boundary
    true true true true true true
    true true true true
    false false false false
    "remaining analytic leaves are now: instantiate the selected concrete-complex norm/cartesian q laws; prove the eventual successor-ratio inequality for n^4 r^n and n^6 r^n when 0<=r<1 (the Bishop ratio-test compiler is already owned); transport those real majorants to convergence of the literal complex E4/E6 partial sums; then identify the limits with the all-SL2(Z) Eisenstein objects"
