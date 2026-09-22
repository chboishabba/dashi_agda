module DASHI.Moonshine.JInvariantEisensteinAgdaLeanExtractionExact where

------------------------------------------------------------------------
-- ACTUAL AGDA q/E4_N/E6_N -> TARGET COMPLEX EXTRACTION
--
-- Source object:
--   DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact
--
-- This module factors the cross-prover seam below q/E4/E6 themselves.
-- A target complex carrier only has to receive the actual DASHI ComplexPair
-- carrier while preserving the primitive constants, ring operations, pi and
-- complex exponential.  Theorems below then transport the literal qOf,
-- e4Truncated and e6Truncated definitions by recursion.
--
-- In particular this is stronger than declaring three unrelated pointwise
-- q/E4/E6 equalities, but weaker than claiming any current map into Lean's
-- Complex has already been constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q

------------------------------------------------------------------------
-- Target algebra: intended Lean instantiation is ordinary Complex.
------------------------------------------------------------------------

record TargetComplexAlgebra : Set₁ where
  field
    Carrier : Set
    zeroT oneT imaginaryUnitT piT : Carrier
    addT subT mulT : Carrier → Carrier → Carrier
    expT : Carrier → Carrier

open TargetComplexAlgebra public

targetScaleNat :
  (T : TargetComplexAlgebra) →
  Nat → Carrier T → Carrier T
targetScaleNat T zero z = zeroT T
targetScaleNat T (suc n) z =
  addT T z (targetScaleNat T n z)

targetPow :
  (T : TargetComplexAlgebra) →
  Carrier T → Nat → Carrier T
targetPow T z zero = oneT T
targetPow T z (suc n) =
  mulT T z (targetPow T z n)

targetQ :
  (T : TargetComplexAlgebra) →
  Carrier T → Carrier T
targetQ T tau =
  expT T
    (mulT T
      (targetScaleNat T 2
        (mulT T (imaginaryUnitT T) (piT T)))
      tau)

targetE4Truncated :
  (T : TargetComplexAlgebra) →
  Q.DivisorPowerKernel →
  Nat →
  Carrier T →
  Carrier T
targetE4Truncated T kernel zero q = oneT T
targetE4Truncated T kernel (suc n) q =
  addT T
    (targetE4Truncated T kernel n q)
    (targetScaleNat T
      (240 * Q.sigma3 kernel (suc n))
      (targetPow T q (suc n)))

targetE6Truncated :
  (T : TargetComplexAlgebra) →
  Q.DivisorPowerKernel →
  Nat →
  Carrier T →
  Carrier T
targetE6Truncated T kernel zero q = oneT T
targetE6Truncated T kernel (suc n) q =
  subT T
    (targetE6Truncated T kernel n q)
    (targetScaleNat T
      (504 * Q.sigma5 kernel (suc n))
      (targetPow T q (suc n)))

------------------------------------------------------------------------
-- The load-bearing representation morphism.
------------------------------------------------------------------------

record ComplexExtraction
  (C : Complex.ConstructedComplexPackage)
  (T : TargetComplexAlgebra) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C

  field
    mapC : Complex.ComplexPair R → Carrier T

    preservesZero :
      mapC Complex.zeroC ≡ zeroT T

    preservesOne :
      mapC Complex.oneC ≡ oneT T

    preservesImaginaryUnit :
      mapC Complex.imaginaryUnit ≡ imaginaryUnitT T

    preservesPiComplex :
      mapC (Complex.complex (Complex.pi CE) (Real.zero R))
      ≡ piT T

    preservesAdd :
      ∀ x y →
      mapC (Complex._+C_ x y)
      ≡ addT T (mapC x) (mapC y)

    preservesSub :
      ∀ x y →
      mapC (Complex._-C_ x y)
      ≡ subT T (mapC x) (mapC y)

    preservesMul :
      ∀ x y →
      mapC (Complex._*C_ x y)
      ≡ mulT T (mapC x) (mapC y)

    preservesExp :
      ∀ z →
      mapC (Complex.expC CE z)
      ≡ expT T (mapC z)

open ComplexExtraction public

------------------------------------------------------------------------
-- Primitive operations compile through the extraction.
------------------------------------------------------------------------

mapScaleNat :
  ∀ {C T}
    (E : ComplexExtraction C T)
    (n : Nat)
    (z : Complex.ComplexPair
      (Real.real (Complex.realPackage C))) →
  mapC E (Q.scaleNatC n z)
  ≡ targetScaleNat T n (mapC E z)
mapScaleNat E zero z
  rewrite preservesZero E = refl
mapScaleNat E (suc n) z
  rewrite preservesAdd E z (Q.scaleNatC n z)
        | mapScaleNat E n z = refl

mapPow :
  ∀ {C T}
    (E : ComplexExtraction C T)
    (z : Complex.ComplexPair
      (Real.real (Complex.realPackage C)))
    (n : Nat) →
  mapC E (Q.powC z n)
  ≡ targetPow T (mapC E z) n
mapPow E z zero
  rewrite preservesOne E = refl
mapPow E z (suc n)
  rewrite preservesMul E z (Q.powC z n)
        | mapPow E z n = refl

------------------------------------------------------------------------
-- The actual qOf definition transports from the primitive laws.
------------------------------------------------------------------------

mapQOf :
  ∀ {C T}
    (E : ComplexExtraction C T)
    (tau : Complex.ComplexPair
      (Real.real (Complex.realPackage C))) →
  mapC E (Q.qOf C tau)
  ≡ targetQ T (mapC E tau)
mapQOf {C} {T} E tau
  rewrite preservesExp E
    (Complex._*C_
      (Q.scaleNatC 2
        (Complex._*C_
          Complex.imaginaryUnit
          (Complex.complex
            (Complex.pi (Complex.complexExponential C))
            (Real.zero (Real.real (Complex.realPackage C))))))
      tau)
        | preservesMul E
            (Q.scaleNatC 2
              (Complex._*C_
                Complex.imaginaryUnit
                (Complex.complex
                  (Complex.pi (Complex.complexExponential C))
                  (Real.zero (Real.real (Complex.realPackage C))))))
            tau
        | mapScaleNat E 2
            (Complex._*C_
              Complex.imaginaryUnit
              (Complex.complex
                (Complex.pi (Complex.complexExponential C))
                (Real.zero (Real.real (Complex.realPackage C)))))
        | preservesMul E
            Complex.imaginaryUnit
            (Complex.complex
              (Complex.pi (Complex.complexExponential C))
              (Real.zero (Real.real (Complex.realPackage C))))
        | preservesImaginaryUnit E
        | preservesPiComplex E
  = refl

------------------------------------------------------------------------
-- The literal finite E4/E6 recurrences now transport by induction.
------------------------------------------------------------------------

mapE4Truncated :
  ∀ {C T}
    (E : ComplexExtraction C T)
    (kernel : Q.DivisorPowerKernel)
    (terms : Nat)
    (tau : Complex.ComplexPair
      (Real.real (Complex.realPackage C))) →
  mapC E (Q.e4Truncated C kernel terms tau)
  ≡ targetE4Truncated T kernel terms (mapC E (Q.qOf C tau))
mapE4Truncated E kernel zero tau
  rewrite preservesOne E = refl
mapE4Truncated {C} {T} E kernel (suc n) tau
  rewrite preservesAdd E
            (Q.e4Truncated C kernel n tau)
            (Q.scaleNatC
              (240 * Q.sigma3 kernel (suc n))
              (Q.powC (Q.qOf C tau) (suc n)))
        | mapE4Truncated E kernel n tau
        | mapScaleNat E
            (240 * Q.sigma3 kernel (suc n))
            (Q.powC (Q.qOf C tau) (suc n))
        | mapPow E (Q.qOf C tau) (suc n)
  = refl

mapE6Truncated :
  ∀ {C T}
    (E : ComplexExtraction C T)
    (kernel : Q.DivisorPowerKernel)
    (terms : Nat)
    (tau : Complex.ComplexPair
      (Real.real (Complex.realPackage C))) →
  mapC E (Q.e6Truncated C kernel terms tau)
  ≡ targetE6Truncated T kernel terms (mapC E (Q.qOf C tau))
mapE6Truncated E kernel zero tau
  rewrite preservesOne E = refl
mapE6Truncated {C} {T} E kernel (suc n) tau
  rewrite preservesSub E
            (Q.e6Truncated C kernel n tau)
            (Q.scaleNatC
              (504 * Q.sigma5 kernel (suc n))
              (Q.powC (Q.qOf C tau) (suc n)))
        | mapE6Truncated E kernel n tau
        | mapScaleNat E
            (504 * Q.sigma5 kernel (suc n))
            (Q.powC (Q.qOf C tau) (suc n))
        | mapPow E (Q.qOf C tau) (suc n)
  = refl

------------------------------------------------------------------------
-- Stronger corollaries: replace extracted q by the target's canonical q.
------------------------------------------------------------------------

mapE4TruncatedCanonicalQ :
  ∀ {C T}
    (E : ComplexExtraction C T)
    (kernel : Q.DivisorPowerKernel)
    (terms : Nat)
    (tau : Complex.ComplexPair
      (Real.real (Complex.realPackage C))) →
  mapC E (Q.e4Truncated C kernel terms tau)
  ≡ targetE4Truncated T kernel terms (targetQ T (mapC E tau))
mapE4TruncatedCanonicalQ E kernel terms tau
  rewrite mapE4Truncated E kernel terms tau
        | mapQOf E tau
  = refl

mapE6TruncatedCanonicalQ :
  ∀ {C T}
    (E : ComplexExtraction C T)
    (kernel : Q.DivisorPowerKernel)
    (terms : Nat)
    (tau : Complex.ComplexPair
      (Real.real (Complex.realPackage C))) →
  mapC E (Q.e6Truncated C kernel terms tau)
  ≡ targetE6Truncated T kernel terms (targetQ T (mapC E tau))
mapE6TruncatedCanonicalQ E kernel terms tau
  rewrite mapE6Truncated E kernel terms tau
        | mapQOf E tau
  = refl

------------------------------------------------------------------------
-- Frontier: the recursion is paid; the concrete Lean Complex extraction is not.
------------------------------------------------------------------------

record AgdaLeanEisensteinExtractionBoundary : Set where
  constructor agda-lean-eisenstein-extraction-boundary
  field
    actualQOfTransportCompilerOwned : Bool
    actualE4TruncatedTransportCompilerOwned : Bool
    actualE6TruncatedTransportCompilerOwned : Bool
    transportDerivedFromPrimitiveAlgebraExpLaws : Bool
    canonicalDivisorKernelSharedDefinitionRequired : Bool

    concreteMapIntoLeanComplexInhabited : Bool
    agdaConstructedRealIdentifiedWithLeanReal : Bool
    agdaComplexExpIdentifiedWithLeanComplexExp : Bool
    infiniteLimitTransportPaid : Bool
    deltaNormalizationTransportPaid : Bool

canonicalAgdaLeanEisensteinExtractionBoundary :
  AgdaLeanEisensteinExtractionBoundary
canonicalAgdaLeanEisensteinExtractionBoundary =
  agda-lean-eisenstein-extraction-boundary
    true true true true true
    false false false false false
