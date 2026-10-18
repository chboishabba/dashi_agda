module DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact where

------------------------------------------------------------------------
-- ORDINARY COMPLEX PAIRS DIRECTLY OVER THE PINNED MURRAY--BISHOP REAL CARRIER
--
-- This avoids a second generic-real carrier on the RH low-side route.  The
-- analytic function layer remains independent; only ordinary complex geometry
-- is fixed here.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import Real as Bishop
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopLocatedHeightCarrierExact as Height

record BishopComplex : Set where
  constructor bishop-complex
  field
    re im : Bishop.ℝ

open BishopComplex public

zeroC oneC : BishopComplex
zeroC = bishop-complex Bishop.0ℝ Bishop.0ℝ
oneC = bishop-complex Bishop.1ℝ Bishop.0ℝ

_+C_ : BishopComplex → BishopComplex → BishopComplex
bishop-complex a b +C bishop-complex c d =
  bishop-complex
    (Bishop._+_ a c)
    (Bishop._+_ b d)

_*C_ : BishopComplex → BishopComplex → BishopComplex
bishop-complex a b *C bishop-complex c d =
  bishop-complex
    (Bishop._-_
      (Bishop._*_ a c)
      (Bishop._*_ b d))
    (Bishop._+_
      (Bishop._*_ a d)
      (Bishop._*_ b c))

negC : BishopComplex → BishopComplex
negC (bishop-complex a b) =
  bishop-complex (Bishop.-_ a) (Bishop.-_ b)

conjC : BishopComplex → BishopComplex
conjC (bishop-complex a b) =
  bishop-complex a (Bishop.-_ b)

record BishopComplexAnalyticFunctionLayer : Set₁ where
  field
    Function : Set
    apply : Function → BishopComplex → BishopComplex
    Holomorphic : Function → Set
    Entire : Function → Set
    Meromorphic : Function → Set
    SimplePoleAt : Function → BishopComplex → Set

open BishopComplexAnalyticFunctionLayer public

bishopComplexAnalyticCarrier :
  BishopComplexAnalyticFunctionLayer →
  Analytic.ComplexAnalyticCarrier
bishopComplexAnalyticCarrier functions = record
  { Analytic.ComplexAnalyticCarrier.Complex = BishopComplex
  ; Analytic.ComplexAnalyticCarrier.Real = Bishop.ℝ
  ; Analytic.ComplexAnalyticCarrier.zeroC = zeroC
  ; Analytic.ComplexAnalyticCarrier.oneC = oneC
  ; Analytic.ComplexAnalyticCarrier._+C_ = _+C_
  ; Analytic.ComplexAnalyticCarrier._*C_ = _*C_
  ; Analytic.ComplexAnalyticCarrier.negC = negC
  ; Analytic.ComplexAnalyticCarrier.conjC = conjC
  ; Analytic.ComplexAnalyticCarrier.realPart = re
  ; Analytic.ComplexAnalyticCarrier.imaginaryPart = im
  ; Analytic.ComplexAnalyticCarrier.Function = Function functions
  ; Analytic.ComplexAnalyticCarrier.apply = apply functions
  ; Analytic.ComplexAnalyticCarrier.Holomorphic = Holomorphic functions
  ; Analytic.ComplexAnalyticCarrier.Entire = Entire functions
  ; Analytic.ComplexAnalyticCarrier.Meromorphic = Meromorphic functions
  ; Analytic.ComplexAnalyticCarrier.SimplePoleAt = SimplePoleAt functions
  }

realCarrierIsBishop :
  ∀ functions →
  Analytic.ComplexAnalyticCarrier.Real
    (bishopComplexAnalyticCarrier functions)
  ≡ Bishop.ℝ
realCarrierIsBishop functions = refl

complexCarrierIsBishopPair :
  ∀ functions →
  Analytic.ComplexAnalyticCarrier.Complex
    (bishopComplexAnalyticCarrier functions)
  ≡ BishopComplex
complexCarrierIsBishopPair functions = refl

conjugatePreservesRealPart :
  ∀ point →
  re (conjC point) ≡ re point
conjugatePreservesRealPart (bishop-complex _ _) = refl

conjugateNegatesImaginaryPart :
  ∀ point →
  im (conjC point) ≡ Bishop.-_ (im point)
conjugateNegatesImaginaryPart (bishop-complex _ _) = refl

record CanonicalBishopComplexCarrierRealization
    (analytic : Analytic.AnalyticSubstrate)
    (functions : BishopComplexAnalyticFunctionLayer) : Set₁ where
  field
    carrierIdentity :
      Analytic.AnalyticSubstrate.carrier analytic
      ≡ bishopComplexAnalyticCarrier functions
    realizationReference : String

open CanonicalBishopComplexCarrierRealization public

record BishopComplexAnalyticCarrierBoundary : Set where
  constructor bishop-complex-analytic-carrier-boundary
  field
    realCarrierConcreteBishop : Bool
    complexCarrierConcretePair : Bool
    conjugationGeometryDefinitional : Bool
    analyticFunctionLayerSeparated : Bool
    wholeSelectedAnalyticCarrierIdentityStillRequired : Bool
    zetaLayerConstructedHere : Bool
    rhDerivedHere : Bool

open BishopComplexAnalyticCarrierBoundary public

canonicalBishopComplexAnalyticCarrierBoundary :
  BishopComplexAnalyticCarrierBoundary
canonicalBishopComplexAnalyticCarrierBoundary =
  bishop-complex-analytic-carrier-boundary
    true true true true true false false
