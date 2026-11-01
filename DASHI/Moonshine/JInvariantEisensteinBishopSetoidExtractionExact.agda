module DASHI.Moonshine.JInvariantEisensteinBishopSetoidExtractionExact where

------------------------------------------------------------------------
-- DIRECT VENDORED-BISHOP SETOID -> TARGET COMPLEX EXTRACTION
--
-- This is the carrier-correct route-B extraction compiler.
--
-- Source:
--   * vendored BishopReal.ℝ with BishopReal._≃_;
--   * DASHI.Analysis.BishopSetoidComplexExact;
--   * DASHI.Moonshine.JInvariantEisensteinBishopSetoidFiniteQSeriesExact.
--
-- Target:
--   the same abstract real/complex algebra used by the Lean route-B target.
--
-- No legacy ConstructedOrderedCompleteReal quotient appears in this module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Analysis.BishopSetoidComplexExact as BC
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidFiniteQSeriesExact as BQ
import DASHI.Moonshine.JInvariantEisensteinAgdaLeanExtractionExact as Target
import DASHI.Moonshine.JInvariantEisensteinAgdaLeanRealExtractionExact as TargetReal

------------------------------------------------------------------------
-- Primitive Bishop-real semantic extraction.
------------------------------------------------------------------------

record BishopSetoidRealExtraction
    (T : TargetReal.TargetRealTranscendental)
    (source : BC.BishopSetoidComplexTranscendentals) : Set₁ where
  field
    mapR : BishopReal.ℝ → TargetReal.CarrierR T

    respectsEquivalent :
      ∀ {x y} →
      BishopReal._≃_ x y →
      mapR x ≡ mapR y

    preservesZero :
      mapR BishopReal.0ℝ ≡ TargetReal.zeroR T

    preservesOne :
      mapR BishopReal.1ℝ ≡ TargetReal.oneR T

    preservesAdd :
      ∀ x y →
      mapR (BishopReal._+_ x y)
      ≡
      TargetReal.addR T (mapR x) (mapR y)

    preservesSub :
      ∀ x y →
      mapR (BishopReal._-_ x y)
      ≡
      TargetReal.subR T (mapR x) (mapR y)

    preservesMul :
      ∀ x y →
      mapR (BishopReal._*_ x y)
      ≡
      TargetReal.mulR T (mapR x) (mapR y)

    preservesNeg :
      ∀ x →
      mapR (BishopReal.- x)
      ≡
      TargetReal.negR T (mapR x)

    preservesExp :
      ∀ x →
      mapR (Exp.bishopExp x)
      ≡
      TargetReal.expR T (mapR x)

    preservesSin :
      ∀ x →
      mapR
        (Elementary.bishopSin
          (BC.dataSet source) x)
      ≡
      TargetReal.sinR T (mapR x)

    preservesCos :
      ∀ x →
      mapR
        (Elementary.bishopCos
          (BC.dataSet source) x)
      ≡
      TargetReal.cosR T (mapR x)

    preservesPi :
      mapR (BC.pi source)
      ≡
      TargetReal.piR T

open BishopSetoidRealExtraction public

------------------------------------------------------------------------
-- Componentwise complex extraction.
------------------------------------------------------------------------

mapComplex :
  ∀ {T source} →
  BishopSetoidRealExtraction T source →
  BC.BishopComplex →
  TargetReal.TargetComplexPair T
mapComplex E (BC.complex x y) =
  TargetReal.targetComplex (mapR E x) (mapR E y)

mapComplexEquivalent :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    {x y} →
  BC._≈C_ x y →
  mapComplex E x ≡ mapComplex E y
mapComplexEquivalent E equivalent
  rewrite respectsEquivalent E
            (BC.reEquivalent equivalent)
        | respectsEquivalent E
            (BC.imEquivalent equivalent)
  = refl

mapZero :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source) →
  mapComplex E BC.zeroC
  ≡ TargetReal.targetZeroC
mapZero E
  rewrite preservesZero E = refl

mapOne :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source) →
  mapComplex E BC.oneC
  ≡ TargetReal.targetOneC
mapOne E
  rewrite preservesOne E
        | preservesZero E = refl

mapI :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source) →
  mapComplex E BC.imaginaryUnit
  ≡ TargetReal.targetIC
mapI E
  rewrite preservesZero E
        | preservesOne E = refl

mapPi :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source) →
  mapComplex E (BC.piC source)
  ≡ TargetReal.targetPiC
mapPi E
  rewrite preservesPi E
        | preservesZero E = refl

mapAdd :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (x y : BC.BishopComplex) →
  mapComplex E (BC._+C_ x y)
  ≡
  TargetReal.targetAddC
    (mapComplex E x)
    (mapComplex E y)
mapAdd E (BC.complex xr xi) (BC.complex yr yi)
  rewrite preservesAdd E xr yr
        | preservesAdd E xi yi = refl

mapSub :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (x y : BC.BishopComplex) →
  mapComplex E (BC._-C_ x y)
  ≡
  TargetReal.targetSubC
    (mapComplex E x)
    (mapComplex E y)
mapSub E (BC.complex xr xi) (BC.complex yr yi)
  rewrite preservesSub E xr yr
        | preservesSub E xi yi = refl

mapMul :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (x y : BC.BishopComplex) →
  mapComplex E (BC._*C_ x y)
  ≡
  TargetReal.targetMulC
    (mapComplex E x)
    (mapComplex E y)
mapMul E (BC.complex xr xi) (BC.complex yr yi)
  rewrite preservesSub E
            (BishopReal._*_ xr yr)
            (BishopReal._*_ xi yi)
        | preservesMul E xr yr
        | preservesMul E xi yi
        | preservesAdd E
            (BishopReal._*_ xr yi)
            (BishopReal._*_ xi yr)
        | preservesMul E xr yi
        | preservesMul E xi yr = refl

mapExp :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (z : BC.BishopComplex) →
  mapComplex E (BC.expC source z)
  ≡
  TargetReal.targetExpC (mapComplex E z)
mapExp {source = source} E (BC.complex x y)
  rewrite preservesMul E
            (Exp.bishopExp x)
            (Elementary.bishopCos (BC.dataSet source) y)
        | preservesExp E x
        | preservesCos E y
        | preservesMul E
            (Exp.bishopExp x)
            (Elementary.bishopSin (BC.dataSet source) y)
        | preservesExp E x
        | preservesSin E y = refl

------------------------------------------------------------------------
-- Scaling and powers.
------------------------------------------------------------------------

mapScaleNat :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (n : Nat)
    (z : BC.BishopComplex) →
  mapComplex E (BC.scaleNatC n z)
  ≡
  Target.targetScaleNat
    (TargetReal.cartesianTargetComplexAlgebra T)
    n
    (mapComplex E z)
mapScaleNat E zero z
  rewrite mapZero E = refl
mapScaleNat E (suc n) z
  rewrite mapAdd E z (BC.scaleNatC n z)
        | mapScaleNat E n z = refl

mapPow :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (z : BC.BishopComplex)
    (n : Nat) →
  mapComplex E (BC.powC z n)
  ≡
  Target.targetPow
    (TargetReal.cartesianTargetComplexAlgebra T)
    (mapComplex E z)
    n
mapPow E z zero
  rewrite mapOne E = refl
mapPow E z (suc n)
  rewrite mapMul E z (BC.powC z n)
        | mapPow E z n = refl

------------------------------------------------------------------------
-- The actual Bishop q/E4/E6/discriminant recurrence transports.
------------------------------------------------------------------------

mapQ :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (tau : BC.BishopComplex) →
  mapComplex E (BQ.qOf source tau)
  ≡
  Target.targetQ
    (TargetReal.cartesianTargetComplexAlgebra T)
    (mapComplex E tau)
mapQ {T} {source} E tau
  rewrite mapExp E
            (BC._*C_
              (BC.scaleNatC 2
                (BC._*C_
                  BC.imaginaryUnit
                  (BC.piC source)))
              tau)
        | mapMul E
            (BC.scaleNatC 2
              (BC._*C_
                BC.imaginaryUnit
                (BC.piC source)))
            tau
        | mapScaleNat E 2
            (BC._*C_
              BC.imaginaryUnit
              (BC.piC source))
        | mapMul E
            BC.imaginaryUnit
            (BC.piC source)
        | mapI E
        | mapPi E = refl

mapE4 :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (kernel : BQ.DivisorPowerKernel)
    (terms : Nat)
    (tau : BC.BishopComplex) →
  mapComplex E (BQ.e4Truncated source kernel terms tau)
  ≡
  Target.targetE4Truncated
    (TargetReal.cartesianTargetComplexAlgebra T)
    kernel
    terms
    (Target.targetQ
      (TargetReal.cartesianTargetComplexAlgebra T)
      (mapComplex E tau))
mapE4 E kernel zero tau
  rewrite mapOne E = refl
mapE4 {T} {source} E kernel (suc n) tau
  rewrite mapAdd E
            (BQ.e4Truncated source kernel n tau)
            (BC.scaleNatC
              (240 * BQ.sigma3 kernel (suc n))
              (BC.powC (BQ.qOf source tau) (suc n)))
        | mapE4 E kernel n tau
        | mapScaleNat E
            (240 * BQ.sigma3 kernel (suc n))
            (BC.powC (BQ.qOf source tau) (suc n))
        | mapPow E
            (BQ.qOf source tau)
            (suc n)
        | mapQ E tau = refl

mapE6 :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (kernel : BQ.DivisorPowerKernel)
    (terms : Nat)
    (tau : BC.BishopComplex) →
  mapComplex E (BQ.e6Truncated source kernel terms tau)
  ≡
  Target.targetE6Truncated
    (TargetReal.cartesianTargetComplexAlgebra T)
    kernel
    terms
    (Target.targetQ
      (TargetReal.cartesianTargetComplexAlgebra T)
      (mapComplex E tau))
mapE6 E kernel zero tau
  rewrite mapOne E = refl
mapE6 {T} {source} E kernel (suc n) tau
  rewrite mapSub E
            (BQ.e6Truncated source kernel n tau)
            (BC.scaleNatC
              (504 * BQ.sigma5 kernel (suc n))
              (BC.powC (BQ.qOf source tau) (suc n)))
        | mapE6 E kernel n tau
        | mapScaleNat E
            (504 * BQ.sigma5 kernel (suc n))
            (BC.powC (BQ.qOf source tau) (suc n))
        | mapPow E
            (BQ.qOf source tau)
            (suc n)
        | mapQ E tau = refl

mapSquare :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (z : BC.BishopComplex) →
  mapComplex E (BQ.squareC z)
  ≡
  Target.targetSquare
    (TargetReal.cartesianTargetComplexAlgebra T)
    (mapComplex E z)
mapSquare E z =
  mapMul E z z

mapCube :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (z : BC.BishopComplex) →
  mapComplex E (BQ.cubeC z)
  ≡
  Target.targetCube
    (TargetReal.cartesianTargetComplexAlgebra T)
    (mapComplex E z)
mapCube E z
  rewrite mapMul E (BQ.squareC z) z
        | mapSquare E z = refl

mapDiscriminantNumerator :
  ∀ {T source}
    (E : BishopSetoidRealExtraction T source)
    (kernel : BQ.DivisorPowerKernel)
    (terms : Nat)
    (tau : BC.BishopComplex) →
  mapComplex E
    (BQ.discriminantNumeratorTruncated
      source kernel terms tau)
  ≡
  Target.targetDiscriminantNumeratorTruncated
    (TargetReal.cartesianTargetComplexAlgebra T)
    kernel
    terms
    (Target.targetQ
      (TargetReal.cartesianTargetComplexAlgebra T)
      (mapComplex E tau))
mapDiscriminantNumerator E kernel terms tau
  rewrite mapSub E
            (BQ.cubeC (BQ.e4Truncated _ kernel terms tau))
            (BQ.squareC (BQ.e6Truncated _ kernel terms tau))
        | mapCube E (BQ.e4Truncated _ kernel terms tau)
        | mapSquare E (BQ.e6Truncated _ kernel terms tau)
        | mapE4 E kernel terms tau
        | mapE6 E kernel terms tau = refl

------------------------------------------------------------------------
-- Route-B boundary.
------------------------------------------------------------------------

record BishopSetoidExtractionBoundary : Set where
  constructor bishop-setoid-extraction-boundary
  field
    sourceIsVendoredBishopSetoid : Bool
    legacyPropositionalQuotientUsed : Bool
    setoidEquivalenceRespected : Bool
    componentwiseComplexTransportDerived : Bool
    actualBishopQTransportDerived : Bool
    actualBishopE4TransportDerived : Bool
    actualBishopE6TransportDerived : Bool
    actualBishopDiscriminantTransportDerived : Bool

    concreteBishopToLeanRealEvaluatorInhabitedInAgda : Bool
    bishopExpClassicalSemanticWeld : Bool
    bishopSinClassicalSemanticWeld : Bool
    bishopCosClassicalSemanticWeld : Bool
    bishopPiClassicalSemanticWeld : Bool

canonicalBishopSetoidExtractionBoundary :
  BishopSetoidExtractionBoundary
canonicalBishopSetoidExtractionBoundary =
  bishop-setoid-extraction-boundary
    true false true true true true true true
    false false false false false
