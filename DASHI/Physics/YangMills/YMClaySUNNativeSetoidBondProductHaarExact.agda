{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNNativeSetoidBondProductHaarExact where

------------------------------------------------------------------------
-- R443-H: ORIGINAL SUN BOND FIELDS / FINITE VECTORS AT SETOID PRECISION.
--
-- Original BondField = PositiveBond -> Link is a FUNCTION TYPE. The old
-- SUNNativeBondProductCodec asks for equality of those whole functions.
-- This alternate *same original carrier* codec uses pointwise equality,
-- the exact congruence proved for physical Wilson/Gibbs observables.
--
-- No arbitrary function extensionality, no fake finite gauge fields:
-- the integral is still the n-link product integral of the decoded
-- original periodic full-matrix bond fields. C3 is a finite permutation
-- witness. The codec's existence, actual link count and measurable
-- one-link Haar source are still physical mathematical obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNNativeWilsonBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as ProductC3
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

record SUNNativeSetoidBondCodec
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (linkCount : Nat) : Set₁ where
  field
    encode :
      Native.SUNSideFourLinks N theory →
      Vec (SUN.SUNMatrixElement theory) linkCount
    decode :
      Vec (SUN.SUNMatrixElement theory) linkCount →
      Native.SUNSideFourLinks N theory

    encodeDecode : ∀ vector → encode (decode vector) ≡ vector

    -- Function extensionality is deliberately NOT required.
    decodeEncodeAt : ∀ links bond →
      decode (encode links) bond ≡ links bond

    c3Permutation : Product.LinkPermutation linkCount
    c3DecodeAt : ∀ vector bond →
      Weld.nativeForwardC3Bonds (decode vector) bond
      ≡ decode (Product.permuteLinks c3Permutation vector) bond

open SUNNativeSetoidBondCodec public

nativeSetoidProductHaar :
  ∀ {Matrix Complex : Set} {N n : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex} →
  Product.OneLinkProductHaar (SUN.SUNMatrixElement theory) →
  SUNNativeSetoidBondCodec theory n →
  (Native.SUNSideFourLinks N theory → ℝ) → ℝ
nativeSetoidProductHaar source codec observable =
  Product.productIntegral source
    (λ vector → observable (decode codec vector))

record NativeBondPointwiseObservable
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (observable : Native.SUNSideFourLinks N theory → ℝ) : Set where
  field
    congruentAt : ∀ left right →
      Pointwise.NativeBondPointwise theory left right →
      observable left ≡ observable right

open NativeBondPointwiseObservable public

-- The native whole-function equality formerly requested by
-- SUNNativeBondProductCodec.c3Decode is replaced by a selected observable
-- congruence proof. The finite product Haar permutation itself is unchanged.
nativeSetoidHaarC3Invariant :
  ∀ {Matrix Complex : Set} {N n : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (source : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (codec : SUNNativeSetoidBondCodec theory n)
    (observable : Native.SUNSideFourLinks N theory → ℝ) →
    NativeBondPointwiseObservable theory observable →
  nativeSetoidProductHaar source codec
    (λ links → observable (Weld.nativeForwardC3Bonds links))
  ≡ nativeSetoidProductHaar source codec observable
nativeSetoidHaarC3Invariant source codec observable extensional =
  trans
    (ProductC3.productIntegralCongruent source _ _
      (λ vector →
        congruentAt extensional _ _
          (c3DecodeAt codec vector)))
    (Product.productHaarPermutationInvariant source
      (c3Permutation codec)
      (λ vector → observable (decode codec vector)))

nativeSUNWilsonActionRespectsBondPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (beta : ℝ) →
  NativeBondPointwiseObservable theory
    (Gibbs.nativeSUNWilsonAction theory traceData beta)
nativeSUNWilsonActionRespectsBondPointwise theory traceData beta =
  record
    { congruentAt =
        Pointwise.nativeSUNWilsonActionPointwise
          theory traceData beta
    }

nativeSUNGibbsDensityRespectsBondPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ) →
  NativeBondPointwiseObservable theory
    (Gibbs.nativeSUNWilsonGibbsDensity
      theory traceData exponential beta)
nativeSUNGibbsDensityRespectsBondPointwise theory traceData exponential beta =
  record
    { congruentAt =
        Pointwise.nativeSUNGibbsDensityPointwise
          theory traceData exponential beta
    }

nativeSUNPhysicalGibbsSetoidHaarC3 :
  ∀ {Matrix Complex : Set} {N n : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (codec : SUNNativeSetoidBondCodec theory n) →
  nativeSetoidProductHaar source codec
    (λ links → Gibbs.nativeSUNWilsonGibbsDensity
      theory traceData exponential beta
      (Weld.nativeForwardC3Bonds links))
  ≡ nativeSetoidProductHaar source codec
      (Gibbs.nativeSUNWilsonGibbsDensity
        theory traceData exponential beta)
nativeSUNPhysicalGibbsSetoidHaarC3
    theory traceData exponential beta source codec =
  nativeSetoidHaarC3Invariant source codec _
    (nativeSUNGibbsDensityRespectsBondPointwise
      theory traceData exponential beta)
