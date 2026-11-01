module DASHI.Interop.MultiscaleMDLCrossPollinationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.SSPTritCarrier
open import DASHI.Interop.MultiscaleMDLCrossPollination

------------------------------------------------------------------------
-- Exact support/sign witnesses.

negative-roundtrip : decodeSupportSign (factorSSPTrit sspNegOne) ≡ sspNegOne
negative-roundtrip = refl

zero-roundtrip : decodeSupportSign (factorSSPTrit sspZero) ≡ sspZero
zero-roundtrip = refl

positive-roundtrip : decodeSupportSign (factorSSPTrit sspPosOne) ≡ sspPosOne
positive-roundtrip = refl

inactive-sign-is-quotiented :
  decodeSupportSign (support-sign false true) ≡
  decodeSupportSign (support-sign false false)
inactive-sign-is-quotiented = refl

inactive-sign-canonicalises :
  canonicaliseSupportSign (support-sign false true) ≡ support-sign false false
inactive-sign-canonicalises = refl

------------------------------------------------------------------------
-- Claim-boundary witnesses.

shared-core-recorded : exactCoreShared canonicalCrossPollinationBoundary ≡ true
shared-core-recorded = refl

semantics-not-identified : laneSemanticsIdentical canonicalCrossPollinationBoundary ≡ false
semantics-not-identified = refl

authority-not-transferred :
  empiricalAuthorityTransfersAutomatically canonicalCrossPollinationBoundary ≡ false
authority-not-transferred = refl

mdl-action-not-identified :
  mdlEqualsPhysicalActionAutomatically canonicalCrossPollinationBoundary ≡ false
mdl-action-not-identified = refl

wave-unitarity-not-automatic :
  waveLiftMakesEveryKernelUnitary canonicalCrossPollinationBoundary ≡ false
wave-unitarity-not-automatic = refl

vorticity-closure-not-promoted :
  sparseTwistProxyProvesVorticityClosure canonicalCrossPollinationBoundary ≡ false
vorticity-closure-not-promoted = refl
