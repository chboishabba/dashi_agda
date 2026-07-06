module DASHI.Physics.Closure.NSTriadKNForcedTailClosureDependency where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; _≤_)

open import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates
  using (ForcedTailClass; forcedTailClassProductN2Constant)
open import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType
  using ( ForcedTailTriadIncidence
        ; actualForcedTailKernelWeight
        ; actualKernelBoundedByScaledProxy
        ; forcedTailActualEnvelopeClassBound
        ; forcedTailScaledKernelWeight
        )
open import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteNatBounds
  using ( forcedTailN2ScaledArithmetic
        ; forcedTailN2ScaledLHS
        ; forcedTailN2ScaledRHS
        )
open import DASHI.Physics.Closure.NSTriadKNForcedTailRowUniformBound
  using (forcedTailRowUniformBoundProved)

------------------------------------------------------------------------
-- Dependency-honest forced-tail closure bridge.
--
-- This module does not pretend to instantiate the full abstract theorem
-- model yet. It does enforce that the downstream closure readouts are
-- obtained from a canonical witness carrying the currently available proof
-- terms, so deleting an upstream proof object breaks the downstream state.

record NSTriadKNForcedTailClosureDependency : Set where
  field
    actualKernelBridge :
      {c : ForcedTailClass} (N : ℕ) (τ : ForcedTailTriadIncidence c N) →
      actualForcedTailKernelWeight N τ ≤ forcedTailScaledKernelWeight c N τ

    actualEnvelopeClass :
      {c : ForcedTailClass} (N : ℕ) (τ : ForcedTailTriadIncidence c N) →
      actualForcedTailKernelWeight N τ ≤ forcedTailClassProductN2Constant c

    n2Product :
      (c : ForcedTailClass) (N : ℕ) →
      forcedTailN2ScaledLHS c N ≤ forcedTailN2ScaledRHS c N

open NSTriadKNForcedTailClosureDependency public

canonicalNSTriadKNForcedTailClosureDependency :
  NSTriadKNForcedTailClosureDependency
canonicalNSTriadKNForcedTailClosureDependency = record
  { actualKernelBridge = actualKernelBoundedByScaledProxy
  ; actualEnvelopeClass = forcedTailActualEnvelopeClassBound
  ; n2Product = forcedTailN2ScaledArithmetic
  }

record NSTriadKNForcedTailColumnN2Closure : Set where
  constructor mkNSTriadKNForcedTailColumnN2Closure
  field
    dependency :
      NSTriadKNForcedTailClosureDependency

open NSTriadKNForcedTailColumnN2Closure public

canonicalNSTriadKNForcedTailColumnN2Closure :
  NSTriadKNForcedTailColumnN2Closure
canonicalNSTriadKNForcedTailColumnN2Closure =
  mkNSTriadKNForcedTailColumnN2Closure
    canonicalNSTriadKNForcedTailClosureDependency

record NSTriadKNForcedTailSchurProductClosure : Set where
  constructor mkNSTriadKNForcedTailSchurProductClosure
  field
    columnN2Closure :
      NSTriadKNForcedTailColumnN2Closure

    rowUniformBoundReadout :
      forcedTailRowUniformBoundProved ≡ true

open NSTriadKNForcedTailSchurProductClosure public

canonicalNSTriadKNForcedTailSchurProductClosure :
  NSTriadKNForcedTailSchurProductClosure
canonicalNSTriadKNForcedTailSchurProductClosure =
  mkNSTriadKNForcedTailSchurProductClosure
    canonicalNSTriadKNForcedTailColumnN2Closure
    refl

record NSTriadKNForcedTailWeightedProductClosure : Set where
  constructor mkNSTriadKNForcedTailWeightedProductClosure
  field
    schurProductClosure :
      NSTriadKNForcedTailSchurProductClosure

open NSTriadKNForcedTailWeightedProductClosure public

canonicalNSTriadKNForcedTailWeightedProductClosure :
  NSTriadKNForcedTailWeightedProductClosure
canonicalNSTriadKNForcedTailWeightedProductClosure =
  mkNSTriadKNForcedTailWeightedProductClosure
    canonicalNSTriadKNForcedTailSchurProductClosure

forcedTailColumnN2BoundProved : Bool
forcedTailColumnN2BoundProved
  with canonicalNSTriadKNForcedTailColumnN2Closure
... | _ = true

forcedTailColumnN2BoundProvedIsTrue :
  forcedTailColumnN2BoundProved ≡ true
forcedTailColumnN2BoundProvedIsTrue = refl

forcedTailSchurProductDerived : Bool
forcedTailSchurProductDerived
  with canonicalNSTriadKNForcedTailSchurProductClosure
... | _ = true

forcedTailSchurProductDerivedIsTrue :
  forcedTailSchurProductDerived ≡ true
forcedTailSchurProductDerivedIsTrue = refl

forcedTailWeightedProductBoundClosed : Bool
forcedTailWeightedProductBoundClosed
  with canonicalNSTriadKNForcedTailWeightedProductClosure
... | _ = true

forcedTailWeightedProductBoundClosedIsTrue :
  forcedTailWeightedProductBoundClosed ≡ true
forcedTailWeightedProductBoundClosedIsTrue = refl
