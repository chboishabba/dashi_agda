module DASHI.Foundations.SSPPrimeLane369BridgeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Core.SuperSSP369Field using
  ( rootField
  ; depth3Field
  ; focusPrimeLane
  )
open import DASHI.Foundations.SSPBase369Bridge using
  ( canonicalExampleBridgeReceipt
  ; canonicalZeroBridgeReceipt
  ; triPhase
  )
open import DASHI.Foundations.SSPPrimeLane369Refinement using
  ( canonicalRootLane369Refinement
  ; canonicalThreeSixNineLane369Refinement
  ; refinementDepth
  )
open import DASHI.Foundations.SSPPrimeLane369Signature using
  ( p7Prime369Signature
  ; p11Prime369Signature
  ; p71Prime369Signature
  )
open import DASHI.Foundations.SSPPrimeLaneSymmetryProfile using
  ( p7PrimeLaneSymmetryProfile
  ; p11PrimeLaneSymmetryProfile
  ; unitOrder
  )
open import DASHI.TrackedPrimes using (p3; p7)

record SSPPrimeLane369BridgeRegression : Set where
  constructor mkSSPPrimeLane369BridgeRegression
  field
    p7Signature : DASHI.Foundations.SSPPrimeLane369Signature.Prime369Signature
    p11Signature : DASHI.Foundations.SSPPrimeLane369Signature.Prime369Signature
    p71Signature : DASHI.Foundations.SSPPrimeLane369Signature.Prime369Signature
    p7UnitOrder : unitOrder p7PrimeLaneSymmetryProfile ≡ 6
    p11UnitOrder : unitOrder p11PrimeLaneSymmetryProfile ≡ 10
    rootDepth : refinementDepth canonicalRootLane369Refinement ≡ zero
    depth3 : refinementDepth canonicalThreeSixNineLane369Refinement ≡ suc (suc (suc zero))
    rootFieldPrime : focusPrimeLane rootField ≡ p3
    depth3FieldPrime : focusPrimeLane depth3Field ≡ p7

open SSPPrimeLane369BridgeRegression public

canonicalSSPPrimeLane369BridgeRegression : SSPPrimeLane369BridgeRegression
canonicalSSPPrimeLane369BridgeRegression =
  mkSSPPrimeLane369BridgeRegression
    p7Prime369Signature
    p11Prime369Signature
    p71Prime369Signature
    refl
    refl
    refl
    refl
    refl
    refl

canonicalZeroBridgeTriPhase :
  triPhase canonicalZeroBridgeReceipt ≡ triPhase canonicalZeroBridgeReceipt
canonicalZeroBridgeTriPhase = refl

canonicalExampleBridgeTriPhase :
  triPhase canonicalExampleBridgeReceipt ≡ triPhase canonicalExampleBridgeReceipt
canonicalExampleBridgeTriPhase = refl
