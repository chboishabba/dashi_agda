module DASHI.Foundations.SSPBase369Bridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high ; fromTriIndex ; tri-index
  ; HexTruth ; fromHexIndex ; hex-index
  ; NonaryTruth ; fromNonaryIndex ; nonary-index
  )
open import DASHI.Core.Prelude using (_×_; _,_)
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface
  ; surfaceAsVec15
  ; canonicalZeroFifteenSSPSurface
  ; canonicalExampleFifteenSSPSurface
  ; canonicalPositiveFifteenSSPSurface
  )
open import DASHI.Foundations.HexTruthPolarityFactor using
  ( Polarity
  ; hexTruthToFactor
  )
open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne ; sspZero ; sspPosOne
  ; toTriTruth
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

tritNat : SSPTrit → Nat
tritNat sspNegOne = 0
tritNat sspZero = 1
tritNat sspPosOne = 2

sumVec15Nat : Vec15 Nat → Nat
sumVec15Nat (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  a2 + a3 + a5 + a7 + a11 + a13 + a17 + a19 + a23 + a29 + a31 + a41 + a47 + a59 + a71

countPositiveTrits : Vec15 SSPTrit → Nat
countPositiveTrits (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  positiveNat a2 + positiveNat a3 + positiveNat a5 + positiveNat a7 + positiveNat a11 +
  positiveNat a13 + positiveNat a17 + positiveNat a19 + positiveNat a23 + positiveNat a29 +
  positiveNat a31 + positiveNat a41 + positiveNat a47 + positiveNat a59 + positiveNat a71
  where
    positiveNat : SSPTrit → Nat
    positiveNat sspPosOne = 1
    positiveNat _ = 0

countNegativeTrits : Vec15 SSPTrit → Nat
countNegativeTrits (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  negativeNat a2 + negativeNat a3 + negativeNat a5 + negativeNat a7 + negativeNat a11 +
  negativeNat a13 + negativeNat a17 + negativeNat a19 + negativeNat a23 + negativeNat a29 +
  negativeNat a31 + negativeNat a41 + negativeNat a47 + negativeNat a59 + negativeNat a71
  where
    negativeNat : SSPTrit → Nat
    negativeNat sspNegOne = 1
    negativeNat _ = 0

surfaceTriTruth : FifteenSSPSurface → TriTruth
surfaceTriTruth s =
  fromTriIndex
    (sumVec15Nat
      (mapTritsToNat (surfaceAsVec15 s)))
  where
    mapTritsToNat : Vec15 SSPTrit → Vec15 Nat
    mapTritsToNat (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
      mkVec15
        (tritNat a2) (tritNat a3) (tritNat a5) (tritNat a7) (tritNat a11)
        (tritNat a13) (tritNat a17) (tritNat a19) (tritNat a23) (tritNat a29)
        (tritNat a31) (tritNat a41) (tritNat a47) (tritNat a59) (tritNat a71)

surfaceHexTruth : FifteenSSPSurface → HexTruth
surfaceHexTruth s =
  fromHexIndex
    (countPositiveTrits (surfaceAsVec15 s) + countNegativeTrits (surfaceAsVec15 s))

surfaceNonaryTruth : FifteenSSPSurface → NonaryTruth
surfaceNonaryTruth s =
  fromNonaryIndex
    (sumVec15Nat
      (mapTriIndices (surfaceAsVec15 s)))
  where
    mapTriIndices : Vec15 SSPTrit → Vec15 Nat
    mapTriIndices (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
      mkVec15
        (tri-index (toTriTruth a2)) (tri-index (toTriTruth a3)) (tri-index (toTriTruth a5))
        (tri-index (toTriTruth a7)) (tri-index (toTriTruth a11)) (tri-index (toTriTruth a13))
        (tri-index (toTriTruth a17)) (tri-index (toTriTruth a19)) (tri-index (toTriTruth a23))
        (tri-index (toTriTruth a29)) (tri-index (toTriTruth a31)) (tri-index (toTriTruth a41))
        (tri-index (toTriTruth a47)) (tri-index (toTriTruth a59)) (tri-index (toTriTruth a71))

surfacePolarity : FifteenSSPSurface → Polarity
surfacePolarity s = proj₂ (hexTruthToFactor (surfaceHexTruth s))
  where
    proj₂ : ∀ {A B : Set} → A × B → B
    proj₂ (_ , b) = b

record SSPBase369BridgeReceipt : Set where
  constructor mkSSPBase369BridgeReceipt
  field
    sourceSurface : FifteenSSPSurface
    triPhase : TriTruth
    hexPhase : HexTruth
    nonaryPhase : NonaryTruth
    triPhaseMatches : triPhase ≡ surfaceTriTruth sourceSurface
    hexPhaseMatches : hexPhase ≡ surfaceHexTruth sourceSurface
    nonaryPhaseMatches : nonaryPhase ≡ surfaceNonaryTruth sourceSurface

open SSPBase369BridgeReceipt public

canonicalZeroBridgeReceipt : SSPBase369BridgeReceipt
canonicalZeroBridgeReceipt =
  mkSSPBase369BridgeReceipt
    canonicalZeroFifteenSSPSurface
    (surfaceTriTruth canonicalZeroFifteenSSPSurface)
    (surfaceHexTruth canonicalZeroFifteenSSPSurface)
    (surfaceNonaryTruth canonicalZeroFifteenSSPSurface)
    refl refl refl

canonicalExampleBridgeReceipt : SSPBase369BridgeReceipt
canonicalExampleBridgeReceipt =
  mkSSPBase369BridgeReceipt
    canonicalExampleFifteenSSPSurface
    (surfaceTriTruth canonicalExampleFifteenSSPSurface)
    (surfaceHexTruth canonicalExampleFifteenSSPSurface)
    (surfaceNonaryTruth canonicalExampleFifteenSSPSurface)
    refl refl refl

canonicalPositiveBridgeReceipt : SSPBase369BridgeReceipt
canonicalPositiveBridgeReceipt =
  mkSSPBase369BridgeReceipt
    canonicalPositiveFifteenSSPSurface
    (surfaceTriTruth canonicalPositiveFifteenSSPSurface)
    (surfaceHexTruth canonicalPositiveFifteenSSPSurface)
    (surfaceNonaryTruth canonicalPositiveFifteenSSPSurface)
    refl refl refl
