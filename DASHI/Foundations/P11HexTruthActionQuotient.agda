module DASHI.Foundations.P11HexTruthActionQuotient where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  )

open import DASHI.Foundations.HexTruthPolarityFactor using
  ( Polarity
  ; flipPolarity
  ; hexTruthToFactor
  )
open import DASHI.Foundations.P11UnitGroupC10Witness using
  ( P11UnitClass
  ; p11-unit0
  ; p11-unit5
  ; p11UnitGenerator
  ; p11UnitHalfTurnElement
  ; toStep
  )
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( actOnHexFactor
  ; actOnHexTruth
  ; rotateTriTruthBy
  )
open import DASHI.Foundations.SSPPrimeLane369Signature as Signature using
  ( hexResidue )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( p11SSPPrimeLane369PhaseBridge
  ; residueSignature
  )
open import DASHI.TrackedPrimes using (p11)

actOnP11HexTruth : P11UnitClass → HexTruth → HexTruth
actOnP11HexTruth q h = actOnHexTruth p11 (toStep q) h

actOnP11HexFactor : P11UnitClass → HexTruth → TriTruth × Polarity
actOnP11HexFactor q h = actOnHexFactor p11 (toStep q) h

p11ResidueHexTruth : HexTruth
p11ResidueHexTruth =
  Signature.hexResidue (Phase.residueSignature p11SSPPrimeLane369PhaseBridge)

p11ResidueHexFactor : TriTruth × Polarity
p11ResidueHexFactor = hexTruthToFactor p11ResidueHexTruth

identityActsOnP11HexTruth :
  (h : HexTruth) →
  actOnP11HexTruth p11-unit0 h ≡ h
identityActsOnP11HexTruth hex-0 = refl
identityActsOnP11HexTruth hex-1 = refl
identityActsOnP11HexTruth hex-2 = refl
identityActsOnP11HexTruth hex-3 = refl
identityActsOnP11HexTruth hex-4 = refl
identityActsOnP11HexTruth hex-5 = refl

generatorActsOnP11ResidueHexTruth :
  actOnP11HexTruth p11UnitGenerator p11ResidueHexTruth ≡ hex-0
generatorActsOnP11ResidueHexTruth = refl

halfTurnActsOnP11HexFactor :
  (h : HexTruth) →
  actOnP11HexFactor p11UnitHalfTurnElement h
  ≡
  ( Action.rotateTriTruthBy 2 (proj₁ (hexTruthToFactor h))
  , flipPolarity (proj₂ (hexTruthToFactor h))
  )
halfTurnActsOnP11HexFactor hex-0 = refl
halfTurnActsOnP11HexFactor hex-1 = refl
halfTurnActsOnP11HexFactor hex-2 = refl
halfTurnActsOnP11HexFactor hex-3 = refl
halfTurnActsOnP11HexFactor hex-4 = refl
halfTurnActsOnP11HexFactor hex-5 = refl

halfTurnActsOnP11ResidueHexTruth :
  actOnP11HexTruth p11UnitHalfTurnElement p11ResidueHexTruth ≡ hex-1
halfTurnActsOnP11ResidueHexTruth = refl

halfTurnDoubleActionOnHex0 :
  actOnP11HexTruth p11UnitHalfTurnElement
    (actOnP11HexTruth p11UnitHalfTurnElement hex-0)
  ≡ hex-1
halfTurnDoubleActionOnHex0 = refl

halfTurnDoubleActionOnResidue :
  actOnP11HexTruth p11UnitHalfTurnElement
    (actOnP11HexTruth p11UnitHalfTurnElement p11ResidueHexTruth)
  ≡ hex-3
halfTurnDoubleActionOnResidue = refl
