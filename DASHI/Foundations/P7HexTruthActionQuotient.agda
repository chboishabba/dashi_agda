module DASHI.Foundations.P7HexTruthActionQuotient where

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

open import DASHI.Foundations.Base369MobiusTransport using
  ( mobiusTransport )
open import DASHI.Foundations.HexTruthPolarityFactor using
  ( Polarity
  ; flipPolarity
  ; hexFactorToTruth
  ; hexTruthToFactor
  )
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( actOnHexFactor
  ; actOnHexTruth
  )
open import DASHI.Foundations.SSPPrimeLaneUnitGroup using
  ( P7UnitClass
  ; p7-unit0
  ; p7-unit1
  ; p7-unit3
  ; p7UnitGenerator
  ; p7UnitIdentity
  ; p7UnitMobiusElement
  ; toStep
  )
open import DASHI.Foundations.SSPPrimeLane369Signature as Signature using
  ( hexResidue )
open import DASHI.Foundations.SSPPrimeLane369Refinement using ()
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( p7SSPPrimeLane369PhaseBridge
  ; residueSignature
  )
open import DASHI.TrackedPrimes using (p7)

actOnP7HexTruth : P7UnitClass → HexTruth → HexTruth
actOnP7HexTruth q h = actOnHexTruth p7 (toStep q) h

actOnP7HexFactor : P7UnitClass → HexTruth → TriTruth × Polarity
actOnP7HexFactor q h = actOnHexFactor p7 (toStep q) h

p7ResidueHexTruth : HexTruth
p7ResidueHexTruth = Signature.hexResidue (Phase.residueSignature p7SSPPrimeLane369PhaseBridge)

p7ResidueHexFactor : TriTruth × Polarity
p7ResidueHexFactor = hexTruthToFactor p7ResidueHexTruth

identityActsOnP7HexTruth :
  (h : HexTruth) →
  actOnP7HexTruth p7UnitIdentity h ≡ h
identityActsOnP7HexTruth hex-0 = refl
identityActsOnP7HexTruth hex-1 = refl
identityActsOnP7HexTruth hex-2 = refl
identityActsOnP7HexTruth hex-3 = refl
identityActsOnP7HexTruth hex-4 = refl
identityActsOnP7HexTruth hex-5 = refl

generatorActsOnP7ResidueHexTruth :
  actOnP7HexTruth p7UnitGenerator p7ResidueHexTruth ≡ hex-5
generatorActsOnP7ResidueHexTruth = refl

generatorActsOnP7ResidueHexFactor :
  actOnP7HexFactor p7UnitGenerator p7ResidueHexTruth
  ≡ hexTruthToFactor hex-5
generatorActsOnP7ResidueHexFactor = refl

mobiusActsAsMobiusTransport :
  (h : HexTruth) →
  actOnP7HexTruth p7UnitMobiusElement h ≡ mobiusTransport h
mobiusActsAsMobiusTransport hex-0 = refl
mobiusActsAsMobiusTransport hex-1 = refl
mobiusActsAsMobiusTransport hex-2 = refl
mobiusActsAsMobiusTransport hex-3 = refl
mobiusActsAsMobiusTransport hex-4 = refl
mobiusActsAsMobiusTransport hex-5 = refl

mobiusActsOnP7HexFactor :
  (h : HexTruth) →
  actOnP7HexFactor p7UnitMobiusElement h
  ≡
  ( proj₁ (hexTruthToFactor h)
  , flipPolarity (proj₂ (hexTruthToFactor h))
  )
mobiusActsOnP7HexFactor hex-0 = refl
mobiusActsOnP7HexFactor hex-1 = refl
mobiusActsOnP7HexFactor hex-2 = refl
mobiusActsOnP7HexFactor hex-3 = refl
mobiusActsOnP7HexFactor hex-4 = refl
mobiusActsOnP7HexFactor hex-5 = refl

mobiusSquaredActsAsIdentity :
  (h : HexTruth) →
  actOnP7HexTruth p7UnitMobiusElement
    (actOnP7HexTruth p7UnitMobiusElement h)
  ≡ h
mobiusSquaredActsAsIdentity hex-0 = refl
mobiusSquaredActsAsIdentity hex-1 = refl
mobiusSquaredActsAsIdentity hex-2 = refl
mobiusSquaredActsAsIdentity hex-3 = refl
mobiusSquaredActsAsIdentity hex-4 = refl
mobiusSquaredActsAsIdentity hex-5 = refl
