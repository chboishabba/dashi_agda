module DASHI.Foundations.P13HexTruthActionQuotient where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; tri-mid
  ; tri-high
  )

open import DASHI.Foundations.Base369MobiusTransport using (positive)
open import DASHI.Foundations.HexTruthPolarityFactor using
  ( Polarity
  ; hexTruthToFactor
  )
open import DASHI.Foundations.SSPPrimeLane369Signature as Signature using
  ( hexResidue )
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( SSPPrimeLaneUnitActionProfile
  ; UnitActionStep
  ; actOnHexFactor
  ; actOnHexTruth
  ; canonicalGeneratorStep
  ; actedHexFactor
  ; actedHexTruth
  ; flipsPolarity
  ; normalizedStep
  ; primeLaneUnitActionProfile
  ; triadicStep
  )
open import DASHI.Physics.Closure.SSPPrimeLane369ActionPhaseBridge as ActionPhase using
  ( SSPPrimeLane369ActionPhaseBridge
  ; polarityFlipBit
  ; primeLane369ActionPhaseBridge
  ; sourceHexFactor
  ; sourceHexTruth
  ; transportedHexFactor
  ; transportedHexTruth
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( SSPPrimeLane369PhaseBridge
  ; primeIdentityStage
  ; primeLane369PhaseBridge
  ; residueSignature
  ; unitOrder
  ; unitOrderStage
  )
open import DASHI.TrackedPrimes using (p13)
open import DASHI.Foundations.StageAtlasZeroToEleven using (atlas-0; atlas-1)

actOnP13HexTruth : UnitActionStep → HexTruth → HexTruth
actOnP13HexTruth step h = actOnHexTruth p13 step h

actOnP13HexFactor : UnitActionStep → HexTruth → TriTruth × Polarity
actOnP13HexFactor step h = actOnHexFactor p13 step h

p13PhaseBridge : SSPPrimeLane369PhaseBridge
p13PhaseBridge = primeLane369PhaseBridge p13

p13ResidueHexTruth : HexTruth
p13ResidueHexTruth = Signature.hexResidue (residueSignature p13PhaseBridge)

p13ResidueHexFactor : TriTruth × Polarity
p13ResidueHexFactor = hexTruthToFactor p13ResidueHexTruth

p13GeneratorUnitActionProfile : SSPPrimeLaneUnitActionProfile
p13GeneratorUnitActionProfile = primeLaneUnitActionProfile p13 canonicalGeneratorStep

p13ActionPhaseBridge : SSPPrimeLane369ActionPhaseBridge
p13ActionPhaseBridge = primeLane369ActionPhaseBridge p13 canonicalGeneratorStep

p13HalfTurnStep : UnitActionStep
p13HalfTurnStep = suc (suc (suc (suc (suc (suc zero)))))

identityActsOnP13HexTruth :
  (h : HexTruth) →
  actOnP13HexTruth zero h ≡ h
identityActsOnP13HexTruth hex-0 = refl
identityActsOnP13HexTruth hex-1 = refl
identityActsOnP13HexTruth hex-2 = refl
identityActsOnP13HexTruth hex-3 = refl
identityActsOnP13HexTruth hex-4 = refl
identityActsOnP13HexTruth hex-5 = refl

p13PrimeIdentityStageIsAtlas1 :
  primeIdentityStage p13PhaseBridge ≡ atlas-1
p13PrimeIdentityStageIsAtlas1 = refl

p13UnitOrderIs12 :
  unitOrder p13PhaseBridge ≡ 12
p13UnitOrderIs12 = refl

p13UnitOrderStageIsAtlas0 :
  unitOrderStage p13PhaseBridge ≡ atlas-0
p13UnitOrderStageIsAtlas0 = refl

p13ResidueHexTruthIsHex1 :
  p13ResidueHexTruth ≡ hex-1
p13ResidueHexTruthIsHex1 = refl

p13ResidueHexFactorIsMidPositive :
  p13ResidueHexFactor ≡ (tri-mid , positive)
p13ResidueHexFactorIsMidPositive = refl

generatorActsOnP13ResidueHexTruth :
  actOnP13HexTruth canonicalGeneratorStep p13ResidueHexTruth ≡ hex-5
generatorActsOnP13ResidueHexTruth = refl

generatorActsOnP13ResidueHexFactor :
  actOnP13HexFactor canonicalGeneratorStep p13ResidueHexTruth
  ≡ hexTruthToFactor hex-5
generatorActsOnP13ResidueHexFactor = refl

halfTurnActsOnP13ResidueHexTruth :
  actOnP13HexTruth p13HalfTurnStep p13ResidueHexTruth ≡ hex-1
halfTurnActsOnP13ResidueHexTruth = refl

halfTurnActsOnP13ResidueHexFactor :
  actOnP13HexFactor p13HalfTurnStep p13ResidueHexTruth
  ≡ hexTruthToFactor hex-1
halfTurnActsOnP13ResidueHexFactor = refl

p13GeneratorActionPhaseBridgeNormalizedStepIs1 :
  ActionPhase.normalizedStep p13ActionPhaseBridge ≡ 1
p13GeneratorActionPhaseBridgeNormalizedStepIs1 = refl

p13GeneratorActionPhaseBridgeTriadicStepIs1 :
  ActionPhase.triadicStep p13ActionPhaseBridge ≡ 1
p13GeneratorActionPhaseBridgeTriadicStepIs1 = refl

p13GeneratorActionPhaseBridgeFlipsPolarity :
  ActionPhase.polarityFlipBit p13ActionPhaseBridge ≡ true
p13GeneratorActionPhaseBridgeFlipsPolarity = refl

p13GeneratorActionPhaseBridgeSourceHexTruthIsResidue :
  ActionPhase.sourceHexTruth p13ActionPhaseBridge ≡ p13ResidueHexTruth
p13GeneratorActionPhaseBridgeSourceHexTruthIsResidue = refl

p13GeneratorActionPhaseBridgeSourceHexFactorIsResidueFactor :
  ActionPhase.sourceHexFactor p13ActionPhaseBridge ≡ p13ResidueHexFactor
p13GeneratorActionPhaseBridgeSourceHexFactorIsResidueFactor = refl

p13GeneratorActionPhaseBridgeTransportedHexTruthIsHex5 :
  ActionPhase.transportedHexTruth p13ActionPhaseBridge ≡ hex-5
p13GeneratorActionPhaseBridgeTransportedHexTruthIsHex5 = refl

p13GeneratorActionPhaseBridgeTransportedHexFactorIsHex5Factor :
  ActionPhase.transportedHexFactor p13ActionPhaseBridge ≡ hexTruthToFactor hex-5
p13GeneratorActionPhaseBridgeTransportedHexFactorIsHex5Factor = refl

p13GeneratorProfileNormalizedStepIs1 :
  normalizedStep p13GeneratorUnitActionProfile ≡ 1
p13GeneratorProfileNormalizedStepIs1 = refl

p13GeneratorProfileTriadicStepIs1 :
  triadicStep p13GeneratorUnitActionProfile ≡ 1
p13GeneratorProfileTriadicStepIs1 = refl

p13GeneratorProfileFlipsPolarity :
  flipsPolarity p13 canonicalGeneratorStep ≡ true
p13GeneratorProfileFlipsPolarity = refl

p13GeneratorProfileActedHexTruthIsHex5 :
  actedHexTruth p13GeneratorUnitActionProfile ≡ hex-5
p13GeneratorProfileActedHexTruthIsHex5 = refl

p13GeneratorProfileActedHexFactorIsHex5Factor :
  actedHexFactor p13GeneratorUnitActionProfile ≡ hexTruthToFactor hex-5
p13GeneratorProfileActedHexFactorIsHex5Factor = refl
