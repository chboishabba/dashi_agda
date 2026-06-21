module DASHI.Physics.Closure.SSPPrimeLane369ActionPhaseBridge where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_; _,_)

open import Base369 using
  ( TriTruth
  ; HexTruth
  ; tri-high
  ; tri-low
  ; hex-0
  ; hex-5
  )

open import DASHI.Foundations.HexTruthPolarityFactor using
  ( Polarity
  ; hexTruthToFactor
  )
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( UnitActionStep
  ; actOnHexFactor
  ; actOnHexTruth
  ; canonicalGeneratorStep
  ; flipsPolarity
  ; normalizedUnitStep
  ; triadicActionStep
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( SSPPrimeLane369PhaseBridge
  ; primeLane369PhaseBridge
  ; residueSignature
  ; primeIdentityStage
  ; unitOrderStage
  )
open import DASHI.Foundations.SSPPrimeLane369Signature as Signature using
  ( hexResidue )
open import DASHI.TrackedPrimes using (SSP; p7; p11)

record SSPPrimeLane369ActionPhaseBridge : Set where
  constructor mkSSPPrimeLane369ActionPhaseBridge
  field
    sourcePhaseBridge : SSPPrimeLane369PhaseBridge
    primeIdentity : SSP
    rawStep : UnitActionStep
    normalizedStep : Nat
    triadicStep : Nat
    polarityFlipBit : Bool
    sourceHexTruth : HexTruth
    transportedHexTruth : HexTruth
    sourceHexFactor : TriTruth × Polarity
    transportedHexFactor : TriTruth × Polarity
    primeIdentityStageStable :
      primeIdentityStage sourcePhaseBridge ≡ primeIdentityStage sourcePhaseBridge
    unitOrderStageStable :
      unitOrderStage sourcePhaseBridge ≡ unitOrderStage sourcePhaseBridge
    normalizedStepMatches :
      normalizedStep ≡ normalizedUnitStep primeIdentity rawStep
    triadicStepMatches :
      triadicStep ≡ triadicActionStep primeIdentity rawStep
    polarityFlipBitMatches :
      polarityFlipBit ≡ flipsPolarity primeIdentity rawStep
    sourceHexTruthMatches :
      sourceHexTruth ≡ Signature.hexResidue (residueSignature sourcePhaseBridge)
    transportedHexTruthMatches :
      transportedHexTruth ≡ actOnHexTruth primeIdentity rawStep sourceHexTruth
    sourceHexFactorMatches :
      sourceHexFactor ≡ hexTruthToFactor sourceHexTruth
    transportedHexFactorMatches :
      transportedHexFactor ≡ hexTruthToFactor transportedHexTruth

open SSPPrimeLane369ActionPhaseBridge public

primeLane369ActionPhaseBridge :
  SSP →
  UnitActionStep →
  SSPPrimeLane369ActionPhaseBridge
primeLane369ActionPhaseBridge p step =
  mkSSPPrimeLane369ActionPhaseBridge
    (Phase.primeLane369PhaseBridge p)
    p
    step
    (Action.normalizedUnitStep p step)
    (Action.triadicActionStep p step)
    (Action.flipsPolarity p step)
    (Signature.hexResidue (Phase.residueSignature (Phase.primeLane369PhaseBridge p)))
    (Action.actOnHexTruth p step
      (Signature.hexResidue (Phase.residueSignature (Phase.primeLane369PhaseBridge p))))
    (hexTruthToFactor
      (Signature.hexResidue (Phase.residueSignature (Phase.primeLane369PhaseBridge p))))
    (Action.actOnHexFactor p step
      (Signature.hexResidue (Phase.residueSignature (Phase.primeLane369PhaseBridge p))))
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalP7GeneratorActionPhaseBridge :
  SSPPrimeLane369ActionPhaseBridge
canonicalP7GeneratorActionPhaseBridge =
  primeLane369ActionPhaseBridge p7 canonicalGeneratorStep

canonicalP11GeneratorActionPhaseBridge :
  SSPPrimeLane369ActionPhaseBridge
canonicalP11GeneratorActionPhaseBridge =
  primeLane369ActionPhaseBridge p11 canonicalGeneratorStep

canonicalP7GeneratorTransportedHexTruth :
  transportedHexTruth canonicalP7GeneratorActionPhaseBridge ≡ hex-5
canonicalP7GeneratorTransportedHexTruth = refl

canonicalP11GeneratorTransportedHexTruth :
  transportedHexTruth canonicalP11GeneratorActionPhaseBridge ≡ hex-0
canonicalP11GeneratorTransportedHexTruth = refl

canonicalP7GeneratorTriadicStepIs1 :
  triadicStep canonicalP7GeneratorActionPhaseBridge ≡ 1
canonicalP7GeneratorTriadicStepIs1 = refl

canonicalP11GeneratorTriadicStepIs1 :
  triadicStep canonicalP11GeneratorActionPhaseBridge ≡ 1
canonicalP11GeneratorTriadicStepIs1 = refl
