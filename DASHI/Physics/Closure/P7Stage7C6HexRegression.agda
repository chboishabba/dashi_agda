module DASHI.Physics.Closure.P7Stage7C6HexRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.P7EquivariantOddFieldGate as Odd using
  ( P7EquivariantOddFieldGateReceipt
  ; depth3FieldGeneratorOddGate
  ; depth3FieldMobiusOddGate
  ; rootFieldIdentityOddGate
  )
open import DASHI.Foundations.P7HexTruthActionQuotient as Hex using
  ( generatorActsOnP7ResidueHexTruth
  ; mobiusActsAsMobiusTransport
  ; mobiusSquaredActsAsIdentity
  ; p7ResidueHexTruth
  )
open import DASHI.Foundations.P7UnitGroupC6Witness as C6 using
  ( P7UnitGroupC6Witness
  ; canonicalP7UnitGroupC6Witness
  ; p7GeneratorCubedIsMobius
  ; p7IdentityStageIsStage7
  ; p7UnitStageIsStage6
  )
open import DASHI.Foundations.SSPPrimeLaneUnitGroup using
  ( p7UnitGenerator
  ; p7UnitIdentity
  ; p7UnitMobiusElement
  )
open import DASHI.Geometry.P7UnitActionTreeIsometry as Tree using
  ( generatorActsOnCanonicalAddressDigits
  ; generatorCanonicalSelfDistanceIsZero
  ; mobiusActsOnCanonicalAddressDigits
  ; mobiusCanonicalSelfDistanceIsZero
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( p7SSPPrimeLane369PhaseBridge )
open import DASHI.Foundations.StageAtlasZeroToEleven using (atlas-6; atlas-7)
open import Base369 using (hex-5)

record P7Stage7C6HexRegression : Set where
  constructor mkP7Stage7C6HexRegression
  field
    phaseBridge : Phase.SSPPrimeLane369PhaseBridge
    unitGroupWitness : P7UnitGroupC6Witness
    rootIdentityOddGate : P7EquivariantOddFieldGateReceipt zero
    depth3GeneratorOddGate :
      P7EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
    depth3MobiusOddGate :
      P7EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
    stage7Identity :
      C6.p7IdentityStageIsStage7 ≡ refl
    stage6UnitOrder :
      C6.p7UnitStageIsStage6 ≡ refl
    generatorCubedMatchesMobius :
      C6.p7GeneratorCubedIsMobius ≡ refl
    generatorActsOnResidueAsHex5 :
      Hex.generatorActsOnP7ResidueHexTruth ≡ refl
    generatorCanonicalTreeReceipt :
      Tree.generatorActsOnCanonicalAddressDigits ≡ refl
    mobiusCanonicalTreeReceipt :
      Tree.mobiusActsOnCanonicalAddressDigits ≡ refl
    generatorSelfDistanceReceipt :
      Tree.generatorCanonicalSelfDistanceIsZero ≡ refl
    mobiusSelfDistanceReceipt :
      Tree.mobiusCanonicalSelfDistanceIsZero ≡ refl

open P7Stage7C6HexRegression public

canonicalP7Stage7C6HexRegression : P7Stage7C6HexRegression
canonicalP7Stage7C6HexRegression =
  mkP7Stage7C6HexRegression
    p7SSPPrimeLane369PhaseBridge
    canonicalP7UnitGroupC6Witness
    rootFieldIdentityOddGate
    depth3FieldGeneratorOddGate
    depth3FieldMobiusOddGate
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
