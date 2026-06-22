module DASHI.Physics.Closure.P13Stage12C12Regression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.P13EquivariantOddFieldGate as Odd using
  ( P13EquivariantOddFieldGateReceipt
  ; depth3FieldGeneratorOddGate
  ; depth3FieldSixthOddGate
  ; rootFieldIdentityOddGate
  )
open import DASHI.Foundations.P13HexTruthActionQuotient as Hex using
  ( generatorActsOnP13ResidueHexTruth
  ; halfTurnActsOnP13ResidueHexTruth
  )
open import DASHI.Foundations.P13UnitGroupC12Witness as C12 using
  ( P13UnitGroupC12Witness
  ; canonicalP13UnitGroupC12Witness
  )
open import DASHI.Geometry.P13UnitActionTreeIsometry as Tree using
  ( generatorActsOnCanonicalAddressDigits
  ; generatorActsOnCanonicalPrefixDigits
  ; generatorCommutesWithPrefixOnCanonicalAddress
  ; generatorCanonicalSelfDistanceIsZero
  ; generatorPreservesCanonicalDepth
  )
open import DASHI.Interop.PrimeSuccessorWitness as Successor using
  ( canonicalP13PrimeSuccessorWitness
  ; stageWitnessed
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( p13SSPPrimeLane369PhaseBridge )

record P13Stage12C12Regression : Set where
  constructor mkP13Stage12C12Regression
  field
    phaseBridge : Phase.SSPPrimeLane369PhaseBridge
    unitGroupWitness : P13UnitGroupC12Witness
    rootIdentityOddGate : P13EquivariantOddFieldGateReceipt zero
    depth3GeneratorOddGate :
      P13EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
    depth3HalfTurnOddGate :
      P13EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
    stage12Witnessed :
      stageWitnessed canonicalP13PrimeSuccessorWitness ≡ 12
    stage1Identity :
      C12.primeIdentityStageIsAtlas1 canonicalP13UnitGroupC12Witness ≡ refl
    stage0UnitOrder :
      C12.unitOrderStageIsAtlas0 canonicalP13UnitGroupC12Witness ≡ refl
    generatorActsOnResidueAsHex5 :
      Hex.generatorActsOnP13ResidueHexTruth ≡ refl
    halfTurnActsOnResidueAsHex1 :
      Hex.halfTurnActsOnP13ResidueHexTruth ≡ refl
    generatorCanonicalTreeReceipt :
      Tree.generatorActsOnCanonicalAddressDigits ≡ refl
    generatorCanonicalPrefixTreeReceipt :
      Tree.generatorActsOnCanonicalPrefixDigits ≡ refl
    generatorPrefixCommutesReceipt :
      Tree.generatorCommutesWithPrefixOnCanonicalAddress ≡ refl
    generatorPreservesCanonicalDepthReceipt :
      Tree.generatorPreservesCanonicalDepth ≡ refl
    generatorSelfDistanceReceipt :
      Tree.generatorCanonicalSelfDistanceIsZero ≡ refl

open P13Stage12C12Regression public

canonicalP13Stage12C12Regression : P13Stage12C12Regression
canonicalP13Stage12C12Regression =
  mkP13Stage12C12Regression
    p13SSPPrimeLane369PhaseBridge
    canonicalP13UnitGroupC12Witness
    rootFieldIdentityOddGate
    depth3FieldGeneratorOddGate
    depth3FieldSixthOddGate
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
