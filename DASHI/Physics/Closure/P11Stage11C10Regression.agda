module DASHI.Physics.Closure.P11Stage11C10Regression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.P11EquivariantOddFieldGate as Odd using
  ( P11EquivariantOddFieldGateReceipt
  ; depth3FieldGeneratorOddGate
  ; depth3FieldHalfTurnOddGate
  ; rootFieldIdentityOddGate
  )
open import DASHI.Foundations.P11HexTruthActionQuotient as Hex using
  ( generatorActsOnP11ResidueHexTruth
  ; halfTurnActsOnP11ResidueHexTruth
  )
open import DASHI.Foundations.P11UnitGroupC10Witness as C10 using
  ( P11UnitGroupC10Witness
  ; canonicalP11UnitGroupC10Witness
  ; p11UnitHalfTurnElement
  )
open import DASHI.Geometry.P11UnitActionTreeIsometry as Tree using
  ( generatorActsOnCanonicalAddressDigits
  ; generatorCanonicalSelfDistanceIsZero
  ; halfTurnActsOnCanonicalAddressDigits
  ; halfTurnCanonicalSelfDistanceIsZero
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( p11SSPPrimeLane369PhaseBridge )

record P11Stage11C10Regression : Set where
  constructor mkP11Stage11C10Regression
  field
    phaseBridge : Phase.SSPPrimeLane369PhaseBridge
    unitGroupWitness : P11UnitGroupC10Witness
    rootIdentityOddGate : P11EquivariantOddFieldGateReceipt zero
    depth3GeneratorOddGate :
      P11EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
    depth3HalfTurnOddGate :
      P11EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
    stage11Identity :
      C10.stage11Witness canonicalP11UnitGroupC10Witness ≡ refl
    stage10UnitOrder :
      C10.stage10Witness canonicalP11UnitGroupC10Witness ≡ refl
    generatorActsOnResidueAsHex0 :
      Hex.generatorActsOnP11ResidueHexTruth ≡ refl
    halfTurnActsOnResidueAsHex1 :
      Hex.halfTurnActsOnP11ResidueHexTruth ≡ refl
    generatorCanonicalTreeReceipt :
      Tree.generatorActsOnCanonicalAddressDigits ≡ refl
    halfTurnCanonicalTreeReceipt :
      Tree.halfTurnActsOnCanonicalAddressDigits ≡ refl
    generatorSelfDistanceReceipt :
      Tree.generatorCanonicalSelfDistanceIsZero ≡ refl
    halfTurnSelfDistanceReceipt :
      Tree.halfTurnCanonicalSelfDistanceIsZero ≡ refl

open P11Stage11C10Regression public

canonicalP11Stage11C10Regression : P11Stage11C10Regression
canonicalP11Stage11C10Regression =
  mkP11Stage11C10Regression
    p11SSPPrimeLane369PhaseBridge
    canonicalP11UnitGroupC10Witness
    rootFieldIdentityOddGate
    depth3FieldGeneratorOddGate
    depth3FieldHalfTurnOddGate
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
