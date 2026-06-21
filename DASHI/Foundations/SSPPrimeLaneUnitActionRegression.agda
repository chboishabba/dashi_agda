module DASHI.Foundations.SSPPrimeLaneUnitActionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.SuperSSP369EquivariantOddGate as Equivariant using
  ( SuperSSP369EquivariantOddGateReceipt
  ; canonicalRootFieldEquivariantOddGateReceipt
  ; canonicalDepth3FieldEquivariantOddGateReceipt
  )
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( SSPPrimeLaneUnitActionProfile
  ; p7GeneratorUnitActionProfile
  ; p11GeneratorUnitActionProfile
  )
open import DASHI.Geometry.SSP369SymmetryIsometry as Iso using
  ( SSP369SymmetryIsometryReceipt
  ; canonicalP7GeneratorIsometryReceipt
  ; canonicalP11GeneratorIsometryReceipt
  )
open import DASHI.Geometry.SSP369TreeAutomorphism as Auto using
  ( p7CanonicalThreeSixNineDigitsAfterGenerator
  ; p11CanonicalThreeSixNineDigitsAfterGenerator
  )
open import DASHI.Physics.Closure.SSPPrimeLane369ActionPhaseBridge as Phase using
  ( SSPPrimeLane369ActionPhaseBridge
  ; canonicalP7GeneratorActionPhaseBridge
  ; canonicalP11GeneratorActionPhaseBridge
  )

record SSPPrimeLaneUnitActionRegression : Set where
  constructor mkSSPPrimeLaneUnitActionRegression
  field
    p7ActionProfile : SSPPrimeLaneUnitActionProfile
    p11ActionProfile : SSPPrimeLaneUnitActionProfile
    p7ActionPhaseBridge : SSPPrimeLane369ActionPhaseBridge
    p11ActionPhaseBridge : SSPPrimeLane369ActionPhaseBridge
    p7IsometryReceipt : SSP369SymmetryIsometryReceipt (suc (suc (suc zero)))
    p11IsometryReceipt : SSP369SymmetryIsometryReceipt (suc (suc (suc zero)))
    rootEquivariantOddGate : SuperSSP369EquivariantOddGateReceipt zero
    depth3EquivariantOddGate :
      SuperSSP369EquivariantOddGateReceipt (suc (suc (suc zero)))
    p7ActionProfileIsCanonical :
      p7ActionProfile ≡ Action.p7GeneratorUnitActionProfile
    p11ActionProfileIsCanonical :
      p11ActionProfile ≡ Action.p11GeneratorUnitActionProfile
    p7ActionPhaseBridgeIsCanonical :
      p7ActionPhaseBridge ≡ Phase.canonicalP7GeneratorActionPhaseBridge
    p11ActionPhaseBridgeIsCanonical :
      p11ActionPhaseBridge ≡ Phase.canonicalP11GeneratorActionPhaseBridge
    p7IsometryReceiptIsCanonical :
      p7IsometryReceipt ≡ Iso.canonicalP7GeneratorIsometryReceipt
    p11IsometryReceiptIsCanonical :
      p11IsometryReceipt ≡ Iso.canonicalP11GeneratorIsometryReceipt
    rootEquivariantOddGateIsCanonical :
      rootEquivariantOddGate
      ≡ Equivariant.canonicalRootFieldEquivariantOddGateReceipt
    depth3EquivariantOddGateIsCanonical :
      depth3EquivariantOddGate
      ≡ Equivariant.canonicalDepth3FieldEquivariantOddGateReceipt

open SSPPrimeLaneUnitActionRegression public

canonicalSSPPrimeLaneUnitActionRegression :
  SSPPrimeLaneUnitActionRegression
canonicalSSPPrimeLaneUnitActionRegression =
  mkSSPPrimeLaneUnitActionRegression
    Action.p7GeneratorUnitActionProfile
    Action.p11GeneratorUnitActionProfile
    Phase.canonicalP7GeneratorActionPhaseBridge
    Phase.canonicalP11GeneratorActionPhaseBridge
    Iso.canonicalP7GeneratorIsometryReceipt
    Iso.canonicalP11GeneratorIsometryReceipt
    Equivariant.canonicalRootFieldEquivariantOddGateReceipt
    Equivariant.canonicalDepth3FieldEquivariantOddGateReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
