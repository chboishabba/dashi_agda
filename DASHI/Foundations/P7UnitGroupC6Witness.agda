module DASHI.Foundations.P7UnitGroupC6Witness where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.P7HexTruthActionQuotient using ()
open import DASHI.Foundations.SSPPrimeLaneSymmetryProfile as Symmetry using
  ( p7PrimeLaneSymmetryProfile
  ; unitOrder
  )
open import DASHI.Foundations.SSPPrimeLaneUnitGroup using
  ( P7UnitClass
  ; composeP7UnitClass
  ; generatorCubeIsMobius
  ; generatorPower2
  ; generatorPower3
  ; generatorPower6
  ; inverseP7UnitClass
  ; leftInverseP7UnitClass
  ; mobiusSquaredIsIdentity
  ; p7-unit2
  ; p7-unit4
  ; p7-unit5
  ; p7UnitGenerator
  ; p7UnitIdentity
  ; p7UnitMobiusElement
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( p7PrimeIdentityStageIsAtlas7
  ; p7SSPPrimeLane369PhaseBridge
  ; p7UnitOrderIs6
  ; p7UnitOrderStageIsAtlas6
  )

record P7UnitGroupC6Witness : Set where
  constructor mkP7UnitGroupC6Witness
  field
    phaseBridgeIsCanonical :
      Phase.unitOrder p7SSPPrimeLane369PhaseBridge ≡ 6
    symmetryProfileOrderIs6 :
      Symmetry.unitOrder p7PrimeLaneSymmetryProfile ≡ 6
    generator : P7UnitClass
    identity : P7UnitClass
    mobiusElement : P7UnitClass
    generatorOrderSix :
      composeP7UnitClass p7UnitGenerator p7-unit5 ≡ p7UnitIdentity
    generatorCubeMatchesMobius :
      composeP7UnitClass p7UnitGenerator
        (composeP7UnitClass p7UnitGenerator p7UnitGenerator)
      ≡ p7UnitMobiusElement
    mobiusOrderTwo :
      composeP7UnitClass p7UnitMobiusElement p7UnitMobiusElement
      ≡ p7UnitIdentity
    generatorInverseIsFive :
      inverseP7UnitClass p7UnitGenerator ≡ p7-unit5
    generatorTwoInverseIsFour :
      inverseP7UnitClass p7-unit2 ≡ p7-unit4
    generatorHasLeftInverse :
      composeP7UnitClass (inverseP7UnitClass p7UnitGenerator) p7UnitGenerator
      ≡ p7UnitIdentity

open P7UnitGroupC6Witness public

canonicalP7UnitGroupC6Witness : P7UnitGroupC6Witness
canonicalP7UnitGroupC6Witness =
  mkP7UnitGroupC6Witness
    p7UnitOrderIs6
    Symmetry.p7UnitOrderIs6
    p7UnitGenerator
    p7UnitIdentity
    p7UnitMobiusElement
    generatorPower6
    generatorCubeIsMobius
    mobiusSquaredIsIdentity
    refl
    refl
    (leftInverseP7UnitClass p7UnitGenerator)

p7IdentityStageIsStage7 = p7PrimeIdentityStageIsAtlas7

p7UnitStageIsStage6 = p7UnitOrderStageIsAtlas6

p7GeneratorSquaredIsTwo :
  composeP7UnitClass p7UnitGenerator p7UnitGenerator ≡ p7-unit2
p7GeneratorSquaredIsTwo = generatorPower2

p7GeneratorCubedIsMobius :
  composeP7UnitClass p7UnitGenerator
    (composeP7UnitClass p7UnitGenerator p7UnitGenerator)
  ≡ p7UnitMobiusElement
p7GeneratorCubedIsMobius = generatorPower3
