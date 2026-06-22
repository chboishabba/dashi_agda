module DASHI.Foundations.P11UnitGroupC10Witness where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Foundations.PrimeLaneUnitActionQuotient as Quotient
open import DASHI.Foundations.SSPPrimeLaneUnitAction using
  ( canonicalGeneratorStep
  ; primeLaneUnitActionProfile
  )
open import DASHI.Foundations.SSPPrimeLaneSymmetryProfile as Symmetry using
  ( p11PrimeLaneSymmetryProfile )
open import DASHI.Foundations.StageAtlasZeroToEleven using
  ( atlas-10
  ; atlas-11
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( p11PrimeIdentityStageIsAtlas11
  ; p11SSPPrimeLane369PhaseBridge
  ; p11UnitOrderIs10
  ; p11UnitOrderStageIsAtlas10
  )
open import DASHI.TrackedPrimes using (p11)

data P11UnitClass : Set where
  p11-unit0 : P11UnitClass
  p11-unit1 : P11UnitClass
  p11-unit2 : P11UnitClass
  p11-unit3 : P11UnitClass
  p11-unit4 : P11UnitClass
  p11-unit5 : P11UnitClass
  p11-unit6 : P11UnitClass
  p11-unit7 : P11UnitClass
  p11-unit8 : P11UnitClass
  p11-unit9 : P11UnitClass

p11UnitIdentity : P11UnitClass
p11UnitIdentity = p11-unit0

p11UnitGenerator : P11UnitClass
p11UnitGenerator = p11-unit1

p11UnitPentadElement : P11UnitClass
p11UnitPentadElement = p11-unit2

p11UnitHalfTurnElement : P11UnitClass
p11UnitHalfTurnElement = p11-unit5

succP11UnitClass : P11UnitClass → P11UnitClass
succP11UnitClass p11-unit0 = p11-unit1
succP11UnitClass p11-unit1 = p11-unit2
succP11UnitClass p11-unit2 = p11-unit3
succP11UnitClass p11-unit3 = p11-unit4
succP11UnitClass p11-unit4 = p11-unit5
succP11UnitClass p11-unit5 = p11-unit6
succP11UnitClass p11-unit6 = p11-unit7
succP11UnitClass p11-unit7 = p11-unit8
succP11UnitClass p11-unit8 = p11-unit9
succP11UnitClass p11-unit9 = p11-unit0

toStep : P11UnitClass → Nat
toStep p11-unit0 = 0
toStep p11-unit1 = 1
toStep p11-unit2 = 2
toStep p11-unit3 = 3
toStep p11-unit4 = 4
toStep p11-unit5 = 5
toStep p11-unit6 = 6
toStep p11-unit7 = 7
toStep p11-unit8 = 8
toStep p11-unit9 = 9

composeP11UnitClass : P11UnitClass → P11UnitClass → P11UnitClass
composeP11UnitClass p11-unit0 x = x
composeP11UnitClass p11-unit1 x = succP11UnitClass x
composeP11UnitClass p11-unit2 x = succP11UnitClass (succP11UnitClass x)
composeP11UnitClass p11-unit3 x =
  succP11UnitClass (succP11UnitClass (succP11UnitClass x))
composeP11UnitClass p11-unit4 x =
  succP11UnitClass
    (succP11UnitClass
      (succP11UnitClass
        (succP11UnitClass x)))
composeP11UnitClass p11-unit5 x =
  succP11UnitClass
    (succP11UnitClass
      (succP11UnitClass
        (succP11UnitClass
          (succP11UnitClass x))))
composeP11UnitClass p11-unit6 x =
  succP11UnitClass
    (succP11UnitClass
      (succP11UnitClass
        (succP11UnitClass
          (succP11UnitClass
            (succP11UnitClass x)))))
composeP11UnitClass p11-unit7 x =
  succP11UnitClass
    (succP11UnitClass
      (succP11UnitClass
        (succP11UnitClass
          (succP11UnitClass
            (succP11UnitClass
              (succP11UnitClass x))))))
composeP11UnitClass p11-unit8 x =
  succP11UnitClass
    (succP11UnitClass
      (succP11UnitClass
        (succP11UnitClass
          (succP11UnitClass
            (succP11UnitClass
              (succP11UnitClass
                (succP11UnitClass x)))))))
composeP11UnitClass p11-unit9 x =
  succP11UnitClass
    (succP11UnitClass
      (succP11UnitClass
        (succP11UnitClass
          (succP11UnitClass
            (succP11UnitClass
              (succP11UnitClass
                (succP11UnitClass
                  (succP11UnitClass x))))))))

inverseP11UnitClass : P11UnitClass → P11UnitClass
inverseP11UnitClass p11-unit0 = p11-unit0
inverseP11UnitClass p11-unit1 = p11-unit9
inverseP11UnitClass p11-unit2 = p11-unit8
inverseP11UnitClass p11-unit3 = p11-unit7
inverseP11UnitClass p11-unit4 = p11-unit6
inverseP11UnitClass p11-unit5 = p11-unit5
inverseP11UnitClass p11-unit6 = p11-unit4
inverseP11UnitClass p11-unit7 = p11-unit3
inverseP11UnitClass p11-unit8 = p11-unit2
inverseP11UnitClass p11-unit9 = p11-unit1

generatorPower2 :
  composeP11UnitClass p11UnitGenerator p11UnitGenerator ≡ p11-unit2
generatorPower2 = refl

generatorPower5 :
  composeP11UnitClass p11UnitGenerator p11-unit4 ≡ p11UnitHalfTurnElement
generatorPower5 = refl

generatorPower10 :
  composeP11UnitClass p11UnitGenerator p11-unit9 ≡ p11UnitIdentity
generatorPower10 = refl

halfTurnSquaredIsIdentity :
  composeP11UnitClass p11UnitHalfTurnElement p11UnitHalfTurnElement
  ≡ p11UnitIdentity
halfTurnSquaredIsIdentity = refl

pentadOrderFive :
  composeP11UnitClass p11UnitPentadElement p11-unit8 ≡ p11UnitIdentity
pentadOrderFive = refl

leftIdentityP11UnitClass :
  (x : P11UnitClass) →
  composeP11UnitClass p11UnitIdentity x ≡ x
leftIdentityP11UnitClass p11-unit0 = refl
leftIdentityP11UnitClass p11-unit1 = refl
leftIdentityP11UnitClass p11-unit2 = refl
leftIdentityP11UnitClass p11-unit3 = refl
leftIdentityP11UnitClass p11-unit4 = refl
leftIdentityP11UnitClass p11-unit5 = refl
leftIdentityP11UnitClass p11-unit6 = refl
leftIdentityP11UnitClass p11-unit7 = refl
leftIdentityP11UnitClass p11-unit8 = refl
leftIdentityP11UnitClass p11-unit9 = refl

leftInverseP11UnitClass :
  (x : P11UnitClass) →
  composeP11UnitClass (inverseP11UnitClass x) x ≡ p11UnitIdentity
leftInverseP11UnitClass p11-unit0 = refl
leftInverseP11UnitClass p11-unit1 = refl
leftInverseP11UnitClass p11-unit2 = refl
leftInverseP11UnitClass p11-unit3 = refl
leftInverseP11UnitClass p11-unit4 = refl
leftInverseP11UnitClass p11-unit5 = refl
leftInverseP11UnitClass p11-unit6 = refl
leftInverseP11UnitClass p11-unit7 = refl
leftInverseP11UnitClass p11-unit8 = refl
leftInverseP11UnitClass p11-unit9 = refl

canonicalP11UnitActionQuotient :
  Quotient.PrimeLaneUnitActionQuotientSurface
canonicalP11UnitActionQuotient =
  Quotient.mkPrimeLaneUnitActionQuotientSurface
    p11
    Quotient.p11C10PrimeLaneQuotientCarrier
    (Phase.primeLane369PhaseBridge p11)
    refl
    (primeLaneUnitActionProfile p11 canonicalGeneratorStep)
    refl
    Quotient.p11CandidateOnlyAuthority
    refl

record P11UnitGroupC10Witness : Set where
  constructor mkP11UnitGroupC10Witness
  field
    phaseBridgeOrderIs10 :
      Phase.unitOrder p11SSPPrimeLane369PhaseBridge ≡ 10
    symmetryProfileOrderIs10 :
      Symmetry.unitOrder p11PrimeLaneSymmetryProfile ≡ 10
    stage11Witness :
      Phase.primeIdentityStage p11SSPPrimeLane369PhaseBridge ≡ atlas-11
    stage10Witness :
      Phase.unitOrderStage p11SSPPrimeLane369PhaseBridge ≡ atlas-10
    generator : P11UnitClass
    identity : P11UnitClass
    halfTurn : P11UnitClass
    pentadElement : P11UnitClass
    generatorOrderTen :
      composeP11UnitClass p11UnitGenerator p11-unit9 ≡ p11UnitIdentity
    halfTurnOrderTwo :
      composeP11UnitClass p11UnitHalfTurnElement p11UnitHalfTurnElement
      ≡ p11UnitIdentity
    pentadOrderFiveWitness :
      composeP11UnitClass p11UnitPentadElement p11-unit8 ≡ p11UnitIdentity
    generatorInverseIsNine :
      inverseP11UnitClass p11UnitGenerator ≡ p11-unit9

open P11UnitGroupC10Witness public

canonicalP11UnitGroupC10Witness : P11UnitGroupC10Witness
canonicalP11UnitGroupC10Witness =
  mkP11UnitGroupC10Witness
    p11UnitOrderIs10
    Symmetry.p11UnitOrderIs10
    p11PrimeIdentityStageIsAtlas11
    p11UnitOrderStageIsAtlas10
    p11UnitGenerator
    p11UnitIdentity
    p11UnitHalfTurnElement
    p11UnitPentadElement
    generatorPower10
    halfTurnSquaredIsIdentity
    pentadOrderFive
    refl
