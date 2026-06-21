module DASHI.Foundations.SSPPrimeLaneUnitGroup where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data P7UnitClass : Set where
  p7-unit0 : P7UnitClass
  p7-unit1 : P7UnitClass
  p7-unit2 : P7UnitClass
  p7-unit3 : P7UnitClass
  p7-unit4 : P7UnitClass
  p7-unit5 : P7UnitClass

p7UnitIdentity : P7UnitClass
p7UnitIdentity = p7-unit0

p7UnitGenerator : P7UnitClass
p7UnitGenerator = p7-unit1

p7UnitMobiusElement : P7UnitClass
p7UnitMobiusElement = p7-unit3

succP7UnitClass : P7UnitClass → P7UnitClass
succP7UnitClass p7-unit0 = p7-unit1
succP7UnitClass p7-unit1 = p7-unit2
succP7UnitClass p7-unit2 = p7-unit3
succP7UnitClass p7-unit3 = p7-unit4
succP7UnitClass p7-unit4 = p7-unit5
succP7UnitClass p7-unit5 = p7-unit0

predP7UnitClass : P7UnitClass → P7UnitClass
predP7UnitClass p7-unit0 = p7-unit5
predP7UnitClass p7-unit1 = p7-unit0
predP7UnitClass p7-unit2 = p7-unit1
predP7UnitClass p7-unit3 = p7-unit2
predP7UnitClass p7-unit4 = p7-unit3
predP7UnitClass p7-unit5 = p7-unit4

toStep : P7UnitClass → Nat
toStep p7-unit0 = 0
toStep p7-unit1 = 1
toStep p7-unit2 = 2
toStep p7-unit3 = 3
toStep p7-unit4 = 4
toStep p7-unit5 = 5

composeP7UnitClass : P7UnitClass → P7UnitClass → P7UnitClass
composeP7UnitClass p7-unit0 x = x
composeP7UnitClass p7-unit1 x = succP7UnitClass x
composeP7UnitClass p7-unit2 x = succP7UnitClass (succP7UnitClass x)
composeP7UnitClass p7-unit3 x = succP7UnitClass (succP7UnitClass (succP7UnitClass x))
composeP7UnitClass p7-unit4 x =
  succP7UnitClass (succP7UnitClass (succP7UnitClass (succP7UnitClass x)))
composeP7UnitClass p7-unit5 x =
  succP7UnitClass
    (succP7UnitClass
      (succP7UnitClass
        (succP7UnitClass
          (succP7UnitClass x))))

inverseP7UnitClass : P7UnitClass → P7UnitClass
inverseP7UnitClass p7-unit0 = p7-unit0
inverseP7UnitClass p7-unit1 = p7-unit5
inverseP7UnitClass p7-unit2 = p7-unit4
inverseP7UnitClass p7-unit3 = p7-unit3
inverseP7UnitClass p7-unit4 = p7-unit2
inverseP7UnitClass p7-unit5 = p7-unit1

generatorPower0 :
  composeP7UnitClass p7UnitIdentity p7UnitGenerator ≡ p7UnitGenerator
generatorPower0 = refl

generatorPower1 :
  composeP7UnitClass p7UnitGenerator p7UnitIdentity ≡ p7-unit1
generatorPower1 = refl

generatorPower2 :
  composeP7UnitClass p7UnitGenerator p7UnitGenerator ≡ p7-unit2
generatorPower2 = refl

generatorPower3 :
  composeP7UnitClass p7UnitGenerator p7-unit2 ≡ p7UnitMobiusElement
generatorPower3 = refl

generatorPower4 :
  composeP7UnitClass p7UnitGenerator p7UnitMobiusElement ≡ p7-unit4
generatorPower4 = refl

generatorPower5 :
  composeP7UnitClass p7UnitGenerator p7-unit4 ≡ p7-unit5
generatorPower5 = refl

generatorPower6 :
  composeP7UnitClass p7UnitGenerator p7-unit5 ≡ p7UnitIdentity
generatorPower6 = refl

generatorCubeIsMobius :
  composeP7UnitClass p7UnitGenerator
    (composeP7UnitClass p7UnitGenerator p7UnitGenerator)
  ≡ p7UnitMobiusElement
generatorCubeIsMobius = refl

mobiusSquaredIsIdentity :
  composeP7UnitClass p7UnitMobiusElement p7UnitMobiusElement ≡ p7UnitIdentity
mobiusSquaredIsIdentity = refl

leftIdentityP7UnitClass :
  (x : P7UnitClass) →
  composeP7UnitClass p7UnitIdentity x ≡ x
leftIdentityP7UnitClass p7-unit0 = refl
leftIdentityP7UnitClass p7-unit1 = refl
leftIdentityP7UnitClass p7-unit2 = refl
leftIdentityP7UnitClass p7-unit3 = refl
leftIdentityP7UnitClass p7-unit4 = refl
leftIdentityP7UnitClass p7-unit5 = refl

rightIdentityP7UnitClass :
  (x : P7UnitClass) →
  composeP7UnitClass x p7UnitIdentity ≡ x
rightIdentityP7UnitClass p7-unit0 = refl
rightIdentityP7UnitClass p7-unit1 = refl
rightIdentityP7UnitClass p7-unit2 = refl
rightIdentityP7UnitClass p7-unit3 = refl
rightIdentityP7UnitClass p7-unit4 = refl
rightIdentityP7UnitClass p7-unit5 = refl

leftInverseP7UnitClass :
  (x : P7UnitClass) →
  composeP7UnitClass (inverseP7UnitClass x) x ≡ p7UnitIdentity
leftInverseP7UnitClass p7-unit0 = refl
leftInverseP7UnitClass p7-unit1 = refl
leftInverseP7UnitClass p7-unit2 = refl
leftInverseP7UnitClass p7-unit3 = refl
leftInverseP7UnitClass p7-unit4 = refl
leftInverseP7UnitClass p7-unit5 = refl

rightInverseP7UnitClass :
  (x : P7UnitClass) →
  composeP7UnitClass x (inverseP7UnitClass x) ≡ p7UnitIdentity
rightInverseP7UnitClass p7-unit0 = refl
rightInverseP7UnitClass p7-unit1 = refl
rightInverseP7UnitClass p7-unit2 = refl
rightInverseP7UnitClass p7-unit3 = refl
rightInverseP7UnitClass p7-unit4 = refl
rightInverseP7UnitClass p7-unit5 = refl

doublePredReturnsSource :
  (x : P7UnitClass) →
  predP7UnitClass (succP7UnitClass x) ≡ x
doublePredReturnsSource p7-unit0 = refl
doublePredReturnsSource p7-unit1 = refl
doublePredReturnsSource p7-unit2 = refl
doublePredReturnsSource p7-unit3 = refl
doublePredReturnsSource p7-unit4 = refl
doublePredReturnsSource p7-unit5 = refl
