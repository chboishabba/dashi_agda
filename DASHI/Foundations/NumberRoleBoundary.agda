module DASHI.Foundations.NumberRoleBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

data Empty : Set where

data NumberRole : Set where
  algebraCarrierRole :
    NumberRole

  factorCoordinateRole :
    NumberRole

  phaseTopologicalRole :
    NumberRole

  quotientTransportRole :
    NumberRole

  narrativeMnemonicRole :
    NumberRole

numberRoleLabel : NumberRole → String
numberRoleLabel algebraCarrierRole =
  "algebra-carrier"
numberRoleLabel factorCoordinateRole =
  "factor-coordinate"
numberRoleLabel phaseTopologicalRole =
  "phase-topological"
numberRoleLabel quotientTransportRole =
  "quotient-transport"
numberRoleLabel narrativeMnemonicRole =
  "narrative-mnemonic"

algebraCarrierRole≠factorCoordinateRole :
  algebraCarrierRole ≡ factorCoordinateRole →
  Empty
algebraCarrierRole≠factorCoordinateRole ()

algebraCarrierRole≠phaseTopologicalRole :
  algebraCarrierRole ≡ phaseTopologicalRole →
  Empty
algebraCarrierRole≠phaseTopologicalRole ()

algebraCarrierRole≠quotientTransportRole :
  algebraCarrierRole ≡ quotientTransportRole →
  Empty
algebraCarrierRole≠quotientTransportRole ()

algebraCarrierRole≠narrativeMnemonicRole :
  algebraCarrierRole ≡ narrativeMnemonicRole →
  Empty
algebraCarrierRole≠narrativeMnemonicRole ()

factorCoordinateRole≠phaseTopologicalRole :
  factorCoordinateRole ≡ phaseTopologicalRole →
  Empty
factorCoordinateRole≠phaseTopologicalRole ()

factorCoordinateRole≠quotientTransportRole :
  factorCoordinateRole ≡ quotientTransportRole →
  Empty
factorCoordinateRole≠quotientTransportRole ()

factorCoordinateRole≠narrativeMnemonicRole :
  factorCoordinateRole ≡ narrativeMnemonicRole →
  Empty
factorCoordinateRole≠narrativeMnemonicRole ()

phaseTopologicalRole≠quotientTransportRole :
  phaseTopologicalRole ≡ quotientTransportRole →
  Empty
phaseTopologicalRole≠quotientTransportRole ()

phaseTopologicalRole≠narrativeMnemonicRole :
  phaseTopologicalRole ≡ narrativeMnemonicRole →
  Empty
phaseTopologicalRole≠narrativeMnemonicRole ()

quotientTransportRole≠narrativeMnemonicRole :
  quotientTransportRole ≡ narrativeMnemonicRole →
  Empty
quotientTransportRole≠narrativeMnemonicRole ()

data NumeralToken : Set where
  numeral0 : NumeralToken
  numeral1 : NumeralToken
  numeral2 : NumeralToken
  numeral3 : NumeralToken
  numeral4 : NumeralToken
  numeral5 : NumeralToken
  numeral6 : NumeralToken
  numeral7 : NumeralToken
  numeral8 : NumeralToken
  numeral9 : NumeralToken
  numeral10 : NumeralToken
  numeral11 : NumeralToken

numeralTokenLabel : NumeralToken → String
numeralTokenLabel numeral0 = "0"
numeralTokenLabel numeral1 = "1"
numeralTokenLabel numeral2 = "2"
numeralTokenLabel numeral3 = "3"
numeralTokenLabel numeral4 = "4"
numeralTokenLabel numeral5 = "5"
numeralTokenLabel numeral6 = "6"
numeralTokenLabel numeral7 = "7"
numeralTokenLabel numeral8 = "8"
numeralTokenLabel numeral9 = "9"
numeralTokenLabel numeral10 = "10"
numeralTokenLabel numeral11 = "11"

record NumberRoleReading : Set where
  constructor mkNumberRoleReading
  field
    numeral :
      NumeralToken

    role :
      NumberRole

    readingLabel :
      String

    promotesWithoutBridge :
      Bool

    promotesWithoutBridgeIsFalse :
      promotesWithoutBridge ≡ false

open NumberRoleReading public

triTruthAlgebraReading : NumberRoleReading
triTruthAlgebraReading =
  mkNumberRoleReading
    numeral3
    algebraCarrierRole
    "3 as TriTruth algebra carrier"
    false
    refl

hexTruthAlgebraReading : NumberRoleReading
hexTruthAlgebraReading =
  mkNumberRoleReading
    numeral6
    algebraCarrierRole
    "6 as HexTruth algebra carrier"
    false
    refl

nonaryTruthAlgebraReading : NumberRoleReading
nonaryTruthAlgebraReading =
  mkNumberRoleReading
    numeral9
    algebraCarrierRole
    "9 as NonaryTruth algebra carrier"
    false
    refl

phaseThreeReading : NumberRoleReading
phaseThreeReading =
  mkNumberRoleReading
    numeral3
    phaseTopologicalRole
    "3 as phase/origin reading"
    false
    refl

phaseEightReading : NumberRoleReading
phaseEightReading =
  mkNumberRoleReading
    numeral8
    phaseTopologicalRole
    "8 as void-gap phase reading"
    false
    refl

phaseElevenReading : NumberRoleReading
phaseElevenReading =
  mkNumberRoleReading
    numeral11
    phaseTopologicalRole
    "11 as second-revolution manifold reading"
    false
    refl

quotientTenReading : NumberRoleReading
quotientTenReading =
  mkNumberRoleReading
    numeral10
    quotientTransportRole
    "10 as mod-9 overflow trace rather than plain 1"
    false
    refl

factorSevenReading : NumberRoleReading
factorSevenReading =
  mkNumberRoleReading
    numeral7
    factorCoordinateRole
    "7 as prime-axis/factor coordinate"
    false
    refl

narrativeSevenReading : NumberRoleReading
narrativeSevenReading =
  mkNumberRoleReading
    numeral7
    narrativeMnemonicRole
    "7 as maximum-tension mnemonic"
    false
    refl

numberRoleNoPromotionBoundary :
  (reading : NumberRoleReading) →
  promotesWithoutBridge reading ≡ false
numberRoleNoPromotionBoundary reading =
  promotesWithoutBridgeIsFalse reading
