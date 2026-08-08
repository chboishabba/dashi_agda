module DASHI.Moonshine.EulerMonsterMeaningSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.GradedRepresentation as Graded

------------------------------------------------------------------------
-- Sources and authority scope
--
-- Leonhard Euler, Methodus inveniendi lineas curvas maximi minimive
-- proprietate gaudentes (1744); no DOI assigned.
--
-- Richard E. Borcherds, Monstrous Moonshine and Monstrous Lie
-- Superalgebras, Inventiones Mathematicae 109 (1992), 405-444,
-- DOI 10.1007/BF01232032.
--
-- The module separates several standard uses of the name Euler.  It does not
-- infer an Euler characteristic interpretation of a Moonshine coefficient.
------------------------------------------------------------------------

data EulerMeaning : Set where
  eulerLagrangeStationarity : EulerMeaning
  eulerCharacteristic : EulerMeaning
  eulerPoincareAlternatingSum : EulerMeaning
  gradedEulerSupertrace : EulerMeaning
  moonshineOrdinaryGradedTrace : EulerMeaning

record EulerLagrangeDatum : Set₁ where
  constructor eulerLagrangeDatum
  field
    Configuration Variation : Set
    selectedConfiguration : Configuration
    firstVariation : Configuration → Variation → Nat
    admissible : Variation → Set
    stationaryOnAdmissible :
      (v : Variation) → admissible v →
      firstVariation selectedConfiguration v ≡ 0

------------------------------------------------------------------------
-- Euler characteristic and supertrace are represented division-free as even
-- and odd totals.  Their signed value is the formal difference even - odd;
-- equality to zero is expressed by equality of the two natural totals.
------------------------------------------------------------------------

record SignedNaturalDifference : Set where
  constructor signedNaturalDifference
  field
    positivePart negativePart : Nat

open SignedNaturalDifference public

record FiniteEulerCharacteristic : Set where
  constructor finiteEulerCharacteristic
  field
    evenDimension oddDimension : Nat
    characteristic : SignedNaturalDifference
    characteristicExact :
      characteristic ≡ signedNaturalDifference evenDimension oddDimension

record ThreeTermEulerPoincareData : Set where
  constructor threeTermEulerPoincareData
  field
    c0Dimension c1Dimension c2Dimension : Nat
    evenTotal oddTotal : Nat
    evenExact : c0Dimension + c2Dimension ≡ evenTotal
    oddExact : c1Dimension ≡ oddTotal

oneTwoOneComplex : ThreeTermEulerPoincareData
oneTwoOneComplex = threeTermEulerPoincareData 1 2 1 2 2 refl refl

oneTwoOneEulerCharacteristicZero :
  ThreeTermEulerPoincareData.evenTotal oneTwoOneComplex
  ≡ ThreeTermEulerPoincareData.oddTotal oneTwoOneComplex
oneTwoOneEulerCharacteristicZero = refl

record FiniteGradedSupertrace : Set where
  constructor finiteGradedSupertrace
  field
    evenTrace oddTrace : Nat
    supertrace : SignedNaturalDifference
    supertraceExact :
      supertrace ≡ signedNaturalDifference evenTrace oddTrace

------------------------------------------------------------------------
-- An ordinary graded trace does not alternate signs unless an independent
-- parity grading has been supplied.
------------------------------------------------------------------------

record OrdinaryGradedTraceCoefficient : Set where
  constructor ordinaryGradedTraceCoefficient
  field
    grade : Nat
    dimension : Nat
    identityTrace : Nat
    identityTraceIsDimension : identityTrace ≡ dimension

moonshineWeightTwoCoefficient : OrdinaryGradedTraceCoefficient
moonshineWeightTwoCoefficient =
  ordinaryGradedTraceCoefficient 2 196884 196884 refl

moonshineCoefficientIs196884 :
  OrdinaryGradedTraceCoefficient.identityTrace moonshineWeightTwoCoefficient
  ≡ 196884
moonshineCoefficientIs196884 = refl

monsterNontrivialPartPlusInvariant : 196883 + 1 ≡ 196884
monsterNontrivialPartPlusInvariant = refl

------------------------------------------------------------------------
-- A genuine Euler-Moonshine theorem would need a parity-graded complex,
-- square-zero differential, a Monster action commuting with that differential,
-- and a proved equality between the resulting equivariant supertrace and the
-- desired graded trace.  Cardinal arithmetic cannot supply these fields.
------------------------------------------------------------------------

record EquivariantEulerMoonshineBridge : Set₂ where
  constructor equivariantEulerMoonshineBridge
  field
    GroupElement ChainState : Set
    group : Graded.Group GroupElement
    zeroState : ChainState
    parity : ChainState → Bool
    differential : ChainState → ChainState
    differentialSquaresToZero :
      (x : ChainState) → differential (differential x) ≡ zeroState
    action : GroupElement → ChainState → ChainState
    actionCommutesWithDifferential :
      (g : GroupElement) (x : ChainState) →
      action g (differential x) ≡ differential (action g x)
    equivariantSupertrace : GroupElement → Nat
    moonshineTrace : GroupElement → Nat
    bridgeEquality :
      (g : GroupElement) → equivariantSupertrace g ≡ moonshineTrace g

record EulerMonsterAuthorityBoundary : Set where
  constructor eulerMonsterAuthorityBoundary
  field
    eulerLagrangeIsEulerCharacteristic : Bool
    eulerLagrangeIsEulerCharacteristicIsFalse :
      eulerLagrangeIsEulerCharacteristic ≡ false
    ordinaryMoonshineTraceIsAlternatingSupertrace : Bool
    ordinaryMoonshineTraceIsAlternatingSupertraceIsFalse :
      ordinaryMoonshineTraceIsAlternatingSupertrace ≡ false
    coefficient196884IsEulerCharacteristicClaimed : Bool
    coefficient196884IsEulerCharacteristicClaimedIsFalse :
      coefficient196884IsEulerCharacteristicClaimed ≡ false
    equivariantEulerMoonshineBridgeConstructed : Bool
    equivariantEulerMoonshineBridgeConstructedIsFalse :
      equivariantEulerMoonshineBridgeConstructed ≡ false

canonicalEulerMonsterAuthorityBoundary : EulerMonsterAuthorityBoundary
canonicalEulerMonsterAuthorityBoundary =
  eulerMonsterAuthorityBoundary false refl false refl false refl false refl
