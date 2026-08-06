module DASHI.Physics.Foundations.TriToBiTransportExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Product probability mass and additive transported mass are different
-- operations.  The finite witnesses make the distinction executable.

jointProductMass : Nat → Nat → Nat
jointProductMass left right = left * right

additiveIncomingMass : Nat → Nat → Nat → Nat
additiveIncomingMass first second third = first + second + third

productMassWitness : jointProductMass 2 3 ≡ 6
productMassWitness = refl

additiveMassWitness : additiveIncomingMass 2 3 4 ≡ 9
additiveMassWitness = refl

productMassIsNotAdditiveMass :
  jointProductMass 2 3 ≡ additiveIncomingMass 2 3 4 → ⊥
productMassIsNotAdditiveMass ()

------------------------------------------------------------------------
-- Denominator-six conservative routing table.  Every incoming unit is routed
-- to exactly one of the two outputs; the route may depend on a coupled
-- junction state.

data IncomingLeg : Set where
  legOne : IncomingLeg
  legTwo : IncomingLeg
  legThree : IncomingLeg

data OutgoingWaist : Set where
  waistA : OutgoingWaist
  waistB : OutgoingWaist

data JunctionState : Set where
  balancedRouting : JunctionState
  tiltedRouting : JunctionState

inputMass : IncomingLeg → Nat
inputMass legOne = 1
inputMass legTwo = 2
inputMass legThree = 3

route : JunctionState → IncomingLeg → OutgoingWaist
route balancedRouting legOne = waistA
route balancedRouting legTwo = waistB
route balancedRouting legThree = waistA
route tiltedRouting legOne = waistB
route tiltedRouting legTwo = waistA
route tiltedRouting legThree = waistB

routedMass : JunctionState → OutgoingWaist → Nat
routedMass balancedRouting waistA = inputMass legOne + inputMass legThree
routedMass balancedRouting waistB = inputMass legTwo
routedMass tiltedRouting waistA = inputMass legTwo
routedMass tiltedRouting waistB = inputMass legOne + inputMass legThree

balancedRoutingConserves :
  routedMass balancedRouting waistA
  +
  routedMass balancedRouting waistB
  ≡
  additiveIncomingMass
    (inputMass legOne)
    (inputMass legTwo)
    (inputMass legThree)
balancedRoutingConserves = refl

tiltedRoutingConserves :
  routedMass tiltedRouting waistA
  +
  routedMass tiltedRouting waistB
  ≡
  additiveIncomingMass
    (inputMass legOne)
    (inputMass legTwo)
    (inputMass legThree)
tiltedRoutingConserves = refl

routingIsStateDependent :
  route balancedRouting legOne ≡ route tiltedRouting legOne → ⊥
routingIsStateDependent ()

------------------------------------------------------------------------
-- Junction storage and declared loss channels.

record MassBalance : Set where
  constructor massBalance
  field
    incoming : Nat
    storedBefore : Nat
    outgoing : Nat
    storedAfter : Nat
    lost : Nat

open MassBalance public

canonicalTemporalBalance : MassBalance
canonicalTemporalBalance = massBalance 6 1 5 2 0

canonicalTemporalBalanceCloses :
  incoming canonicalTemporalBalance
  +
  storedBefore canonicalTemporalBalance
  ≡
  outgoing canonicalTemporalBalance
  +
  storedAfter canonicalTemporalBalance
  +
  lost canonicalTemporalBalance
canonicalTemporalBalanceCloses = refl

junctionResidual : MassBalance → Nat
junctionResidual balance =
  storedAfter balance + lost balance

canonicalResidualIsTwo :
  junctionResidual canonicalTemporalBalance ≡ 2
canonicalResidualIsTwo = refl

record TriToBiTransportBoundary : Set where
  constructor triToBiTransportBoundary
  field
    productPushforwardAutomaticallyConservesAdditiveFlux : Bool
    productPushforwardAutomaticallyConservesAdditiveFluxIsFalse :
      productPushforwardAutomaticallyConservesAdditiveFlux ≡ false

    unrestrictedGELUIsProbabilityWeight : Bool
    unrestrictedGELUIsProbabilityWeightIsFalse :
      unrestrictedGELUIsProbabilityWeight ≡ false

    silentRenormalisationPreservesResidualSemantics : Bool
    silentRenormalisationPreservesResidualSemanticsIsFalse :
      silentRenormalisationPreservesResidualSemantics ≡ false

open TriToBiTransportBoundary public

canonicalTriToBiTransportBoundary : TriToBiTransportBoundary
canonicalTriToBiTransportBoundary =
  triToBiTransportBoundary false refl false refl false refl
