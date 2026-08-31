module DASHI.Core.ThreeChannelC3EquivarianceGateExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- THREE-CHANNEL C3 EQUIVARIANCE GATE
--
-- Repository-native bridge extracted from the exact C3 / Base369 / Monster
-- symmetry work.  This module owns only the generic theorem shape.
--
-- Having three channels is not enough to infer a C3 representation.  A genuine
-- cyclic bridge must supply an order-three action on the literal carrier and
-- equivariance of every downstream map that is supposed to respect it.
------------------------------------------------------------------------

record OrderThreeAction (Carrier : Set) : Set₁ where
  field
    rotate : Carrier → Carrier
    rotateCubed : (x : Carrier) → rotate (rotate (rotate x)) ≡ x

open OrderThreeAction public

record EquivariantMap
    {A B : Set}
    (actionA : OrderThreeAction A)
    (actionB : OrderThreeAction B)
    (map : A → B) : Set where
  field
    intertwines :
      (x : A) →
      map (rotate actionA x) ≡ rotate actionB (map x)

open EquivariantMap public

record ThreeChannelC3Weld
    (Input Mid Output : Set) : Set₁ where
  field
    inputAction : OrderThreeAction Input
    midAction : OrderThreeAction Mid
    outputAction : OrderThreeAction Output

    forward : Input → Mid
    consumer : Mid → Output

    forwardEquivariant : EquivariantMap inputAction midAction forward
    consumerEquivariant : EquivariantMap midAction outputAction consumer

open ThreeChannelC3Weld public

------------------------------------------------------------------------
-- Exact anti-promotion boundary.
------------------------------------------------------------------------

data C3EvidenceStage : Set where
  threeNamedChannels
  candidateCyclicPermutation
  orderThreeActionProved
  forwardEquivarianceProved
  consumerEquivarianceProved
  c3WeldClosed
  : C3EvidenceStage

threeChannelsNotAction : threeNamedChannels ≡ orderThreeActionProved → ⊥
threeChannelsNotAction ()

orderThreeNotConsumerEquivariance :
  orderThreeActionProved ≡ consumerEquivarianceProved → ⊥
orderThreeNotConsumerEquivariance ()

record ThreeChannelC3Boundary : Set where
  constructor threeChannelC3Boundary
  field
    threeChannelsAutomaticallyC3 : Bool
    threeChannelsAutomaticallyC3IsFalse :
      threeChannelsAutomaticallyC3 ≡ false
    exactOrderThreeActionCanBeUseful : Bool
    exactOrderThreeActionCanBeUsefulIsTrue :
      exactOrderThreeActionCanBeUseful ≡ true
    equivarianceRequiredBeforeFourierTransport : Bool
    equivarianceRequiredBeforeFourierTransportIsTrue :
      equivarianceRequiredBeforeFourierTransport ≡ true
    monsterOrBase369RepresentationTransfersByAnalogy : Bool
    monsterOrBase369RepresentationTransfersByAnalogyIsFalse :
      monsterOrBase369RepresentationTransfersByAnalogy ≡ false

canonicalThreeChannelC3Boundary : ThreeChannelC3Boundary
canonicalThreeChannelC3Boundary =
  threeChannelC3Boundary false refl true refl true refl false refl
