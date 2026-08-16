module DASHI.Topology.TernaryPantsFrontierExact where

------------------------------------------------------------------------
-- ARBITRARY-DEPTH FRONTIER OF THE TERNARY PANTS TREE
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Bridge

PantsPath : Nat → Set
PantsPath n = Vec Bridge.BranchSlot n

addressToPantsPath : ∀ {n : Nat} → U369.Address n → PantsPath n
addressToPantsPath vnil = vnil
addressToPantsPath (digit vcons rest) =
  Bridge.slotOfDigit digit vcons addressToPantsPath rest

pantsPathToAddress : ∀ {n : Nat} → PantsPath n → U369.Address n
pantsPathToAddress vnil = vnil
pantsPathToAddress (slot vcons rest) =
  Bridge.digitOfSlot slot vcons pantsPathToAddress rest

addressPantsPathRoundTrip :
  ∀ {n : Nat} (address : U369.Address n) →
  pantsPathToAddress (addressToPantsPath address) ≡ address
addressPantsPathRoundTrip vnil = refl
addressPantsPathRoundTrip (digit vcons rest)
  rewrite Bridge.digitSlotRoundTrip digit
        | addressPantsPathRoundTrip rest = refl

pantsPathAddressRoundTrip :
  ∀ {n : Nat} (path : PantsPath n) →
  addressToPantsPath (pantsPathToAddress path) ≡ path
pantsPathAddressRoundTrip vnil = refl
pantsPathAddressRoundTrip (slot vcons rest)
  rewrite Bridge.slotDigitRoundTrip slot
        | pantsPathAddressRoundTrip rest = refl

record FrontierEquivalence (n : Nat) : Set where
  constructor frontierEquivalence
  field
    cylinderToPants : U369.Address n → PantsPath n
    pantsToCylinder : PantsPath n → U369.Address n
    cylinderRoundTrip :
      (address : U369.Address n) →
      pantsToCylinder (cylinderToPants address) ≡ address
    pantsRoundTrip :
      (path : PantsPath n) →
      cylinderToPants (pantsToCylinder path) ≡ path

open FrontierEquivalence public

canonicalFrontierEquivalence : (n : Nat) → FrontierEquivalence n
canonicalFrontierEquivalence n =
  frontierEquivalence
    addressToPantsPath
    pantsPathToAddress
    addressPantsPathRoundTrip
    pantsPathAddressRoundTrip

appendSlot :
  ∀ {n : Nat} → PantsPath n → Bridge.BranchSlot → PantsPath (suc n)
appendSlot vnil slot = slot vcons vnil
appendSlot (head vcons tail) slot = head vcons appendSlot tail slot

addressToPantsPathAppend :
  ∀ {n : Nat}
    (address : U369.Address n)
    (digit : U369.Digit369) →
  addressToPantsPath (Bridge.appendDigit address digit)
  ≡ appendSlot (addressToPantsPath address) (Bridge.slotOfDigit digit)
addressToPantsPathAppend vnil digit = refl
addressToPantsPathAppend (head vcons tail) digit
  rewrite addressToPantsPathAppend tail digit = refl

pantsPathToAddressAppend :
  ∀ {n : Nat}
    (path : PantsPath n)
    (slot : Bridge.BranchSlot) →
  pantsPathToAddress (appendSlot path slot)
  ≡ Bridge.appendDigit (pantsPathToAddress path) (Bridge.digitOfSlot slot)
pantsPathToAddressAppend vnil slot = refl
pantsPathToAddressAppend (head vcons tail) slot
  rewrite pantsPathToAddressAppend tail slot = refl

depthThreeCylinder : U369.Address 3
depthThreeCylinder =
  U369.digit3 vcons U369.digit9 vcons U369.digit6 vcons vnil

depthThreePantsPath : PantsPath 3
depthThreePantsPath =
  Bridge.slot3 vcons Bridge.slot9 vcons Bridge.slot6 vcons vnil

depthThreeCylinderMapsToPants :
  addressToPantsPath depthThreeCylinder ≡ depthThreePantsPath
depthThreeCylinderMapsToPants = refl

depthThreePantsMapsToCylinder :
  pantsPathToAddress depthThreePantsPath ≡ depthThreeCylinder
depthThreePantsMapsToCylinder = refl

record TernaryPantsFrontierBoundary : Set where
  constructor ternaryPantsFrontierBoundary
  field
    allFiniteDepthsIndexed : Bool
    allFiniteDepthsIndexedIsTrue : allFiniteDepthsIndexed ≡ true
    refinementCommutesWithPathExtension : Bool
    refinementCommutesWithPathExtensionIsTrue :
      refinementCommutesWithPathExtension ≡ true
    collisionFreeR3EmbeddingConstructed : Bool
    collisionFreeR3EmbeddingConstructedIsFalse :
      collisionFreeR3EmbeddingConstructed ≡ false
    smoothPantsThickeningConstructed : Bool
    smoothPantsThickeningConstructedIsFalse :
      smoothPantsThickeningConstructed ≡ false

open TernaryPantsFrontierBoundary public

canonicalTernaryPantsFrontierBoundary : TernaryPantsFrontierBoundary
canonicalTernaryPantsFrontierBoundary =
  ternaryPantsFrontierBoundary
    true refl
    true refl
    false refl
    false refl
