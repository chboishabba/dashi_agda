module DASHI.Biology.BH4SpatialConnectivityCirculationExact where

------------------------------------------------------------------------
-- Explicit location and circulation permissions for source-backed BH4
-- states. Total chemical inventory is not a transport graph.
-- Reuse existing finite electro-diffusive transfer/conservation owner.
-- No claim that a two-compartment quantum has a physiological rate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Biology.BH4SystemStateExact as BH4
import DASHI.Biology.BH4CompartmentKineticStateExact as Kinetics
import DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact as Transport
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

record ContextIndexedCirculation : Set₁ where
  field
    Location : Set
    compartmentAt : Location → BH4.Compartment
    regionReference : Location → String
    -- Circulation is directed. An anatomical or vascular edge does
    -- not imply its reverse or a measurable transport coefficient.
    PermittedFlow : Location → Location → Set
    originalFlowAuthority : (a b : Location) →
      PermittedFlow a b → String
    originalSpecimen : String
    timeReference : String
    sourceReference : String
    selectedPNP : PNP.ElectrodiffusionApplicationReceipt
    localBH4State : Location → Kinetics.BH4ParameterEvidence

open ContextIndexedCirculation public

-- The same two-compartment inventory can have different reachable
-- target abundance solely because their directed connection differs.
transportIfConnected :
  Bool → Transport.IonPairState → Transport.IonPairState
transportIfConnected false state = state
transportIfConnected true state =
  Transport.transport Transport.leftToRight state

transportIfConnectedConservesTotal :
  (connected : Bool) (state : Transport.IonPairState) →
  Transport.totalAmount (transportIfConnected connected state)
    ≡ Transport.totalAmount state
transportIfConnectedConservesTotal false state = refl
transportIfConnectedConservesTotal true state =
  Transport.transportConservesAmount Transport.leftToRight state

originInventory : Transport.IonPairState
originInventory = Transport.ionPair 1 0

disconnectedExample connectedExample : Transport.IonPairState
disconnectedExample = transportIfConnected false originInventory
connectedExample = transportIfConnected true originInventory

totalIdenticalDespiteDifferentFlow :
  Transport.totalAmount disconnectedExample
    ≡ Transport.totalAmount connectedExample
totalIdenticalDespiteDifferentFlow = refl

targetWithoutFlowZero : Transport.right disconnectedExample ≡ 0
targetWithoutFlowZero = refl

targetWithFlowOne : Transport.right connectedExample ≡ 1
targetWithFlowOne = refl

zeroNotOne : 0 ≡ 1 → ⊥
zeroNotOne ()

-- No future observer of GLOBAL amount alone predicts local delivered
-- material when allowed transport edges vary.
globalInventoryCannotDetermineLocalDelivery :
  (predict : Nat → Nat)
  (factor : (connected : Bool) →
    Transport.right (transportIfConnected connected originInventory)
      ≡ predict
          (Transport.totalAmount
            (transportIfConnected connected originInventory))) →
  ⊥
globalInventoryCannotDetermineLocalDelivery predict factor =
  zeroNotOne
    (trans
      (sym targetWithoutFlowZero)
      (trans (factor false)
        (trans
          (cong predict totalIdenticalDespiteDifferentFlow)
          (trans (sym (factor true)) targetWithFlowOne))))

-- Signed ions retain a second charge conservation invariant
-- for the same fixed valence under any permitted finite transfer.
transportIfConnectedConservesCharge :
  (valenceMagnitude : Nat)
  (connected : Bool) (state : Transport.IonPairState) →
  Transport.chargeMagnitude valenceMagnitude
    (transportIfConnected connected state)
    ≡ Transport.chargeMagnitude valenceMagnitude state
transportIfConnectedConservesCharge valenceMagnitude false state = refl
transportIfConnectedConservesCharge valenceMagnitude true state =
  Transport.transportConservesChargeMagnitude
    valenceMagnitude Transport.leftToRight state

------------------------------------------------------------------------
-- Connectivity can encode directed distal delivery, not only cellular
-- nearest-neighbour diffusion. This is the generic path semantics;
-- physiological pressure/flow resistance remains source-owned.
------------------------------------------------------------------------

data FlowPath
  {Location : Set}
  (Flow : Location → Location → Set) :
  Location → Location → Set where
  here : (x : Location) → FlowPath Flow x x
  thenFlow : ∀ {a b c} →
    Flow a b → FlowPath Flow b c → FlowPath Flow a c

data IllustrativeRegion : Set where
  circulationSource : IllustrativeRegion
  deliveredTarget : IllustrativeRegion

data IllustrativeDirectedVessel :
  IllustrativeRegion → IllustrativeRegion → Set where
  sourceFeedsTarget :
    IllustrativeDirectedVessel circulationSource deliveredTarget

forwardDeliveryPath :
  FlowPath IllustrativeDirectedVessel
    circulationSource deliveredTarget
forwardDeliveryPath =
  thenFlow sourceFeedsTarget (here deliveredTarget)

reversePathNotProvided :
  FlowPath IllustrativeDirectedVessel
    deliveredTarget circulationSource → ⊥
reversePathNotProvided ()

-- Under source-qualified physiological conditions flow might reverse,
-- branch, or be regulated. The toy's absence of reverse flow is not
-- a universal theorem about blood vessels or transport physiology.
