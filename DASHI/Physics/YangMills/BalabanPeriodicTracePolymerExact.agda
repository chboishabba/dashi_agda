module DASHI.Physics.YangMills.BalabanPeriodicTracePolymerExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalHaloOriginExact using
  (cyclicPredecessor)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
open import DASHI.Physics.YangMills.BalabanConcreteRootedTracePolymer

------------------------------------------------------------------------
-- A periodic trace is itself a connected polymer carrier.  This removes the
-- need to enumerate arbitrary finite subsets before the KP overcount: every
-- trace comes with a literal nearest-neighbour walk and is counted by the exact
-- 8^n word theorem.
------------------------------------------------------------------------

updateAxisCoordinate :
  ∀ {L} → Axis4 → (CyclicIndex L → CyclicIndex L) →
  periodicTorus4Definition L → periodicTorus4Definition L
updateAxisCoordinate zeroᵢ update
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (update x0) x1) (pair x2 x3)
updateAxisCoordinate (sucᵢ zeroᵢ) update
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (update x1)) (pair x2 x3)
updateAxisCoordinate (sucᵢ (sucᵢ zeroᵢ)) update
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (update x2) x3)
updateAxisCoordinate (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) update
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (update x3))

moveSignedDirection :
  ∀ {L} → SignedAxis4 →
  periodicTorus4Definition L → periodicTorus4Definition L
moveSignedDirection (pair axis false) =
  updateAxisCoordinate axis cyclicSuccessor
moveSignedDirection (pair axis true) =
  updateAxisCoordinate axis cyclicPredecessor

walkTrace :
  ∀ {L} → periodicTorus4Definition L →
  List SignedAxis4 → List (periodicTorus4Definition L)
walkTrace root [] = root ∷ []
walkTrace root (direction ∷ directions) =
  root ∷ walkTrace (moveSignedDirection direction root) directions

walkTraceLength :
  ∀ {L} root directions →
  length (walkTrace {L} root directions) ≡ suc (length directions)
walkTraceLength root [] = refl
walkTraceLength root (direction ∷ directions) =
  cong suc (walkTraceLength (moveSignedDirection direction root) directions)

record NearestNeighbourStep {L : Nat}
    (left right : periodicTorus4Definition L) : Set where
  constructor nearestNeighbourStep
  field
    direction : SignedAxis4
    followsDirection : moveSignedDirection direction left ≡ right

open NearestNeighbourStep public

data ConnectedTrace {L : Nat} :
    List (periodicTorus4Definition L) → Set where
  singletonConnected : ∀ site → ConnectedTrace (site ∷ [])
  extendConnected : ∀ {left right rest} →
    NearestNeighbourStep left right →
    ConnectedTrace (right ∷ rest) →
    ConnectedTrace (left ∷ right ∷ rest)

walkTraceConnected :
  ∀ {L} root directions →
  ConnectedTrace (walkTrace {L} root directions)
walkTraceConnected root [] = singletonConnected root
walkTraceConnected root (direction ∷ directions) =
  extendConnected
    (nearestNeighbourStep direction refl)
    (walkTraceConnected (moveSignedDirection direction root) directions)

record PeriodicTracePolymer (L : Nat) : Set where
  constructor periodicTracePolymer
  field
    root : periodicTorus4Definition L
    directions : List SignedAxis4

open PeriodicTracePolymer public

tracePolymerSupport :
  ∀ {L} → PeriodicTracePolymer L →
  List (periodicTorus4Definition L)
tracePolymerSupport polymer = walkTrace (root polymer) (directions polymer)

tracePolymerSupportConnected :
  ∀ {L} (polymer : PeriodicTracePolymer L) →
  ConnectedTrace (tracePolymerSupport polymer)
tracePolymerSupportConnected polymer =
  walkTraceConnected (root polymer) (directions polymer)

tracePolymerTraversalSize : ∀ {L} → PeriodicTracePolymer L → Nat
tracePolymerTraversalSize polymer = length (directions polymer)

RootedPeriodicTracePolymer : Nat → periodicTorus4Definition four → Set
RootedPeriodicTracePolymer L rootSite = List SignedAxis4

rootedPeriodicTraceEncoding :
  ∀ {L} {rootSite : periodicTorus4Definition L} →
  PhysicalPolymerTraceEncoding (List SignedAxis4)
rootedPeriodicTraceEncoding = rootedTracePolymerEncoding

rootedPeriodicTraceCount : ∀ size →
  length (allSignedWords size) ≡ pow8 size
rootedPeriodicTraceCount = allSignedWordsLength

periodicTracePolymerCarrierLevel : ProofLevel
periodicTracePolymerCarrierLevel = machineChecked

periodicTracePolymerConnectednessLevel : ProofLevel
periodicTracePolymerConnectednessLevel = machineChecked

periodicTracePolymerEntropyLevel : ProofLevel
periodicTracePolymerEntropyLevel = machineChecked

oneStepRGProducesTraceIndexedActivitiesLevel : ProofLevel
oneStepRGProducesTraceIndexedActivitiesLevel = conditional
