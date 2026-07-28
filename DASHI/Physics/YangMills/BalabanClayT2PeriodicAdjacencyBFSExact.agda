module DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using
  (SignedAxis4; signedDirectionEnumeration; signedDirectionEnumerationComplete)
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal periodic adjacency and the canonical BFS/DFS proof boundary.
-- This is repository-specific finite graph theory; no external source is
-- expected for the rooted-shell injection or decoder.
------------------------------------------------------------------------

lastCyclic : ∀ {n} → CyclicIndex (suc n)
lastCyclic {zero} = zeroᵢ
lastCyclic {suc n} = sucᵢ lastCyclic

cyclicSuccessor : ∀ {n} → CyclicIndex (suc n) → CyclicIndex (suc n)
cyclicSuccessor {zero} zeroᵢ = zeroᵢ
cyclicSuccessor {suc n} zeroᵢ = sucᵢ zeroᵢ
cyclicSuccessor {suc n} (sucᵢ index)
  with cyclicIndexDecidableEquality index lastCyclic
... | yes _ = zeroᵢ
... | no _ = sucᵢ (cyclicSuccessor index)

cyclicPredecessor : ∀ {n} → CyclicIndex (suc n) → CyclicIndex (suc n)
cyclicPredecessor {zero} zeroᵢ = zeroᵢ
cyclicPredecessor {suc n} zeroᵢ = sucᵢ lastCyclic
cyclicPredecessor {suc n} (sucᵢ zeroᵢ) = zeroᵢ
cyclicPredecessor {suc n} (sucᵢ (sucᵢ index)) =
  sucᵢ (cyclicPredecessor (sucᵢ index))

stepCoordinate : ∀ {n} → Bool → CyclicIndex (suc n) → CyclicIndex (suc n)
stepCoordinate false = cyclicPredecessor
stepCoordinate true = cyclicSuccessor

updateAxis :
  ∀ {n} → Axis4 →
  (CyclicIndex (suc n) → CyclicIndex (suc n)) →
  Periodic.PeriodicBlock n → Periodic.PeriodicBlock n
updateAxis zeroᵢ update (pair (pair c0 c1) (pair c2 c3)) =
  pair (pair (update c0) c1) (pair c2 c3)
updateAxis (sucᵢ zeroᵢ) update (pair (pair c0 c1) (pair c2 c3)) =
  pair (pair c0 (update c1)) (pair c2 c3)
updateAxis (sucᵢ (sucᵢ zeroᵢ)) update (pair (pair c0 c1) (pair c2 c3)) =
  pair (pair c0 c1) (pair (update c2) c3)
updateAxis (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) update
  (pair (pair c0 c1) (pair c2 c3)) =
  pair (pair c0 c1) (pair c2 (update c3))

signedStep :
  ∀ {n} → Periodic.PeriodicBlock n → SignedAxis4 → Periodic.PeriodicBlock n
signedStep block (pair axis orientation) =
  updateAxis axis (stepCoordinate orientation) block

data ReachedByDirection {n}
    (left right : Periodic.PeriodicBlock n) :
    List SignedAxis4 → Set where
  reachedHere : ∀ {direction directions} →
    signedStep left direction ≡ right →
    ReachedByDirection left right (direction ∷ directions)
  reachedThere : ∀ {direction directions} →
    ReachedByDirection left right directions →
    ReachedByDirection left right (direction ∷ directions)

PeriodicNearestNeighbour :
  ∀ {n} → Periodic.PeriodicBlock n → Periodic.PeriodicBlock n → Set
PeriodicNearestNeighbour left right =
  ReachedByDirection left right signedDirectionEnumeration

directionFromWitness :
  ∀ {n left right directions} →
  ReachedByDirection {n} left right directions → SignedAxis4
directionFromWitness (reachedHere {direction = direction} equality) = direction
directionFromWitness (reachedThere witness) = directionFromWitness witness

directionWitnessExact :
  ∀ {n left right directions}
    (witness : ReachedByDirection {n} left right directions) →
  signedStep left (directionFromWitness witness) ≡ right
directionWitnessExact (reachedHere equality) = equality
directionWitnessExact (reachedThere witness) = directionWitnessExact witness

reachedByDirectionDecidable :
  ∀ {n} (left right : Periodic.PeriodicBlock n) directions →
  Dec (ReachedByDirection left right directions)
reachedByDirectionDecidable left right [] = no (λ ())
reachedByDirectionDecidable {n} left right (direction ∷ directions)
  with periodicTorus4DecidableEquality (suc n) (signedStep left direction) right
     | reachedByDirectionDecidable left right directions
... | yes equality | tailDecision = yes (reachedHere equality)
... | no notHere | yes tail = yes (reachedThere tail)
... | no notHere | no notThere = no λ where
    (reachedHere equality) → notHere equality
    (reachedThere witness) → notThere witness

nearestNeighbourDecidable :
  ∀ {n} (left right : Periodic.PeriodicBlock n) →
  Dec (PeriodicNearestNeighbour left right)
nearestNeighbourDecidable left right =
  reachedByDirectionDecidable left right signedDirectionEnumeration

defaultDirection : SignedAxis4
defaultDirection = pair zeroᵢ false

directionOfBlocks :
  ∀ {n} → Periodic.PeriodicBlock n → Periodic.PeriodicBlock n → SignedAxis4
directionOfBlocks left right with nearestNeighbourDecidable left right
... | yes witness = directionFromWitness witness
... | no _ = defaultDirection

directionReconstructsBlocks :
  ∀ {n} (left right : Periodic.PeriodicBlock n) →
  PeriodicNearestNeighbour left right →
  signedStep left (directionOfBlocks left right) ≡ right
directionReconstructsBlocks left right adjacent
  with nearestNeighbourDecidable left right
... | yes witness = directionWitnessExact witness
... | no notAdjacent = emptyEliminate (notAdjacent adjacent)
  where
  emptyEliminate : ∀ {A : Set} → Empty → A
  emptyEliminate ()

signedStepAdjacent :
  ∀ {n} (block : Periodic.PeriodicBlock n) direction →
  PeriodicNearestNeighbour block (signedStep block direction)
signedStepAdjacent block direction =
  fromEnumeration (signedDirectionEnumerationComplete direction)
  where
  fromEnumeration :
    ∀ {directions} → direction ∈ directions →
    ReachedByDirection block (signedStep block direction) directions
  fromEnumeration here = reachedHere refl
  fromEnumeration (there membership) = reachedThere (fromEnumeration membership)

periodicAdjacencyData : ∀ n → Periodic.PeriodicAdjacencyData n
periodicAdjacencyData n = record
  { nearestNeighbour = PeriodicNearestNeighbour
  ; nearestNeighbourDecidable = λ left right →
      Dec (PeriodicNearestNeighbour left right)
  ; signedStep = signedStep
  ; directionOfAdjacent = directionOfBlocks
  ; signedStepAdjacent = signedStepAdjacent
  ; directionReconstructsAdjacent = λ left right adjacent →
      directionReconstructsBlocks left right adjacent
  }

------------------------------------------------------------------------
-- Connected physical polymers carry the invariant excluded by raw block lists.
------------------------------------------------------------------------

data PeriodicPath {n} :
    Periodic.PeriodicBlock n → Periodic.PeriodicBlock n → Set where
  pathStop : ∀ {block} → PeriodicPath block block
  pathStep : ∀ {left middle right} →
    PeriodicNearestNeighbour left middle →
    PeriodicPath middle right →
    PeriodicPath left right

pathLength : ∀ {n left right} → PeriodicPath {n} left right → Nat
pathLength pathStop = zero
pathLength (pathStep adjacent rest) = suc (pathLength rest)

record ConnectedPeriodicPolymer (n : Nat) : Set₁ where
  field
    blocks : Periodic.PeriodicPolymer n
    nonempty : Set
    duplicateFree : Set
    membership : Periodic.PeriodicBlock n → Set
    membershipAgreesWithList : ∀ block → Set
    connected : ∀ left right →
      membership left → membership right → PeriodicPath left right

open ConnectedPeriodicPolymer public

record ShortestPathCertificate {n}
    (polymer : ConnectedPeriodicPolymer n)
    (root block : Periodic.PeriodicBlock n) : Set₁ where
  field
    path : PeriodicPath root block
    insidePolymer : Set
    minimal : ∀ candidate → Set

open ShortestPathCertificate public

record CertifiedPeriodicBreadthFirstData
    (n : Nat) (polymer : ConnectedPeriodicPolymer n) : Set₁ where
  field
    root : Periodic.PeriodicBlock n
    rootBelongs : membership polymer root
    rootIsLeast : ∀ block → membership polymer block → Set

    shortestPath : ∀ block → membership polymer block →
      ShortestPathCertificate polymer root block

    distance : Periodic.PeriodicBlock n → Nat
    distanceDefinition : ∀ block belongs →
      distance block ≡ pathLength (path (shortestPath block belongs))

    rootDistanceZero : distance root ≡ zero

    parent : Periodic.PeriodicBlock n → Periodic.PeriodicBlock n
    everyNonRootHasCloserNeighbour : ∀ block → membership polymer block → Set
    parentBelongs : ∀ block → membership polymer block → Set
    parentAdjacent : ∀ block → membership polymer block → Set
    parentDistanceStrictlyDecreases : ∀ block → membership polymer block → Set
    parentLeastAmongCloserNeighbours : ∀ block → membership polymer block → Set

open CertifiedPeriodicBreadthFirstData public

record CertifiedPeriodicTreeDecoder
    (n : Nat) (polymer : ConnectedPeriodicPolymer n)
    (bfs : CertifiedPeriodicBreadthFirstData n polymer) : Set₁ where
  field
    parentTree : Periodic.PeriodicTree n
    parentTreeEdgesExact : Set
    parentChainStrictlyDecreasesDistance : Set
    parentChainTerminatesAtRoot : Set
    parentTreeAcyclic : Set
    parentTreeConnected : Set
    parentTreeCoversExactly : Set

    depthFirstTour : Periodic.PeriodicTraversal n
    depthFirstUsesSignedAxisOrder : Set
    depthFirstVisitsEveryBlock : Set
    depthFirstTraversesEachTreeEdgeTwice : Set

    traversalWord : List SignedAxis4
    traversalWordRecordsForwardAndBacktracking : Set

    decodePolymer :
      Periodic.PeriodicBlock n → List SignedAxis4 → Periodic.PeriodicPolymer n
    decoderReplaysEveryStep : Set
    decodeCanonicalTrace :
      decodePolymer (root bfs) traversalWord ≡ blocks polymer
    rootRecoverableAfterDecode : Set

open CertifiedPeriodicTreeDecoder public

periodicSuccessorPredecessorDefinitionLevel : ProofLevel
periodicSuccessorPredecessorDefinitionLevel = machineChecked

periodicSignedStepDefinitionLevel : ProofLevel
periodicSignedStepDefinitionLevel = machineChecked

periodicAdjacencyDecisionLevel : ProofLevel
periodicAdjacencyDecisionLevel = machineChecked

periodicConnectedPolymerCarrierLevel : ProofLevel
periodicConnectedPolymerCarrierLevel = machineChecked

periodicBFSShortestPathProofInputsLevel : ProofLevel
periodicBFSShortestPathProofInputsLevel = conditional

periodicDFSDecoderProofInputsLevel : ProofLevel
periodicDFSDecoderProofInputsLevel = conditional
