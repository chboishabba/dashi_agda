module DASHI.Physics.YangMills.BalabanClayGate4StrongBFSParentCertificateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Algorithmic provenance.
--
-- Edward F. Moore,
-- "The Shortest Path Through a Maze", Proceedings of the International
-- Symposium on the Theory of Switching, Part II (1959), 285--292.
-- No DOI recorded.
--
-- This is a proof-bearing replacement for older Set-valued BFS labels. Once a
-- concrete distance and parent map satisfy the previous-layer equation, parent
-- chains strictly descend in distance and therefore cannot contain a nonempty
-- cycle. Distance-zero uniqueness makes every parent chain terminate at the
-- root, and physical parent adjacency reverses that chain into an explicit
-- root-to-vertex path of exactly the assigned distance.
------------------------------------------------------------------------

data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

sucInjective : ∀ {left right} → suc left ≡ suc right → left ≡ right
sucInjective refl = refl

plusSucShift : ∀ left right → left + suc right ≡ suc left + right
plusSucShift zero right = refl
plusSucShift (suc left) right = cong suc (plusSucShift left right)

noPositiveAddFixedPoint : ∀ positiveTail value →
  value ≡ suc positiveTail + value → Empty
noPositiveAddFixedPoint positiveTail zero ()
noPositiveAddFixedPoint positiveTail (suc value) equality =
  noPositiveAddFixedPoint positiveTail value
    (trans
      (sucInjective equality)
      (plusSucShift positiveTail value))

infix 4 _≤N_
data _≤N_ : Nat → Nat → Set where
  zero≤N : ∀ {right} → zero ≤N right
  suc≤N : ∀ {left right} → left ≤N right → suc left ≤N suc right

≤N-reflexive : ∀ value → value ≤N value
≤N-reflexive zero = zero≤N
≤N-reflexive (suc value) = suc≤N (≤N-reflexive value)

record StrongBFSParentCertificate (Vertex : Set) : Set₁ where
  field
    root : Vertex
    InGraph : Vertex → Set
    Adjacent : Vertex → Vertex → Set
    IsNonRoot : Vertex → Set

    distance : Vertex → Nat
    parent : Vertex → Vertex

    rootInGraph : InGraph root
    rootDistanceZero : distance root ≡ zero
    distanceZeroImpliesRoot : ∀ vertex → InGraph vertex →
      distance vertex ≡ zero → vertex ≡ root
    positiveDistanceIsNonRoot : ∀ vertex distanceTail → InGraph vertex →
      distance vertex ≡ suc distanceTail → IsNonRoot vertex

    parentInGraph : ∀ vertex → IsNonRoot vertex → InGraph (parent vertex)
    parentAdjacent : ∀ vertex → IsNonRoot vertex →
      Adjacent (parent vertex) vertex

    -- The parent lies in the immediately preceding BFS layer.
    parentDistanceStep : ∀ vertex → IsNonRoot vertex →
      suc (distance (parent vertex)) ≡ distance vertex

open StrongBFSParentCertificate public

data ParentChain
    {Vertex : Set}
    (certificate : StrongBFSParentCertificate Vertex) :
    Vertex → Vertex → Nat → Set where
  chainZero : ∀ {vertex} → ParentChain certificate vertex vertex zero
  chainStep : ∀ {vertex terminal length} →
    IsNonRoot certificate vertex →
    ParentChain certificate (parent certificate vertex) terminal length →
    ParentChain certificate vertex terminal (suc length)

parentChainDistanceExact :
  ∀ {Vertex}
    {certificate : StrongBFSParentCertificate Vertex}
    {start terminal length} →
  ParentChain certificate start terminal length →
  distance certificate start
  ≡ length + distance certificate terminal
parentChainDistanceExact chainZero = refl
parentChainDistanceExact {certificate = certificate}
  (chainStep {vertex = vertex} nonRoot rest) =
  trans
    (sym (parentDistanceStep certificate vertex nonRoot))
    (cong suc (parentChainDistanceExact rest))

nonemptyParentChainCannotCycle :
  ∀ {Vertex}
    {certificate : StrongBFSParentCertificate Vertex}
    {vertex length} →
  ParentChain certificate vertex vertex (suc length) →
  Empty
nonemptyParentChainCannotCycle {certificate = certificate} {vertex = vertex}
  {length = length} chain =
  noPositiveAddFixedPoint length (distance certificate vertex)
    (parentChainDistanceExact chain)

parentCannotEqualChild :
  ∀ {Vertex}
    (certificate : StrongBFSParentCertificate Vertex)
    vertex → IsNonRoot certificate vertex →
  Not (parent certificate vertex ≡ vertex)
parentCannotEqualChild certificate vertex nonRoot equality =
  nonemptyParentChainCannotCycle
    (subst (λ p → ParentChain certificate vertex p (suc zero)) equality (chainStep nonRoot chainZero))

parentChainToRootAtDistance :
  ∀ {Vertex}
    (certificate : StrongBFSParentCertificate Vertex)
    vertex → InGraph certificate vertex →
    (selectedDistance : Nat) →
    distance certificate vertex ≡ selectedDistance →
    ParentChain certificate vertex (root certificate) selectedDistance
parentChainToRootAtDistance certificate vertex inGraph zero distanceIsZero =
  subst
    (λ terminal → ParentChain certificate vertex terminal zero)
    (distanceZeroImpliesRoot certificate vertex inGraph distanceIsZero)
    chainZero
parentChainToRootAtDistance certificate vertex inGraph (suc distanceTail)
  distanceIsSuccessor =
  let nonRoot = positiveDistanceIsNonRoot certificate
        vertex distanceTail inGraph distanceIsSuccessor
      parentGraph = parentInGraph certificate vertex nonRoot
      parentDistance = sucInjective
        (trans
          (parentDistanceStep certificate vertex nonRoot)
          distanceIsSuccessor)
      rest = parentChainToRootAtDistance certificate
        (parent certificate vertex) parentGraph distanceTail parentDistance
  in chainStep nonRoot rest

parentChainToRoot :
  ∀ {Vertex}
    (certificate : StrongBFSParentCertificate Vertex)
    vertex → InGraph certificate vertex →
  ParentChain certificate vertex (root certificate)
    (distance certificate vertex)
parentChainToRoot certificate vertex inGraph =
  parentChainToRootAtDistance certificate vertex inGraph
    (distance certificate vertex) refl

data RootPath
    {Vertex : Set}
    (certificate : StrongBFSParentCertificate Vertex) :
    Vertex → Nat → Set where
  rootPath : RootPath certificate (root certificate) zero
  extendPath : ∀ {parentVertex child length} →
    RootPath certificate parentVertex length →
    Adjacent certificate parentVertex child →
    RootPath certificate child (suc length)

parentChainGivesRootPath :
  ∀ {Vertex}
    {certificate : StrongBFSParentCertificate Vertex}
    {vertex length} →
  ParentChain certificate vertex (root certificate) length →
  RootPath certificate vertex length
parentChainGivesRootPath rootChain@chainZero = rootPath
parentChainGivesRootPath {certificate = certificate}
  (chainStep {vertex = vertex} nonRoot rest) =
  extendPath
    (parentChainGivesRootPath rest)
    (parentAdjacent certificate vertex nonRoot)

rootPathAtAssignedDistance :
  ∀ {Vertex}
    (certificate : StrongBFSParentCertificate Vertex)
    vertex → InGraph certificate vertex →
  RootPath certificate vertex (distance certificate vertex)
rootPathAtAssignedDistance certificate vertex inGraph =
  parentChainGivesRootPath (parentChainToRoot certificate vertex inGraph)

record StrongBFSShortestPathCertificate
    {Vertex : Set}
    (parentCertificate : StrongBFSParentCertificate Vertex) : Set₁ where
  field
    distanceLowerBoundForEveryPath : ∀ {vertex pathLength} →
      RootPath parentCertificate vertex pathLength →
      distance parentCertificate vertex ≤N pathLength

open StrongBFSShortestPathCertificate public

shortestPathRealized :
  ∀ {Vertex}
    {parentCertificate : StrongBFSParentCertificate Vertex}
    (certificate : StrongBFSShortestPathCertificate parentCertificate)
    vertex → InGraph parentCertificate vertex →
  RootPath parentCertificate vertex (distance parentCertificate vertex)
shortestPathRealized {parentCertificate = parentCertificate}
  certificate vertex inGraph =
  rootPathAtAssignedDistance parentCertificate vertex inGraph

assignedDistanceIsMinimal :
  ∀ {Vertex}
    {parentCertificate : StrongBFSParentCertificate Vertex}
    (certificate : StrongBFSShortestPathCertificate parentCertificate)
    {vertex pathLength} →
  RootPath parentCertificate vertex pathLength →
  distance parentCertificate vertex ≤N pathLength
assignedDistanceIsMinimal certificate =
  distanceLowerBoundForEveryPath certificate

strongBFSParentCertificateLevel : ProofLevel
strongBFSParentCertificateLevel = machineChecked

parentChainDistanceLevel : ProofLevel
parentChainDistanceLevel = machineChecked

parentAcyclicityFromDistanceDescentLevel : ProofLevel
parentAcyclicityFromDistanceDescentLevel = machineChecked

parentConnectivityFromDistanceDescentLevel : ProofLevel
parentConnectivityFromDistanceDescentLevel = machineChecked

rootPathAtAssignedDistanceLevel : ProofLevel
rootPathAtAssignedDistanceLevel = machineChecked

strongShortestPathCertificateLevel : ProofLevel
strongShortestPathCertificateLevel = machineChecked

physicalPeriodicDistanceStepInputsLevel : ProofLevel
physicalPeriodicDistanceStepInputsLevel = conditional

physicalPeriodicDistanceZeroUniquenessInputsLevel : ProofLevel
physicalPeriodicDistanceZeroUniquenessInputsLevel = conditional

physicalPeriodicShortestPathMinimalityInputsLevel : ProofLevel
physicalPeriodicShortestPathMinimalityInputsLevel = conditional
