module DASHI.Physics.YangMills.BalabanClayGate4PeriodicPhysicalAdjacencyAndBadReachExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ) renaming (_,_ to _,Σ_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Empty; Dec; yes; no; elements; complete; periodicTorus4Finite;
    periodicTorus4DecidableEquality; _∈_)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as PeriodicAdjacency
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4FiniteEnlargementCollarOwnershipExact as Collar
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicReachCollarEnumerationExact as Reach

------------------------------------------------------------------------
-- Provenance and relationship.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I. The Basic Step of the R Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- The physical nearest-neighbour graph and finite search below are exact DASHI
-- lattice combinatorics.  Bałaban owns the large-field component architecture;
-- no analytic R-operation estimate is inferred from this graph construction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Literal undirected periodic nearest-neighbour adjacency.
------------------------------------------------------------------------

PeriodicPhysicalAdjacent :
  ∀ {n} → Periodic.PeriodicBlock n → Periodic.PeriodicBlock n → Set
PeriodicPhysicalAdjacent left right =
  PeriodicAdjacency.PeriodicNearestNeighbour left right
  ⊎ PeriodicAdjacency.PeriodicNearestNeighbour right left

periodicPhysicalAdjacentDecidable :
  ∀ {n} (left right : Periodic.PeriodicBlock n) →
  Dec (PeriodicPhysicalAdjacent left right)
periodicPhysicalAdjacentDecidable left right
  with PeriodicAdjacency.nearestNeighbourDecidable left right
     | PeriodicAdjacency.nearestNeighbourDecidable right left
... | yes forward | backwardDecision = yes (inj₁ forward)
... | no notForward | yes backward = yes (inj₂ backward)
... | no notForward | no notBackward = no reject
  where
  reject : PeriodicPhysicalAdjacent left right → Empty
  reject (inj₁ forward) = notForward forward
  reject (inj₂ backward) = notBackward backward

periodicPhysicalAdjacentSymmetric :
  ∀ {n} {left right : Periodic.PeriodicBlock n} →
  PeriodicPhysicalAdjacent left right →
  PeriodicPhysicalAdjacent right left
periodicPhysicalAdjacentSymmetric (inj₁ forward) = inj₂ forward
periodicPhysicalAdjacentSymmetric (inj₂ backward) = inj₁ backward

periodicDirectedAdjacencyIncluded :
  ∀ {n} {left right : Periodic.PeriodicBlock n} →
  PeriodicAdjacency.PeriodicNearestNeighbour left right →
  PeriodicPhysicalAdjacent left right
periodicDirectedAdjacencyIncluded = inj₁

periodicPhysicalFiniteReachCarrier :
  ∀ n → Reach.FiniteReachCarrier (Periodic.PeriodicBlock n)
periodicPhysicalFiniteReachCarrier n = record
  { allBlocks =
      elements (periodicTorus4Finite (suc n))
  ; allBlocksComplete =
      complete (periodicTorus4Finite (suc n))
  ; equalDecidable =
      periodicTorus4DecidableEquality (suc n)
  ; Adjacent = PeriodicPhysicalAdjacent
  ; adjacentDecidable =
      periodicPhysicalAdjacentDecidable
  }

periodicPhysicalSymmetricReachCarrier :
  ∀ n → Reach.SymmetricFiniteReachCarrier (Periodic.PeriodicBlock n)
periodicPhysicalSymmetricReachCarrier n = record
  { finiteReach =
      periodicPhysicalFiniteReachCarrier n
  ; adjacentSymmetric =
      periodicPhysicalAdjacentSymmetric
  }

------------------------------------------------------------------------
-- Literal Wilson bad geometry on the physical periodic adjacency.
------------------------------------------------------------------------

literalPeriodicPhysicalBadGeometry :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) →
  Geometry.BadBlockGeometry Configuration Gauge (Periodic.PeriodicBlock n)
literalPeriodicPhysicalBadGeometry dataSet scale = record
  { transform = Wilson.transform dataSet
  ; Adjacent = PeriodicPhysicalAdjacent
  ; adjacentSymmetric =
      periodicPhysicalAdjacentSymmetric
  ; BadBlock = λ configuration block →
      Wilson.LargeFieldBlock dataSet scale configuration block
  ; badBlockDecidable =
      Wilson.largeFieldBlockDecidable dataSet scale
  ; badGaugeForward = λ gauge configuration block →
      Wilson.largeFieldBlockGaugeForward dataSet gauge scale configuration block
  ; badGaugeBackward = λ gauge configuration block →
      Wilson.largeFieldBlockGaugeBackward dataSet gauge scale configuration block
  }

record BadPhysicalEdge
    {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) (configuration : Configuration)
    (left right : Periodic.PeriodicBlock n) : Set where
  constructor badEdge
  field
    leftBad : Wilson.LargeFieldBlock dataSet scale configuration left
    adjacent : PeriodicPhysicalAdjacent left right
    rightBad : Wilson.LargeFieldBlock dataSet scale configuration right

open BadPhysicalEdge public

badPhysicalEdgeDecidable :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    scale configuration left right →
  Dec (BadPhysicalEdge dataSet scale configuration left right)
badPhysicalEdgeDecidable dataSet scale configuration left right
  with Wilson.largeFieldBlockDecidable dataSet scale configuration left
     | periodicPhysicalAdjacentDecidable left right
     | Wilson.largeFieldBlockDecidable dataSet scale configuration right
... | yes leftLarge | yes adjacentProof | yes rightLarge =
      yes (badEdge leftLarge adjacentProof rightLarge)
... | no notLeft | adjacentDecision | rightDecision =
      no (λ edge → notLeft (leftBad edge))
... | yes leftLarge | no notAdjacent | rightDecision =
      no (λ edge → notAdjacent (adjacent edge))
... | yes leftLarge | yes adjacentProof | no notRight =
      no (λ edge → notRight (rightBad edge))

badPhysicalReachCarrier :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) (configuration : Configuration) →
  Reach.FiniteReachCarrier (Periodic.PeriodicBlock n)
badPhysicalReachCarrier {n = n} dataSet scale configuration = record
  { allBlocks =
      elements (periodicTorus4Finite (suc n))
  ; allBlocksComplete =
      complete (periodicTorus4Finite (suc n))
  ; equalDecidable =
      periodicTorus4DecidableEquality (suc n)
  ; Adjacent =
      BadPhysicalEdge dataSet scale configuration
  ; adjacentDecidable =
      badPhysicalEdgeDecidable dataSet scale configuration
  }

boundedBadComponentBlocks :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) (configuration : Configuration) →
  Nat → Periodic.PeriodicBlock n → List (Periodic.PeriodicBlock n)
boundedBadComponentBlocks dataSet scale configuration radius seed =
  Reach.enumerateReachWithin
    (badPhysicalReachCarrier dataSet scale configuration) radius seed

appendReachOne :
  ∀ {Block : Set} {Adjacent : Block → Block → Set}
    {radius start middle finish} →
  Collar.ReachWithin Adjacent radius start middle →
  Adjacent middle finish →
  Collar.ReachWithin Adjacent (suc radius) start finish
appendReachOne Collar.stay edge = Collar.step edge Collar.stay
appendReachOne (Collar.step first rest) edge =
  Collar.step first (appendReachOne rest edge)

boundedBadReachToPath :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) (configuration : Configuration)
    {radius start finish} →
  Wilson.LargeFieldBlock dataSet scale configuration start →
  Collar.ReachWithin
    (BadPhysicalEdge dataSet scale configuration) radius start finish →
  Geometry.BadPath
    (literalPeriodicPhysicalBadGeometry dataSet scale)
    configuration start finish
boundedBadReachToPath dataSet scale configuration startBad Collar.stay =
  Geometry.root startBad
boundedBadReachToPath dataSet scale configuration startBad
  (Collar.step edge rest) =
  Geometry.appendBadPath
    (Geometry.step
      (Geometry.root (leftBad edge))
      (adjacent edge)
      (rightBad edge))
    (boundedBadReachToPath dataSet scale configuration
      (rightBad edge) rest)

badPathToBoundedReach :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) (configuration : Configuration)
    {start finish} →
  Geometry.BadPath
    (literalPeriodicPhysicalBadGeometry dataSet scale)
    configuration start finish →
  Σ Nat (λ radius →
    Collar.ReachWithin
      (BadPhysicalEdge dataSet scale configuration) radius start finish)
badPathToBoundedReach dataSet scale configuration (Geometry.root bad) =
  zero ,Σ Collar.stay
badPathToBoundedReach dataSet scale configuration
  (Geometry.step path adjacentProof nextBad)
  with badPathToBoundedReach dataSet scale configuration path
... | radius ,Σ reach =
  suc radius ,Σ
    appendReachOne reach
      (badEdge (Geometry.pathEndBad path) adjacentProof nextBad)

boundedBadComponentEnumerationSound :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) (configuration : Configuration)
    (radius : Nat) (seed block : Periodic.PeriodicBlock n) →
  (seedBad : Wilson.LargeFieldBlock dataSet scale configuration seed) →
  block ∈ boundedBadComponentBlocks dataSet scale configuration radius seed →
  Geometry.Contains
    (Geometry.badComponentOf
      {dataSet = literalPeriodicPhysicalBadGeometry dataSet scale}
      seedBad)
    block
boundedBadComponentEnumerationSound dataSet scale configuration radius seed block
  seedBad membership =
  boundedBadReachToPath dataSet scale configuration seedBad
    (Reach.enumerateReachWithinSound
      (badPhysicalReachCarrier dataSet scale configuration)
      radius seed membership)

record EventuallyEnumerated
    {Block : Set} (enumeration : Nat → List Block) (block : Block) : Set where
  constructor eventually
  field
    radius : Nat
    member : block ∈ enumeration radius

open EventuallyEnumerated public

everyBadComponentMemberEventuallyEnumerated :
  ∀ {n Scale Configuration Gauge Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (Periodic.PeriodicBlock n) Plaquette)
    (scale : Scale) (configuration : Configuration)
    (seed block : Periodic.PeriodicBlock n)
    (seedBad : Wilson.LargeFieldBlock dataSet scale configuration seed) →
  Geometry.Contains
    (Geometry.badComponentOf
      {dataSet = literalPeriodicPhysicalBadGeometry dataSet scale}
      seedBad)
    block →
  EventuallyEnumerated
    (λ radius → boundedBadComponentBlocks
      dataSet scale configuration radius seed)
    block
everyBadComponentMemberEventuallyEnumerated dataSet scale configuration
  seed block seedBad path
  with badPathToBoundedReach dataSet scale configuration path
... | radius ,Σ reach = eventually radius
  (Reach.enumerateReachWithinComplete
    (badPhysicalReachCarrier dataSet scale configuration)
    radius seed block reach)

periodicPhysicalAdjacencyInstanceLevel : ProofLevel
periodicPhysicalAdjacencyInstanceLevel = machineChecked

periodicPhysicalFiniteReachCarrierLevel : ProofLevel
periodicPhysicalFiniteReachCarrierLevel = machineChecked

literalPeriodicPhysicalBadGeometryLevel : ProofLevel
literalPeriodicPhysicalBadGeometryLevel = machineChecked

boundedBadComponentEnumerationLevel : ProofLevel
boundedBadComponentEnumerationLevel = machineChecked

everyBadComponentMemberEventuallyEnumeratedLevel : ProofLevel
everyBadComponentMemberEventuallyEnumeratedLevel = machineChecked

-- A single duplicate-free list containing the whole component needs a uniform
-- simple-path bound or a terminating visited-set saturation theorem.  This file
-- deliberately proves eventual finite enumeration without installing that
-- finite-graph theorem as an unconstrained field.
uniformDuplicateFreeBadComponentEnumerationLevel : ProofLevel
uniformDuplicateFreeBadComponentEnumerationLevel = conditional
