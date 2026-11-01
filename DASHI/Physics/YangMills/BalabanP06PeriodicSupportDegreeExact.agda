module DASHI.Physics.YangMills.BalabanP06PeriodicSupportDegreeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel, "Graph Theory", Graduate Texts in Mathematics 173,
-- 5th edition, Springer, 2017. DOI: 10.1007/978-3-662-53622-3.
--
-- The actual theorem below is repository-specific finite lattice geometry:
-- every nearest-neighbour block in the four-dimensional periodic support graph
-- is reached by one of the eight signed coordinate directions.  Hence the
-- duplicate-free neighbour count is at most eight, including the degenerate
-- small-torus cases where several directions may reach the same block.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.List.Base using (length)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (_∈_; map; mapMembership)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4; signedDirectionEnumeration;
    signedDirectionEnumerationComplete; eight;
    signedDirectionEnumerationLength)
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact
  using (lengthMap)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayT2PeriodicTraversalDecoderExact as Decoder
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTraversalGeometryReuseExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPhysicalAdjacencyAndBadReachExact as Physical
import DASHI.Physics.YangMills.GraphCombinatorics as Graph
open import DASHI.Physics.YangMills.CompactLieProofLevel

periodicNeighbourEnumeration :
  ∀ {n} → Periodic.PeriodicBlock n → List (Periodic.PeriodicBlock n)
periodicNeighbourEnumeration block =
  map (Adjacency.signedStep block) signedDirectionEnumeration

periodicNeighbourEnumerationLength :
  ∀ {n} (block : Periodic.PeriodicBlock n) →
  length (periodicNeighbourEnumeration block) ≡ eight
periodicNeighbourEnumerationLength block =
  trans
    (lengthMap (Adjacency.signedStep block) signedDirectionEnumeration)
    signedDirectionEnumerationLength

forwardNeighbourEnumerated :
  ∀ {n} {left right : Periodic.PeriodicBlock n} →
  Adjacency.PeriodicNearestNeighbour left right →
  right ∈ periodicNeighbourEnumeration left
forwardNeighbourEnumerated {left = left} witness =
  subst
    (λ target → target ∈ periodicNeighbourEnumeration left)
    (Adjacency.directionWitnessExact witness)
    (mapMembership
      (Adjacency.signedStep left)
      (signedDirectionEnumerationComplete
        (Adjacency.directionFromWitness witness)))

reverseStepReconstructs :
  ∀ {n} {left right : Periodic.PeriodicBlock n} →
  (witness : Adjacency.PeriodicNearestNeighbour right left) →
  Adjacency.signedStep left
    (Decoder.reverseDirection (Adjacency.directionFromWitness witness))
  ≡ right
reverseStepReconstructs {n} {left} {right} witness =
  let direction = Adjacency.directionFromWitness witness
      forward = Adjacency.directionWitnessExact witness
      inverse = Geometry.periodicDirectionInverseLaw n
      roundTrip =
        Decoder.DirectionInverseLaw.forwardThenReverse
          inverse right direction
  in trans
       (cong
         (λ source →
           Adjacency.signedStep source
             (Decoder.reverseDirection direction))
         (sym forward))
       roundTrip

backwardNeighbourEnumerated :
  ∀ {n} {left right : Periodic.PeriodicBlock n} →
  Adjacency.PeriodicNearestNeighbour right left →
  right ∈ periodicNeighbourEnumeration left
backwardNeighbourEnumerated {left = left} witness =
  subst
    (λ target → target ∈ periodicNeighbourEnumeration left)
    (reverseStepReconstructs witness)
    (mapMembership
      (Adjacency.signedStep left)
      (signedDirectionEnumerationComplete
        (Decoder.reverseDirection
          (Adjacency.directionFromWitness witness))))

physicalNeighbourEnumerated :
  ∀ {n} {left right : Periodic.PeriodicBlock n} →
  Physical.PeriodicPhysicalAdjacent left right →
  right ∈ periodicNeighbourEnumeration left
physicalNeighbourEnumerated (inj₁ forward) =
  forwardNeighbourEnumerated forward
physicalNeighbourEnumerated (inj₂ backward) =
  backwardNeighbourEnumerated backward

periodicDistinctNeighbourCount :
  ∀ {n} → Periodic.PeriodicBlock n → Nat
periodicDistinctNeighbourCount block =
  Graph.countUnique (periodicNeighbourEnumeration block)

periodicDistinctNeighbourCountBelowEight :
  ∀ {n} (block : Periodic.PeriodicBlock n) →
  periodicDistinctNeighbourCount block ≤ eight
periodicDistinctNeighbourCountBelowEight block =
  subst
    (λ count → periodicDistinctNeighbourCount block ≤ count)
    (periodicNeighbourEnumerationLength block)
    (Graph.countUnique-bound (periodicNeighbourEnumeration block))

record PeriodicSupportDegreeCertificate (n : Nat) : Set₁ where
  field
    neighbours : Periodic.PeriodicBlock n → List (Periodic.PeriodicBlock n)

    everyPhysicalNeighbourEnumerated :
      ∀ {left right} →
      Physical.PeriodicPhysicalAdjacent left right →
      right ∈ neighbours left

    enumerationLengthEight :
      ∀ block → length (neighbours block) ≡ eight

    distinctNeighbourCount : Periodic.PeriodicBlock n → Nat
    distinctNeighbourCountDefinition :
      ∀ block →
      distinctNeighbourCount block
        ≡ Graph.countUnique (neighbours block)

    degreeAtMostEight :
      ∀ block → distinctNeighbourCount block ≤ eight

open PeriodicSupportDegreeCertificate public

periodicSupportDegreeCertificate :
  ∀ n → PeriodicSupportDegreeCertificate n
periodicSupportDegreeCertificate n = record
  { neighbours = periodicNeighbourEnumeration
  ; everyPhysicalNeighbourEnumerated = physicalNeighbourEnumerated
  ; enumerationLengthEight = periodicNeighbourEnumerationLength
  ; distinctNeighbourCount = periodicDistinctNeighbourCount
  ; distinctNeighbourCountDefinition = λ block → refl
  ; degreeAtMostEight = periodicDistinctNeighbourCountBelowEight
  }

periodicSupportNeighbourEnumerationLevel : ProofLevel
periodicSupportNeighbourEnumerationLevel = machineChecked

periodicSupportDegreeEightLevel : ProofLevel
periodicSupportDegreeEightLevel = machineChecked

-- GraphCombinatorics.countNeighbors is still an abstract compatibility socket.
-- The only remaining adapter field is its identification with the concrete
-- duplicate-free count above; the physical degree theorem itself is closed.
abstractGraphCountNeighborsIdentificationLevel : ProofLevel
abstractGraphCountNeighborsIdentificationLevel = conditional
