module DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathWordExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

------------------------------------------------------------------------
-- Exact conversion of a proof-bearing periodic nearest-neighbour path into
-- the literal signed-axis word consumed by lattice holonomy.
--
-- This is repository-specific finite graph theory.  Every path constructor
-- carries the adjacency proof needed by `directionReconstructsBlocks`; hence
-- the word is executable and its endpoint theorem is proved by induction, not
-- retained as a path-selection assumption.
------------------------------------------------------------------------

pathDirections :
  ∀ {n left right} →
  Adjacency.PeriodicPath {n} left right → List SignedAxis4
pathDirections Adjacency.pathStop = []
pathDirections (Adjacency.pathStep {left = left} {middle = middle}
    adjacent rest) =
  Adjacency.directionOfBlocks left middle ∷ pathDirections rest

pathDirectionsReachEndpoint :
  ∀ {n left right}
    (path : Adjacency.PeriodicPath {n} left right) →
  Bond.walk left (pathDirections path) ≡ right
pathDirectionsReachEndpoint Adjacency.pathStop = refl
pathDirectionsReachEndpoint {right = right}
    (Adjacency.pathStep {left = left} {middle = middle}
      adjacent rest) =
  subst
    (λ firstStep →
      Bond.walk firstStep (pathDirections rest) ≡ right)
    (Adjacency.directionReconstructsBlocks left middle adjacent)
    (pathDirectionsReachEndpoint rest)

pathWordLength :
  ∀ {n left right}
    (path : Adjacency.PeriodicPath {n} left right) → Nat
pathWordLength path = BondPathLength path
  where
  BondPathLength :
    ∀ {n left right} →
    Adjacency.PeriodicPath {n} left right → Nat
  BondPathLength Adjacency.pathStop = zero
  BondPathLength (Adjacency.pathStep adjacent rest) =
    suc (BondPathLength rest)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

pathDirectionsLengthExact :
  ∀ {n left right}
    (path : Adjacency.PeriodicPath {n} left right) →
  listLength (pathDirections path) ≡ pathWordLength path
pathDirectionsLengthExact Adjacency.pathStop = refl
pathDirectionsLengthExact (Adjacency.pathStep adjacent rest) =
  cong suc (pathDirectionsLengthExact rest)

record CertifiedContourWord
    (n : Nat)
    (start finish : Periodic.PeriodicBlock n) : Set where
  field
    path : Adjacency.PeriodicPath start finish

  directions : List SignedAxis4
  directions = pathDirections path

  endpointExact : Bond.walk start directions ≡ finish
  endpointExact = pathDirectionsReachEndpoint path

open CertifiedContourWord public

periodicPathToSignedWordLevel : ProofLevel
periodicPathToSignedWordLevel = computed

periodicPathWordEndpointLevel : ProofLevel
periodicPathWordEndpointLevel = machineChecked

periodicPathWordLengthLevel : ProofLevel
periodicPathWordLengthLevel = machineChecked
