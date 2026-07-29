module DASHI.Physics.YangMills.BalabanClayGate4PeriodicExecutableBFSInstantiationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSAlgorithmExact as BFS

------------------------------------------------------------------------
-- The generic executable visited-set BFS is instantiated with DASHI's literal
-- finite four-torus enumeration, decidable equality and decidable nearest-
-- neighbour relation.  This closes the executable graph layer.  Shortest-path,
-- parent-tree and decoder correctness remain proof obligations over this run.
------------------------------------------------------------------------

decisionBool : ∀ {P : Set} → Dec P → Bool
decisionBool (yes _) = true
decisionBool (no _) = false

decisionTrueGivesWitness :
  ∀ {P : Set} (decision : Dec P) → decisionBool decision ≡ true → P
decisionTrueGivesWitness (yes witness) refl = witness
decisionTrueGivesWitness (no _) ()

witnessGivesDecisionTrue :
  ∀ {P : Set} (decision : Dec P) → P → decisionBool decision ≡ true
witnessGivesDecisionTrue (yes _) witness = refl
witnessGivesDecisionTrue (no notP) witness = emptyEliminate (notP witness)
  where
  emptyEliminate : ∀ {A : Set} → Empty → A
  emptyEliminate ()

periodicBlockEqualBool :
  ∀ {n} → Periodic.PeriodicBlock n → Periodic.PeriodicBlock n → Bool
periodicBlockEqualBool {n} left right =
  decisionBool (periodicTorus4DecidableEquality (suc n) left right)

periodicAdjacentBool :
  ∀ {n} → Periodic.PeriodicBlock n → Periodic.PeriodicBlock n → Bool
periodicAdjacentBool left right =
  decisionBool (Adjacency.nearestNeighbourDecidable left right)

periodicExecutableGraph :
  ∀ n → BFS.FiniteDecidableGraph (Periodic.PeriodicBlock n)
periodicExecutableGraph n = record
  { BFS.FiniteDecidableGraph.vertices =
      elements (periodicTorus4Finite (suc n))
  ; BFS.FiniteDecidableGraph.equalBool = periodicBlockEqualBool
  ; BFS.FiniteDecidableGraph.adjacentBool = periodicAdjacentBool
  }

periodicBlockEqualBoolSound :
  ∀ {n} left right → periodicBlockEqualBool {n} left right ≡ true → left ≡ right
periodicBlockEqualBoolSound {n} left right =
  decisionTrueGivesWitness
    (periodicTorus4DecidableEquality (suc n) left right)

periodicBlockEqualBoolComplete :
  ∀ {n} left right → left ≡ right → periodicBlockEqualBool {n} left right ≡ true
periodicBlockEqualBoolComplete {n} left right =
  witnessGivesDecisionTrue
    (periodicTorus4DecidableEquality (suc n) left right)

periodicAdjacentBoolSound :
  ∀ {n} left right → periodicAdjacentBool {n} left right ≡ true →
  Adjacency.PeriodicNearestNeighbour left right
periodicAdjacentBoolSound left right =
  decisionTrueGivesWitness (Adjacency.nearestNeighbourDecidable left right)

periodicAdjacentBoolComplete :
  ∀ {n} left right → Adjacency.PeriodicNearestNeighbour left right →
  periodicAdjacentBool {n} left right ≡ true
periodicAdjacentBoolComplete left right =
  witnessGivesDecisionTrue (Adjacency.nearestNeighbourDecidable left right)

periodicBFSState :
  ∀ {n} → Periodic.PeriodicBlock n → BFS.BFSState (Periodic.PeriodicBlock n)
periodicBFSState {n} root = BFS.runFiniteBFS (periodicExecutableGraph n) root

periodicVertexEnumerationComplete :
  ∀ {n} (block : Periodic.PeriodicBlock n) →
  block ∈ BFS.vertices (periodicExecutableGraph n)
periodicVertexEnumerationComplete {n} block =
  complete (periodicTorus4Finite (suc n)) block

periodicExecutableGraphLevel : ProofLevel
periodicExecutableGraphLevel = machineChecked

periodicEqualityBooleanReflectionLevel : ProofLevel
periodicEqualityBooleanReflectionLevel = machineChecked

periodicAdjacencyBooleanReflectionLevel : ProofLevel
periodicAdjacencyBooleanReflectionLevel = machineChecked

periodicFuelBoundedBFSExecutionLevel : ProofLevel
periodicFuelBoundedBFSExecutionLevel = machineChecked

periodicBFSShortestPathInvariantInputsLevel : ProofLevel
periodicBFSShortestPathInvariantInputsLevel = conditional

periodicBFSParentTreeCorrectnessInputsLevel : ProofLevel
periodicBFSParentTreeCorrectnessInputsLevel = conditional
