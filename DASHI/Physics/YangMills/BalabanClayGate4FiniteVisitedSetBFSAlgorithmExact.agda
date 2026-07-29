module DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSAlgorithmExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Algorithmic provenance.
--
-- Edward F. Moore,
-- "The Shortest Path Through a Maze", Proceedings of the International
-- Symposium on the Theory of Switching, Part II (1959), 285--292.
-- No DOI recorded.
--
-- The construction is the standard finite breadth-first layering algorithm:
-- V0 contains the root; V(i+1) contains the as-yet undiscovered vertices with
-- an edge to Vi.  Every new vertex receives the first (hence canonical for the
-- supplied frontier order) adjacent parent in the preceding layer.
--
-- This module implements the executable fuel-bounded algorithm.  Shortest-path,
-- exact-spanning and least-parent correctness for the physical periodic graph
-- remain separate proof obligations; they are not inferred merely from the
-- standard name "BFS".
------------------------------------------------------------------------

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (left ∷ rest) right = left ∷ append rest right

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ rest) = suc (length rest)

not : Bool → Bool
not false = true
not true = false

and : Bool → Bool → Bool
and false _ = false
and true right = right

or : Bool → Bool → Bool
or false right = right
or true _ = true

record FiniteDecidableGraph (Vertex : Set) : Set₁ where
  field
    vertices : List Vertex
    equalBool : Vertex → Vertex → Bool
    adjacentBool : Vertex → Vertex → Bool

open FiniteDecidableGraph public

memberBool :
  ∀ {Vertex} → FiniteDecidableGraph Vertex → Vertex → List Vertex → Bool
memberBool graph vertex [] = false
memberBool graph vertex (candidate ∷ rest) with equalBool graph vertex candidate
... | true = true
... | false = memberBool graph vertex rest

removeMembers :
  ∀ {Vertex} → FiniteDecidableGraph Vertex → List Vertex → List Vertex → List Vertex
removeMembers graph removed [] = []
removeMembers graph removed (vertex ∷ rest)
  with memberBool graph vertex removed
... | true = removeMembers graph removed rest
... | false = vertex ∷ removeMembers graph removed rest

firstAdjacentParent :
  ∀ {Vertex} → FiniteDecidableGraph Vertex → Vertex → List Vertex → Maybe Vertex
firstAdjacentParent graph child [] = nothing
firstAdjacentParent graph child (parent ∷ rest)
  with adjacentBool graph parent child
... | true = just parent
... | false = firstAdjacentParent graph child rest

record ParentEdge (Vertex : Set) : Set where
  constructor parentEdge
  field
    child parent : Vertex

open ParentEdge public

record LayerDiscovery (Vertex : Set) : Set where
  constructor layerDiscovery
  field
    discovered : List Vertex
    parentEdges : List (ParentEdge Vertex)

open LayerDiscovery public

emptyDiscovery : ∀ {Vertex} → LayerDiscovery Vertex
emptyDiscovery = layerDiscovery [] []

discoverLayer :
  ∀ {Vertex} → FiniteDecidableGraph Vertex →
  List Vertex → List Vertex → LayerDiscovery Vertex
discoverLayer graph frontier [] = emptyDiscovery
discoverLayer graph frontier (candidate ∷ rest)
  with firstAdjacentParent graph candidate frontier
... | nothing = discoverLayer graph frontier rest
... | just parentVertex with discoverLayer graph frontier rest
...   | layerDiscovery laterVertices laterEdges =
        layerDiscovery
          (candidate ∷ laterVertices)
          (parentEdge candidate parentVertex ∷ laterEdges)

record BFSState (Vertex : Set) : Set where
  constructor bfsState
  field
    visited : List Vertex
    frontier : List Vertex
    undiscovered : List Vertex
    treeEdges : List (ParentEdge Vertex)

open BFSState public

initialState :
  ∀ {Vertex} → FiniteDecidableGraph Vertex → Vertex → BFSState Vertex
initialState graph root = bfsState
  (root ∷ [])
  (root ∷ [])
  (removeMembers graph (root ∷ []) (vertices graph))
  []

advanceState :
  ∀ {Vertex} → FiniteDecidableGraph Vertex → BFSState Vertex → BFSState Vertex
advanceState graph state
  with discoverLayer graph (frontier state) (undiscovered state)
... | layerDiscovery newVertices newEdges = bfsState
      (append (visited state) newVertices)
      newVertices
      (removeMembers graph newVertices (undiscovered state))
      (append (treeEdges state) newEdges)

bfsFuel :
  ∀ {Vertex} → FiniteDecidableGraph Vertex → Nat → BFSState Vertex → BFSState Vertex
bfsFuel graph zero state = state
bfsFuel graph (suc fuel) state with frontier state
... | [] = state
... | _ ∷ _ = bfsFuel graph fuel (advanceState graph state)

runFiniteBFS :
  ∀ {Vertex} → FiniteDecidableGraph Vertex → Vertex → BFSState Vertex
runFiniteBFS graph root =
  bfsFuel graph (length (vertices graph)) (initialState graph root)

bfsFuelZeroExact :
  ∀ {Vertex} (graph : FiniteDecidableGraph Vertex) state →
  bfsFuel graph zero state ≡ state
bfsFuelZeroExact graph state = Agda.Builtin.Equality.refl

record FiniteBFSCorrectness
    {Vertex : Set}
    (graph : FiniteDecidableGraph Vertex)
    (root : Vertex) : Set₁ where
  field
    vertexEnumerationComplete : Set
    equalBoolCorrect : Set
    adjacentBoolCorrect : Set
    rootEnumerated : Set

    visitedDuplicateFree : Set
    everyDiscoveredVertexHasOneParent : Set
    parentBelongsToPreviousLayer : Set
    parentAdjacentToChild : Set
    parentDistanceDropsByOne : Set
    treeEdgesAcyclic : Set
    treeSpansRootComponentExactly : Set
    layerIndexEqualsShortestPathDistance : Set

open FiniteBFSCorrectness public

record PeriodicBFSInstantiation (PeriodicBlock : Set) : Set₁ where
  field
    periodicGraph : FiniteDecidableGraph PeriodicBlock
    zeroBlock : PeriodicBlock
    correctness : FiniteBFSCorrectness periodicGraph zeroBlock

open PeriodicBFSInstantiation public

executableVisitedSetBFSDefinitionLevel : ProofLevel
executableVisitedSetBFSDefinitionLevel = machineChecked

fuelBoundedTerminationByConstructionLevel : ProofLevel
fuelBoundedTerminationByConstructionLevel = machineChecked

canonicalPreviousLayerParentDefinitionLevel : ProofLevel
canonicalPreviousLayerParentDefinitionLevel = machineChecked

physicalPeriodicGraphEnumerationInputsLevel : ProofLevel
physicalPeriodicGraphEnumerationInputsLevel = conditional

periodicBFSCorrectnessInvariantInputsLevel : ProofLevel
periodicBFSCorrectnessInvariantInputsLevel = conditional

periodicBFSImplementationAssemblyInputsLevel : ProofLevel
periodicBFSImplementationAssemblyInputsLevel = conditional
