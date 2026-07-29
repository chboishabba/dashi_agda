module DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSParentCorrectnessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSAlgorithmExact as BFS

------------------------------------------------------------------------
-- Correctness of the executable parent-selection layer.
--
-- The proof is finite recursion over the supplied frontier order.  It does not
-- use choice: the first Boolean-adjacent vertex is returned, and Boolean
-- reflection supplies the physical adjacency witness.
------------------------------------------------------------------------

data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

falseNotTrue : false ≡ true → Empty
falseNotTrue ()

justInjective : ∀ {A : Set} {left right : A} → just left ≡ just right → left ≡ right
justInjective refl = refl

infix 4 _∈L_
data _∈L_ {A : Set} (value : A) : List A → Set where
  hereL : ∀ {rest} → value ∈L (value ∷ rest)
  thereL : ∀ {head rest} → value ∈L rest → value ∈L (head ∷ rest)

record GraphBooleanMeaning
    {Vertex : Set}
    (graph : BFS.FiniteDecidableGraph Vertex) : Set₁ where
  field
    Adjacent : Vertex → Vertex → Set
    adjacentBoolSound : ∀ left right →
      BFS.adjacentBool graph left right ≡ true → Adjacent left right
    adjacentBoolComplete : ∀ left right →
      Adjacent left right → BFS.adjacentBool graph left right ≡ true

open GraphBooleanMeaning public

data FirstAdjacent
    {Vertex : Set}
    {graph : BFS.FiniteDecidableGraph Vertex}
    (meaning : GraphBooleanMeaning graph)
    (child : Vertex) : Vertex → List Vertex → Set where
  firstHere : ∀ {parent rest} →
    Adjacent meaning parent child →
    FirstAdjacent meaning child parent (parent ∷ rest)
  firstThere : ∀ {skipped parent rest} →
    Not (Adjacent meaning skipped child) →
    FirstAdjacent meaning child parent rest →
    FirstAdjacent meaning child parent (skipped ∷ rest)

adjacentBoolFalseMeansNotAdjacent :
  ∀ {Vertex}
    {graph : BFS.FiniteDecidableGraph Vertex}
    (meaning : GraphBooleanMeaning graph)
    left right →
  BFS.adjacentBool graph left right ≡ false →
  Not (Adjacent meaning left right)
adjacentBoolFalseMeansNotAdjacent meaning left right refl adjacent =
  falseNotTrue (adjacentBoolComplete meaning left right adjacent)

firstAdjacentParentSound :
  ∀ {Vertex}
    {graph : BFS.FiniteDecidableGraph Vertex}
    (meaning : GraphBooleanMeaning graph)
    child frontier parent →
  BFS.firstAdjacentParent graph child frontier ≡ just parent →
  parent ∈L frontier × Adjacent meaning parent child
firstAdjacentParentSound meaning child [] parent ()
firstAdjacentParentSound {graph = graph} meaning child (candidate ∷ rest) parent equality
  with BFS.adjacentBool graph candidate child
... | true =
  subst
    (λ selected → selected ∈L (candidate ∷ rest)
      × Adjacent meaning selected child)
    (justInjective equality)
    (hereL , adjacentBoolSound meaning candidate child refl)
... | false with firstAdjacentParentSound meaning child rest parent equality
...   | membership , adjacent = thereL membership , adjacent

firstAdjacentParentIsFirst :
  ∀ {Vertex}
    {graph : BFS.FiniteDecidableGraph Vertex}
    (meaning : GraphBooleanMeaning graph)
    child frontier parent →
  BFS.firstAdjacentParent graph child frontier ≡ just parent →
  FirstAdjacent meaning child parent frontier
firstAdjacentParentIsFirst meaning child [] parent ()
firstAdjacentParentIsFirst {graph = graph} meaning child (candidate ∷ rest) parent equality
  with BFS.adjacentBool graph candidate child
... | true =
  subst
    (λ selected → FirstAdjacent meaning child selected (candidate ∷ rest))
    (justInjective equality)
    (firstHere (adjacentBoolSound meaning candidate child refl))
... | false =
  firstThere
    (adjacentBoolFalseMeansNotAdjacent meaning candidate child refl)
    (firstAdjacentParentIsFirst meaning child rest parent equality)

data ParentEdgesSound
    {Vertex : Set}
    {graph : BFS.FiniteDecidableGraph Vertex}
    (meaning : GraphBooleanMeaning graph)
    (frontier : List Vertex) : List (BFS.ParentEdge Vertex) → Set where
  noEdges : ParentEdgesSound meaning frontier []
  soundEdge : ∀ {child parent rest} →
    parent ∈L frontier →
    Adjacent meaning parent child →
    ParentEdgesSound meaning frontier rest →
    ParentEdgesSound meaning frontier
      (BFS.parentEdge child parent ∷ rest)

discoverLayerParentEdgesSound :
  ∀ {Vertex}
    {graph : BFS.FiniteDecidableGraph Vertex}
    (meaning : GraphBooleanMeaning graph)
    frontier candidates →
  ParentEdgesSound meaning frontier
    (BFS.parentEdges (BFS.discoverLayer graph frontier candidates))
discoverLayerParentEdgesSound meaning frontier [] = noEdges
discoverLayerParentEdgesSound {graph = graph} meaning frontier (candidate ∷ rest)
  with BFS.firstAdjacentParent graph candidate frontier
... | nothing = discoverLayerParentEdgesSound meaning frontier rest
... | just parent with BFS.discoverLayer graph frontier rest
...   | BFS.layerDiscovery laterVertices laterEdges =
      let selected = firstAdjacentParentSound meaning candidate frontier parent refl
      in soundEdge
          (Data.Product.proj₁ selected)
          (Data.Product.proj₂ selected)
          (discoverLayerParentEdgesSound meaning frontier rest)

firstAdjacentParentSoundLevel : ProofLevel
firstAdjacentParentSoundLevel = machineChecked

firstAdjacentParentCanonicalOrderLevel : ProofLevel
firstAdjacentParentCanonicalOrderLevel = machineChecked

discoveredParentEdgesSoundLevel : ProofLevel
discoveredParentEdgesSoundLevel = machineChecked

bfsDistanceLayerInvariantInputsLevel : ProofLevel
bfsDistanceLayerInvariantInputsLevel = conditional

bfsSpanningAndAcyclicityInputsLevel : ProofLevel
bfsSpanningAndAcyclicityInputsLevel = conditional
