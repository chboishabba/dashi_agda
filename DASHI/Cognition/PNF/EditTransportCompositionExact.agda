module DASHI.Cognition.PNF.EditTransportCompositionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_)

open import DASHI.Cognition.PNF.EditTransportLeafLocalityExact

------------------------------------------------------------------------
-- Revision-lineage transport algebra.
--
-- A long-lived document/chat should compose exact local revision transports
-- rather than repeatedly solving one global v0 <-> vn correspondence problem.
------------------------------------------------------------------------

identityEditTransport : EditTransport
identityEditTransport = editTransport (λ coordinate → coordinate)

composeEditTransport : EditTransport → EditTransport → EditTransport
composeEditTransport first second =
  editTransport
    (λ coordinate →
      transportCoordinate second (transportCoordinate first coordinate))

identityTransportCoordinate :
  (coordinate : Nat) →
  transportCoordinate identityEditTransport coordinate ≡ coordinate
identityTransportCoordinate coordinate = refl

composedTransportCoordinate :
  (first second : EditTransport) →
  (coordinate : Nat) →
  transportCoordinate (composeEditTransport first second) coordinate ≡
  transportCoordinate second (transportCoordinate first coordinate)
composedTransportCoordinate first second coordinate = refl

leftIdentityTransportCoordinate :
  (transport : EditTransport) →
  (coordinate : Nat) →
  transportCoordinate (composeEditTransport identityEditTransport transport) coordinate ≡
  transportCoordinate transport coordinate
leftIdentityTransportCoordinate transport coordinate = refl

rightIdentityTransportCoordinate :
  (transport : EditTransport) →
  (coordinate : Nat) →
  transportCoordinate (composeEditTransport transport identityEditTransport) coordinate ≡
  transportCoordinate transport coordinate
rightIdentityTransportCoordinate transport coordinate = refl

associativeTransportCoordinate :
  (first second third : EditTransport) →
  (coordinate : Nat) →
  transportCoordinate
    (composeEditTransport (composeEditTransport first second) third)
    coordinate
  ≡
  transportCoordinate
    (composeEditTransport first (composeEditTransport second third))
    coordinate
associativeTransportCoordinate first second third coordinate = refl

------------------------------------------------------------------------
-- Edit-set / dependency-closure monotonicity.
--
-- For a fixed or enlarged reverse-dependency graph, adding edited source atoms
-- must not make an already predicted affected leaf disappear. This is a cheap
-- runtime regression invariant and is separate from closure precision.
------------------------------------------------------------------------

ClosureSubset :
  {SourceAtom Leaf : Set} →
  EditedDependencyClosure SourceAtom Leaf →
  EditedDependencyClosure SourceAtom Leaf → Set
ClosureSubset {Leaf = Leaf} smaller larger =
  (leaf : Leaf) → InEditedClosure smaller leaf → InEditedClosure larger leaf

closureMonotoneUnderEditedAndReachability :
  {SourceAtom Leaf : Set} →
  {smaller larger : EditedDependencyClosure SourceAtom Leaf} →
  ((source : SourceAtom) → edited smaller source → edited larger source) →
  ((source : SourceAtom) → (leaf : Leaf) →
    reaches smaller source leaf → reaches larger source leaf) →
  ClosureSubset smaller larger
closureMonotoneUnderEditedAndReachability
  editedMonotone reachabilityMonotone leaf
  (source , sourceEdited , sourceReaches) =
    source ,
    editedMonotone source sourceEdited ,
    reachabilityMonotone source leaf sourceReaches
