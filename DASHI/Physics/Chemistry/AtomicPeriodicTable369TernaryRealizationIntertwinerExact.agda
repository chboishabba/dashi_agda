module DASHI.Physics.Chemistry.AtomicPeriodicTable369TernaryRealizationIntertwinerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G

------------------------------------------------------------------------
-- Exact bridge contract needed before a ternary transition graph may be drawn
-- as the same physical one-particle/orbital transition graph.
--
-- This owner intentionally does not manufacture an inhabitant.
------------------------------------------------------------------------

record TernaryAtomicRealizationIntertwiner (d : Nat) : Set₁ where
  field
    PhysicalState : Set

    ternaryStep : G.TernaryKernel d -> G.TernaryKernel d
    physicalStep : PhysicalState -> PhysicalState

    realize : G.TernaryKernel d -> PhysicalState
    orbitalReadout : PhysicalState -> G.OrbitalLabel

    intertwines :
      (x : G.TernaryKernel d) ->
      realize (ternaryStep x) ≡ physicalStep (realize x)

open TernaryAtomicRealizationIntertwiner public

record TernaryAtomicRealizationBoundary : Set where
  constructor ternaryAtomicRealizationBoundary
  field
    abstractRealizationInterfaceExists : Bool
    sameCardinalityConstructsRealization : Bool
    shellCapacityConstructsRealization : Bool
    graphSimilarityConstructsRealization : Bool
    physicalRepresentationStillSupplied : Bool

canonicalTernaryAtomicRealizationBoundary : TernaryAtomicRealizationBoundary
canonicalTernaryAtomicRealizationBoundary =
  ternaryAtomicRealizationBoundary true false false false true

sameCardinalityConstructsRealizationIsFalse :
  TernaryAtomicRealizationBoundary.sameCardinalityConstructsRealization
    canonicalTernaryAtomicRealizationBoundary
  ≡ false
sameCardinalityConstructsRealizationIsFalse = refl

graphSimilarityConstructsRealizationIsFalse :
  TernaryAtomicRealizationBoundary.graphSimilarityConstructsRealization
    canonicalTernaryAtomicRealizationBoundary
  ≡ false
graphSimilarityConstructsRealizationIsFalse = refl

------------------------------------------------------------------------
-- Downstream graph consumer: once an independently sourced realization is
-- supplied, every ternary edge transports to a physical edge by intertwining.
------------------------------------------------------------------------

transportedPhysicalStep :
  {d : Nat} ->
  (R : TernaryAtomicRealizationIntertwiner d) ->
  G.TernaryKernel d -> PhysicalState R
transportedPhysicalStep R x = physicalStep R (realize R x)

transportedEdgeCommutes :
  {d : Nat} ->
  (R : TernaryAtomicRealizationIntertwiner d) ->
  (x : G.TernaryKernel d) ->
  realize R (ternaryStep R x) ≡ transportedPhysicalStep R x
transportedEdgeCommutes R x = intertwines R x
