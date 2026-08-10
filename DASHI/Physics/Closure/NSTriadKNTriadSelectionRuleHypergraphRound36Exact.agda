module DASHI.Physics.Closure.NSTriadKNTriadSelectionRuleHypergraphRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Peter Constantin; Ciprian Foias.
-- Title: "Navier--Stokes Equations".
-- DOI: 10.7208/chicago/9780226115498.001.0001.
--
-- DASHI CONTRIBUTION
--
-- Turn the finite Fourier selection-rule idea into a proof-bearing hypergraph.
-- A hyperedge is not an arbitrary triple: it is one literal lattice triad
-- carrying membership in an `ExactRetainedSectorLaw`.  The sector already
-- requires exact zero momentum and is invariant under the generators of S3
-- and under Fourier reality.
--
-- Round 35 proved that the canonical triad action factors as
--
--   S3 x C2(reality).
--
-- Here that action is lifted to retained hyperedges.  Every one of the twelve
-- factored actions preserves edge admissibility and hence momentum closure.
-- Stabilizers are allowed: this is an action groupoid/hypergraph, not an
-- assertion that every edge has twelve distinct images.
--
-- A genuinely nonzero physical interaction coefficient is deliberately kept
-- as an additional selection law.  Momentum closure plus cutoff membership
-- alone does not manufacture a nonzero coupling.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNTriadS3RealityActionRound35Exact as Action

record RetainedTriadHyperedge
    (cutoff : Nat)
    (sector : Lattice.ExactRetainedSectorLaw cutoff) : Set where
  constructor retained-triad-hyperedge
  field
    triad : Lattice.LatticeTriad
    retained : Lattice.retained? sector triad ≡ true

open RetainedTriadHyperedge public

retainedEdgeMomentumClosure :
  ∀ {cutoff sector}
    (edge : RetainedTriadHyperedge cutoff sector) →
  Lattice.zeroSum? (triad edge) ≡ true
retainedEdgeMomentumClosure {sector = sector} edge =
  Lattice.zeroSumRequired sector (triad edge) (retained edge)

cycleEdge :
  ∀ {cutoff sector} →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
cycleEdge {sector = sector} edge =
  retained-triad-hyperedge
    (Lattice.triadCycle (triad edge))
    (trans (Lattice.cycleInvariant sector (triad edge)) (retained edge))

swapEdge :
  ∀ {cutoff sector} →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
swapEdge {sector = sector} edge =
  retained-triad-hyperedge
    (Lattice.triadSwap (triad edge))
    (trans (Lattice.swapInvariant sector (triad edge)) (retained edge))

realityEdge :
  ∀ {cutoff sector} →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
realityEdge {sector = sector} edge =
  retained-triad-hyperedge
    (Lattice.triadNeg (triad edge))
    (trans (Lattice.realityInvariant sector (triad edge)) (retained edge))

applyPermutationEdge :
  ∀ {cutoff sector} →
  Action.PermutationAction6 →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
applyPermutationEdge Action.identity edge = edge
applyPermutationEdge Action.swap edge = swapEdge edge
applyPermutationEdge Action.cycle edge = cycleEdge edge
applyPermutationEdge Action.swapCycle edge = swapEdge (cycleEdge edge)
applyPermutationEdge Action.cycleTwice edge = cycleEdge (cycleEdge edge)
applyPermutationEdge Action.swapCycleTwice edge =
  swapEdge (cycleEdge (cycleEdge edge))

applyRealityEdge :
  ∀ {cutoff sector} →
  Action.RealityAction2 →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
applyRealityEdge Action.direct edge = edge
applyRealityEdge Action.reality edge = realityEdge edge

applyFactoredEdge :
  ∀ {cutoff sector} →
  Action.PermutationAction6 →
  Action.RealityAction2 →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
applyFactoredEdge permutation realityChoice edge =
  applyRealityEdge realityChoice (applyPermutationEdge permutation edge)

applyPermutationEdgeTriadExact :
  ∀ {cutoff sector}
    (permutation : Action.PermutationAction6)
    (edge : RetainedTriadHyperedge cutoff sector) →
  triad (applyPermutationEdge permutation edge)
  ≡ Action.applyPermutation permutation (triad edge)
applyPermutationEdgeTriadExact Action.identity edge = refl
applyPermutationEdgeTriadExact Action.swap edge = refl
applyPermutationEdgeTriadExact Action.cycle edge = refl
applyPermutationEdgeTriadExact Action.swapCycle edge = refl
applyPermutationEdgeTriadExact Action.cycleTwice edge = refl
applyPermutationEdgeTriadExact Action.swapCycleTwice edge = refl

applyFactoredEdgeTriadExact :
  ∀ {cutoff sector}
    (permutation : Action.PermutationAction6)
    (realityChoice : Action.RealityAction2)
    (edge : RetainedTriadHyperedge cutoff sector) →
  triad (applyFactoredEdge permutation realityChoice edge)
  ≡ Action.applyFactoredAction permutation realityChoice (triad edge)
applyFactoredEdgeTriadExact permutation Action.direct edge =
  applyPermutationEdgeTriadExact permutation edge
applyFactoredEdgeTriadExact permutation Action.reality edge
  rewrite applyPermutationEdgeTriadExact permutation edge = refl

factoredActionPreservesMomentumClosure :
  ∀ {cutoff sector}
    (permutation : Action.PermutationAction6)
    (realityChoice : Action.RealityAction2)
    (edge : RetainedTriadHyperedge cutoff sector) →
  Lattice.zeroSum?
    (Action.applyFactoredAction permutation realityChoice (triad edge))
  ≡ true
factoredActionPreservesMomentumClosure permutation realityChoice edge
  rewrite ← applyFactoredEdgeTriadExact permutation realityChoice edge =
  retainedEdgeMomentumClosure
    (applyFactoredEdge permutation realityChoice edge)

record PhysicalCouplingSelectionLaw
    (cutoff : Nat)
    (sector : Lattice.ExactRetainedSectorLaw cutoff) : Set where
  field
    active? : Lattice.LatticeTriad → Bool

    activeImpliesRetained : ∀ triad →
      active? triad ≡ true → Lattice.retained? sector triad ≡ true

    permutationInvariant :
      (permutation : Action.PermutationAction6) →
      (triad : Lattice.LatticeTriad) →
      active? (Action.applyPermutation permutation triad) ≡ active? triad

    realityInvariant :
      (triad : Lattice.LatticeTriad) →
      active? (Lattice.triadNeg triad) ≡ active? triad

open PhysicalCouplingSelectionLaw public

record ActiveTriadHyperedge
    {cutoff : Nat}
    {sector : Lattice.ExactRetainedSectorLaw cutoff}
    (coupling : PhysicalCouplingSelectionLaw cutoff sector) : Set where
  constructor active-triad-hyperedge
  field
    activeTriad : Lattice.LatticeTriad
    active : active? coupling activeTriad ≡ true

open ActiveTriadHyperedge public

activeEdgeRetained :
  ∀ {cutoff sector coupling}
    (edge : ActiveTriadHyperedge
      {cutoff = cutoff} {sector = sector} coupling) →
  Lattice.retained? sector (activeTriad edge) ≡ true
activeEdgeRetained {coupling = coupling} edge =
  activeImpliesRetained coupling (activeTriad edge) (active edge)

activeEdgeMomentumClosure :
  ∀ {cutoff sector coupling}
    (edge : ActiveTriadHyperedge
      {cutoff = cutoff} {sector = sector} coupling) →
  Lattice.zeroSum? (activeTriad edge) ≡ true
activeEdgeMomentumClosure {sector = sector} edge =
  Lattice.zeroSumRequired sector _ (activeEdgeRetained edge)

triadSelectionRuleHypergraphClosed : Bool
triadSelectionRuleHypergraphClosed = true

factoredSelectionActionClosed : Bool
factoredSelectionActionClosed = true

physicalCouplingSelectionLawConstructed : Bool
physicalCouplingSelectionLawConstructed = false

triadSelectionRuleHypergraphClosedIsTrue :
  triadSelectionRuleHypergraphClosed ≡ true
triadSelectionRuleHypergraphClosedIsTrue = refl

factoredSelectionActionClosedIsTrue :
  factoredSelectionActionClosed ≡ true
factoredSelectionActionClosedIsTrue = refl

physicalCouplingSelectionLawConstructedIsFalse :
  physicalCouplingSelectionLawConstructed ≡ false
physicalCouplingSelectionLawConstructedIsFalse = refl
