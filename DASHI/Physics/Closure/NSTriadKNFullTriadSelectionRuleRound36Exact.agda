module DASHI.Physics.Closure.NSTriadKNFullTriadSelectionRuleRound36Exact where

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
-- Complete the selection-rule hypergraph suggested by the continuation notes.
-- A genuinely active Fourier transition must simultaneously carry
--
--   1. exact momentum closure,
--   2. exact cutoff-shell plus retained-sector membership,
--   3. transversality,
--   4. Fourier-reality compatibility,
--   5. nonzero physical coupling.
--
-- The first two are now carried by the repository's full
-- `RetainedTriadMember`, not by the retained-sector Boolean alone.  The three
-- genuinely physical predicates remain abstract but must be covariant under
-- the already-proved S3 relabelling and C2 reality action.  The full
-- admissibility package is transported under all twelve factored actions.
-- Stabilizers remain allowed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNTriadS3RealityActionRound35Exact as Action
import DASHI.Physics.Closure.NSTriadKNTriadSelectionRuleHypergraphRound36Exact as Hyper

record FullPhysicalTriadSelectionLaw
    (cutoff : Nat)
    (sector : Lattice.ExactRetainedSectorLaw cutoff) : Set₁ where
  field
    Transverse : Lattice.LatticeTriad → Set
    RealityCompatible : Lattice.LatticeTriad → Set
    NonzeroCoupling : Lattice.LatticeTriad → Set

    transversePermutation :
      ∀ permutation triad →
      Transverse triad →
      Transverse (Action.applyPermutation permutation triad)

    transverseReality :
      ∀ triad →
      Transverse triad → Transverse (Lattice.triadNeg triad)

    realityPermutation :
      ∀ permutation triad →
      RealityCompatible triad →
      RealityCompatible (Action.applyPermutation permutation triad)

    realityReality :
      ∀ triad →
      RealityCompatible triad → RealityCompatible (Lattice.triadNeg triad)

    couplingPermutation :
      ∀ permutation triad →
      NonzeroCoupling triad →
      NonzeroCoupling (Action.applyPermutation permutation triad)

    couplingReality :
      ∀ triad →
      NonzeroCoupling triad → NonzeroCoupling (Lattice.triadNeg triad)

open FullPhysicalTriadSelectionLaw public

record FullyAdmissibleTriadHyperedge
    {cutoff : Nat}
    {sector : Lattice.ExactRetainedSectorLaw cutoff}
    (law : FullPhysicalTriadSelectionLaw cutoff sector) : Set₁ where
  constructor fully-admissible-triad-hyperedge
  field
    triad : Lattice.LatticeTriad
    retainedMember : Lattice.RetainedTriadMember cutoff sector triad
    transverse : Transverse law triad
    realityCompatible : RealityCompatible law triad
    nonzeroCoupling : NonzeroCoupling law triad

open FullyAdmissibleTriadHyperedge public

fullyAdmissibleMomentumClosure :
  ∀ {cutoff sector law}
    (edge : FullyAdmissibleTriadHyperedge
      {cutoff = cutoff} {sector = sector} law) →
  Lattice.zeroSum? (triad edge) ≡ true
fullyAdmissibleMomentumClosure edge =
  Hyper.zeroSumFromMember (retainedMember edge)

permutationMember :
  ∀ {cutoff sector}
    (permutation : Action.PermutationAction6)
    (triad : Lattice.LatticeTriad) →
  Lattice.RetainedTriadMember cutoff sector triad →
  Lattice.RetainedTriadMember
    cutoff sector (Action.applyPermutation permutation triad)
permutationMember {cutoff} {sector} permutation triad member =
  let
    edge : Hyper.RetainedTriadHyperedge cutoff sector
    edge = Hyper.retained-triad-hyperedge triad member

    moved : Hyper.RetainedTriadHyperedge cutoff sector
    moved = Hyper.applyPermutationEdge permutation edge
  in
  subst
    (Lattice.RetainedTriadMember cutoff sector)
    (Hyper.applyPermutationEdgeTriadExact permutation edge)
    (Hyper.retainedMember moved)

realityMember :
  ∀ {cutoff sector} (triad : Lattice.LatticeTriad) →
  Lattice.RetainedTriadMember cutoff sector triad →
  Lattice.RetainedTriadMember cutoff sector (Lattice.triadNeg triad)
realityMember = Hyper.realityRetainedMember

applyPermutationFullyAdmissible :
  ∀ {cutoff sector law} →
  (permutation : Action.PermutationAction6) →
  FullyAdmissibleTriadHyperedge
    {cutoff = cutoff} {sector = sector} law →
  FullyAdmissibleTriadHyperedge law
applyPermutationFullyAdmissible {law = law} permutation edge =
  fully-admissible-triad-hyperedge
    (Action.applyPermutation permutation (triad edge))
    (permutationMember permutation (triad edge) (retainedMember edge))
    (transversePermutation law permutation (triad edge) (transverse edge))
    (realityPermutation law permutation (triad edge) (realityCompatible edge))
    (couplingPermutation law permutation (triad edge) (nonzeroCoupling edge))

applyRealityFullyAdmissible :
  ∀ {cutoff sector law} →
  FullyAdmissibleTriadHyperedge
    {cutoff = cutoff} {sector = sector} law →
  FullyAdmissibleTriadHyperedge law
applyRealityFullyAdmissible {law = law} edge =
  fully-admissible-triad-hyperedge
    (Lattice.triadNeg (triad edge))
    (realityMember (triad edge) (retainedMember edge))
    (transverseReality law (triad edge) (transverse edge))
    (realityReality law (triad edge) (realityCompatible edge))
    (couplingReality law (triad edge) (nonzeroCoupling edge))

applyFactoredFullyAdmissible :
  ∀ {cutoff sector law} →
  Action.PermutationAction6 →
  Action.RealityAction2 →
  FullyAdmissibleTriadHyperedge
    {cutoff = cutoff} {sector = sector} law →
  FullyAdmissibleTriadHyperedge law
applyFactoredFullyAdmissible permutation Action.direct edge =
  applyPermutationFullyAdmissible permutation edge
applyFactoredFullyAdmissible permutation Action.reality edge =
  applyRealityFullyAdmissible
    (applyPermutationFullyAdmissible permutation edge)

record FullFivePartSelectionClosure
    (cutoff : Nat)
    (sector : Lattice.ExactRetainedSectorLaw cutoff)
    (law : FullPhysicalTriadSelectionLaw cutoff sector) : Set₁ where
  field
    factoredPreservesAdmissibility :
      Action.PermutationAction6 →
      Action.RealityAction2 →
      FullyAdmissibleTriadHyperedge law →
      FullyAdmissibleTriadHyperedge law

    everyAdmissibleEdgeHasMomentumClosure :
      (edge : FullyAdmissibleTriadHyperedge law) →
      Lattice.zeroSum? (triad edge) ≡ true

open FullFivePartSelectionClosure public

canonicalFullFivePartSelectionClosure :
  ∀ cutoff sector law → FullFivePartSelectionClosure cutoff sector law
canonicalFullFivePartSelectionClosure cutoff sector law = record
  { factoredPreservesAdmissibility = applyFactoredFullyAdmissible
  ; everyAdmissibleEdgeHasMomentumClosure = fullyAdmissibleMomentumClosure
  }

physicalFullTriadSelectionLawConstructed : Bool
physicalFullTriadSelectionLawConstructed = false

physicalFullTriadSelectionLawConstructedIsFalse :
  physicalFullTriadSelectionLawConstructed ≡ false
physicalFullTriadSelectionLawConstructedIsFalse = refl
