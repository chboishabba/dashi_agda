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
--   2. cutoff/retained-sector membership,
--   3. transversality,
--   4. Fourier-reality compatibility,
--   5. nonzero physical coupling.
--
-- The retained-sector law supplies (1)-(2).  This module leaves the three
-- genuinely physical predicates abstract but requires their invariance under
-- the already-proved S3 relabelling and C2 reality action.  It then proves
-- that all twelve factored actions preserve the full five-part admissibility
-- package.  Stabilizers remain allowed.
--
-- This gives F4/HH-bad a typed active-transition subgraph without pretending
-- that momentum closure alone implies nonzero interaction strength.
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
    (law : FullPhysicalTriadSelectionLaw cutoff sector) : Set where
  constructor fully-admissible-triad-hyperedge
  field
    triad : Lattice.LatticeTriad
    retained : Lattice.retained? sector triad ≡ true
    transverse : Transverse law triad
    realityCompatible : RealityCompatible law triad
    nonzeroCoupling : NonzeroCoupling law triad

open FullyAdmissibleTriadHyperedge public

fullyAdmissibleMomentumClosure :
  ∀ {cutoff sector law}
    (edge : FullyAdmissibleTriadHyperedge
      {cutoff = cutoff} {sector = sector} law) →
  Lattice.zeroSum? (triad edge) ≡ true
fullyAdmissibleMomentumClosure {sector = sector} edge =
  Lattice.zeroSumRequired sector (triad edge) (retained edge)

permutationRetained :
  ∀ {cutoff sector}
    (permutation : Action.PermutationAction6)
    (triad : Lattice.LatticeTriad) →
  Lattice.retained? sector triad ≡ true →
  Lattice.retained? sector (Action.applyPermutation permutation triad) ≡ true
permutationRetained {cutoff} {sector} permutation triad retainedProof =
  let
    edge : Hyper.RetainedTriadHyperedge cutoff sector
    edge = Hyper.retained-triad-hyperedge triad retainedProof

    moved : Hyper.RetainedTriadHyperedge cutoff sector
    moved = Hyper.applyPermutationEdge permutation edge
  in
  subst
    (λ selected → Lattice.retained? sector selected ≡ true)
    (Hyper.applyPermutationEdgeTriadExact permutation edge)
    (Hyper.retained moved)

realityRetained :
  ∀ {cutoff sector} (triad : Lattice.LatticeTriad) →
  Lattice.retained? sector triad ≡ true →
  Lattice.retained? sector (Lattice.triadNeg triad) ≡ true
realityRetained {sector = sector} triad retainedProof =
  Hyper.retained
    (Hyper.realityEdge
      (Hyper.retained-triad-hyperedge triad retainedProof))

applyPermutationFullyAdmissible :
  ∀ {cutoff sector law} →
  (permutation : Action.PermutationAction6) →
  FullyAdmissibleTriadHyperedge
    {cutoff = cutoff} {sector = sector} law →
  FullyAdmissibleTriadHyperedge law
applyPermutationFullyAdmissible {law = law} permutation edge =
  fully-admissible-triad-hyperedge
    (Action.applyPermutation permutation (triad edge))
    (permutationRetained permutation (triad edge) (retained edge))
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
    (realityRetained (triad edge) (retained edge))
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

fullFivePartSelectionRuleClosed : Bool
fullFivePartSelectionRuleClosed = true

physicalFullTriadSelectionLawConstructed : Bool
physicalFullTriadSelectionLawConstructed = false

fullFivePartSelectionRuleClosedIsTrue :
  fullFivePartSelectionRuleClosed ≡ true
fullFivePartSelectionRuleClosedIsTrue = refl

physicalFullTriadSelectionLawConstructedIsFalse :
  physicalFullTriadSelectionLawConstructed ≡ false
physicalFullTriadSelectionLawConstructedIsFalse = refl
