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
-- A retained edge now carries the repository's full `RetainedTriadMember`:
-- all three modes are in the exact cutoff shell, the triad has exact zero
-- momentum, and the physical sector predicate holds.  Thus a zero-sum triad
-- outside the cutoff cannot enter this graph.
--
-- Round 35 proved that the canonical triad action factors as
--
--   S3 x C2(reality).
--
-- Here that action is lifted to retained hyperedges.  Cycles and swaps merely
-- permute the three shell-membership proofs.  Reality requires the additional
-- exact theorem proved below that `inExactShell?` is invariant under integer
-- mode negation.  Hence every one of the twelve factored actions preserves
-- the full retained-member invariant, not just a Boolean sector receipt.
-- Stabilizers are allowed.
--
-- A genuinely nonzero physical interaction coefficient is deliberately kept
-- as an additional selection law.  Momentum closure plus cutoff membership
-- alone does not manufacture a nonzero coupling.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as ℤ
import Data.Integer.Tactic.RingSolver as ℤRing
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNTriadS3RealityActionRound35Exact as Action

------------------------------------------------------------------------
-- Exact shell invariance under Fourier reality.
------------------------------------------------------------------------

isZeroNeg : ∀ value → Lattice.isZero (ℤ.- value) ≡ Lattice.isZero value
isZeroNeg (ℤ.+ zero) = refl
isZeroNeg (ℤ.+ sucValue@(suc _)) = refl
isZeroNeg (ℤ.-[1+ _ ]) = refl

modeSquaredNormNeg :
  ∀ mode →
  Lattice.modeSquaredNorm (Lattice.modeNeg mode)
  ≡ Lattice.modeSquaredNorm mode
modeSquaredNormNeg
    (Lattice.mkLatticeMode3 first second third) =
  ℤRing.solve (first ∷ second ∷ third ∷ [])

nonzeroModeNeg :
  ∀ mode →
  Lattice.nonzeroMode? (Lattice.modeNeg mode)
  ≡ Lattice.nonzeroMode? mode
nonzeroModeNeg
    (Lattice.mkLatticeMode3 first second third)
  rewrite isZeroNeg first | isZeroNeg second | isZeroNeg third = refl

inExactShellNeg :
  ∀ cutoff mode →
  Lattice.inExactShell? cutoff (Lattice.modeNeg mode)
  ≡ Lattice.inExactShell? cutoff mode
inExactShellNeg cutoff mode
  rewrite modeSquaredNormNeg mode | nonzeroModeNeg mode = refl

shellMemberNeg :
  ∀ {cutoff mode} →
  Lattice.ShellMember cutoff mode →
  Lattice.ShellMember cutoff (Lattice.modeNeg mode)
shellMemberNeg {cutoff} {mode} member =
  trans (inExactShellNeg cutoff mode) member

------------------------------------------------------------------------
-- Full retained-member transport under the generators.
------------------------------------------------------------------------

retainedProofFromMember :
  ∀ {cutoff sector triad} →
  Lattice.RetainedTriadMember cutoff sector triad →
  Lattice.retained? sector triad ≡ true
retainedProofFromMember
  (leftShell , (rightShell , (outShell , (zeroSum , retainedProof)))) =
  retainedProof

zeroSumFromMember :
  ∀ {cutoff sector triad} →
  Lattice.RetainedTriadMember cutoff sector triad →
  Lattice.zeroSum? triad ≡ true
zeroSumFromMember
  (leftShell , (rightShell , (outShell , (zeroSum , retainedProof)))) =
  zeroSum

cycleRetainedMember :
  ∀ {cutoff sector} (triad : Lattice.LatticeTriad) →
  Lattice.RetainedTriadMember cutoff sector triad →
  Lattice.RetainedTriadMember cutoff sector (Lattice.triadCycle triad)
cycleRetainedMember {sector = sector} triad
    (leftShell , (rightShell , (outShell , (zeroSum , retainedProof)))) =
  rightShell ,
    (outShell ,
      (leftShell ,
        (Lattice.zeroSumRequired sector _ cycledRetained , cycledRetained)))
  where
  cycledRetained :
    Lattice.retained? sector (Lattice.triadCycle triad) ≡ true
  cycledRetained =
    trans (Lattice.cycleInvariant sector triad) retainedProof

swapRetainedMember :
  ∀ {cutoff sector} (triad : Lattice.LatticeTriad) →
  Lattice.RetainedTriadMember cutoff sector triad →
  Lattice.RetainedTriadMember cutoff sector (Lattice.triadSwap triad)
swapRetainedMember {sector = sector} triad
    (leftShell , (rightShell , (outShell , (zeroSum , retainedProof)))) =
  rightShell ,
    (leftShell ,
      (outShell ,
        (Lattice.zeroSumRequired sector _ swappedRetained , swappedRetained)))
  where
  swappedRetained :
    Lattice.retained? sector (Lattice.triadSwap triad) ≡ true
  swappedRetained =
    trans (Lattice.swapInvariant sector triad) retainedProof

realityRetainedMember :
  ∀ {cutoff sector} (triad : Lattice.LatticeTriad) →
  Lattice.RetainedTriadMember cutoff sector triad →
  Lattice.RetainedTriadMember cutoff sector (Lattice.triadNeg triad)
realityRetainedMember {cutoff} {sector} triad
    (leftShell , (rightShell , (outShell , (zeroSum , retainedProof)))) =
  shellMemberNeg leftShell ,
    (shellMemberNeg rightShell ,
      (shellMemberNeg outShell ,
        (Lattice.zeroSumRequired sector _ negatedRetained , negatedRetained)))
  where
  negatedRetained :
    Lattice.retained? sector (Lattice.triadNeg triad) ≡ true
  negatedRetained =
    trans (Lattice.realityInvariant sector triad) retainedProof

------------------------------------------------------------------------
-- Proof-bearing retained hypergraph and S3 x C2 action.
------------------------------------------------------------------------

record RetainedTriadHyperedge
    (cutoff : Nat)
    (sector : Lattice.ExactRetainedSectorLaw cutoff) : Set where
  constructor retained-triad-hyperedge
  field
    triad : Lattice.LatticeTriad
    retainedMember : Lattice.RetainedTriadMember cutoff sector triad

open RetainedTriadHyperedge public

retainedEdgeMomentumClosure :
  ∀ {cutoff sector}
    (edge : RetainedTriadHyperedge cutoff sector) →
  Lattice.zeroSum? (triad edge) ≡ true
retainedEdgeMomentumClosure edge =
  zeroSumFromMember (retainedMember edge)

cycleEdge :
  ∀ {cutoff sector} →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
cycleEdge edge =
  retained-triad-hyperedge
    (Lattice.triadCycle (triad edge))
    (cycleRetainedMember (triad edge) (retainedMember edge))

swapEdge :
  ∀ {cutoff sector} →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
swapEdge edge =
  retained-triad-hyperedge
    (Lattice.triadSwap (triad edge))
    (swapRetainedMember (triad edge) (retainedMember edge))

realityEdge :
  ∀ {cutoff sector} →
  RetainedTriadHyperedge cutoff sector →
  RetainedTriadHyperedge cutoff sector
realityEdge edge =
  retained-triad-hyperedge
    (Lattice.triadNeg (triad edge))
    (realityRetainedMember (triad edge) (retainedMember edge))

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
factoredActionPreservesMomentumClosure permutation realityChoice edge =
  trans
    (sym
      (cong Lattice.zeroSum?
        (applyFactoredEdgeTriadExact permutation realityChoice edge)))
    (retainedEdgeMomentumClosure
      (applyFactoredEdge permutation realityChoice edge))

record RetainedHypergraphActionClosure
    (cutoff : Nat)
    (sector : Lattice.ExactRetainedSectorLaw cutoff) : Set where
  field
    factoredAction :
      Action.PermutationAction6 →
      Action.RealityAction2 →
      RetainedTriadHyperedge cutoff sector →
      RetainedTriadHyperedge cutoff sector

    factoredActionTriadExact :
      ∀ permutation realityChoice edge →
      triad (factoredAction permutation realityChoice edge)
      ≡ Action.applyFactoredAction permutation realityChoice (triad edge)

    factoredActionMomentum :
      ∀ permutation realityChoice edge →
      Lattice.zeroSum?
        (Action.applyFactoredAction permutation realityChoice (triad edge))
      ≡ true

open RetainedHypergraphActionClosure public

canonicalRetainedHypergraphActionClosure :
  ∀ cutoff sector → RetainedHypergraphActionClosure cutoff sector
canonicalRetainedHypergraphActionClosure cutoff sector = record
  { factoredAction = applyFactoredEdge
  ; factoredActionTriadExact = applyFactoredEdgeTriadExact
  ; factoredActionMomentum = factoredActionPreservesMomentumClosure
  }

------------------------------------------------------------------------
-- Physical active-coupling subgraph.
------------------------------------------------------------------------

record PhysicalCouplingSelectionLaw
    (cutoff : Nat)
    (sector : Lattice.ExactRetainedSectorLaw cutoff) : Set where
  field
    active? : Lattice.LatticeTriad → Bool

    activeImpliesMember : ∀ triad →
      active? triad ≡ true →
      Lattice.RetainedTriadMember cutoff sector triad

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
    activeMember : Lattice.RetainedTriadMember cutoff sector activeTriad

open ActiveTriadHyperedge public

canonicalActiveTriadHyperedge :
  ∀ {cutoff sector}
    (coupling : PhysicalCouplingSelectionLaw cutoff sector)
    (triad : Lattice.LatticeTriad) →
  active? coupling triad ≡ true → ActiveTriadHyperedge coupling
canonicalActiveTriadHyperedge coupling triad activeProof =
  active-triad-hyperedge
    triad activeProof (activeImpliesMember coupling triad activeProof)

activeEdgeMomentumClosure :
  ∀ {cutoff sector coupling}
    (edge : ActiveTriadHyperedge
      {cutoff = cutoff} {sector = sector} coupling) →
  Lattice.zeroSum? (activeTriad edge) ≡ true
activeEdgeMomentumClosure edge =
  zeroSumFromMember (activeMember edge)

physicalCouplingSelectionLawConstructed : Bool
physicalCouplingSelectionLawConstructed = false

physicalCouplingSelectionLawConstructedIsFalse :
  physicalCouplingSelectionLawConstructed ≡ false
physicalCouplingSelectionLawConstructedIsFalse = refl
