module DASHI.Reasoning.TrialecticPolicyIndexedAllDepthIterationExact where

------------------------------------------------------------------------
-- POLICY-INDEXED ALL-DEPTH ITERATION
--
-- A carry seed does not determine a unique next T18+face state.  That no-go is
-- retained.  Here we prove the complementary positive result: once mediation
-- and expansion policies are supplied explicitly, coherent iteration through
-- every finite depth is constructible by Nat recursion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticThreeCellCarryDepthExact as Carry
import DASHI.Reasoning.TrialecticCarryDepthExpansionPolicyExact as Expansion

record AllDepthPolicy : Set₁ where
  constructor all-depth-policy
  field
    gluingAt :
      (depth : Nat) →
      (state : Cell.StructuredTrialecticState) →
      Cell.SecondOrderCellGluing state

    expansionAt :
      (depth : Nat) →
      (state : Cell.StructuredTrialecticState) →
      Expansion.NextStructuredExpansionPolicy

open AllDepthPolicy public

nextWithPolicy :
  AllDepthPolicy →
  (depth : Nat) →
  Cell.StructuredTrialecticState →
  Cell.StructuredTrialecticState
nextWithPolicy policy depth state =
  Expansion.expandCarryStep
    (expansionAt policy depth state)
    (Carry.promoteWithFaceGluing
      depth state (gluingAt policy depth state))

iterateWithPolicy :
  AllDepthPolicy →
  Cell.StructuredTrialecticState →
  Nat →
  Cell.StructuredTrialecticState
iterateWithPolicy policy initial zero = initial
iterateWithPolicy policy initial (suc depth) =
  nextWithPolicy policy depth (iterateWithPolicy policy initial depth)

iterationStepCoherence :
  (policy : AllDepthPolicy) →
  (initial : Cell.StructuredTrialecticState) →
  (depth : Nat) →
  iterateWithPolicy policy initial (suc depth)
  ≡
  nextWithPolicy policy depth (iterateWithPolicy policy initial depth)
iterationStepCoherence policy initial depth = refl

------------------------------------------------------------------------
-- A fully inhabited formal policy.  Its mediation relation is deliberately
-- minimal (Top): this is a structural existence witness, not an empirical or
-- normative dynamics claim.
------------------------------------------------------------------------

structuralGluing :
  (state : Cell.StructuredTrialecticState) →
  Cell.SecondOrderCellGluing state
structuralGluing state = record
  { Cell.outputCell =
      Cell.leftCell
        (Cell.edgeAB (Cell.structuredBoundary state))
  ; Cell.mediates = λ face ab bc ca output → ⊤
  ; Cell.mediationReceipt = tt
  }

structuralAllDepthPolicy : AllDepthPolicy
structuralAllDepthPolicy =
  all-depth-policy
    (λ depth state → structuralGluing state)
    (λ depth state → Expansion.originReciprocalPolicy)

canonicalAllDepthTrajectory :
  Nat → Cell.StructuredTrialecticState
canonicalAllDepthTrajectory =
  iterateWithPolicy structuralAllDepthPolicy Cell.structuredReciprocal

canonicalAllDepthTrajectoryStep :
  (depth : Nat) →
  canonicalAllDepthTrajectory (suc depth)
  ≡
  nextWithPolicy
    structuralAllDepthPolicy depth (canonicalAllDepthTrajectory depth)
canonicalAllDepthTrajectoryStep depth = refl

record TrialecticPolicyIndexedAllDepthBoundary : Set where
  constructor trialectic-policy-indexed-all-depth-boundary
  field
    mediationPolicyExplicit : Bool
    expansionPolicyExplicit : Bool
    finiteDepthTrajectoryConstructed : Bool
    oneStepCoherenceAtEveryDepthPaid : Bool
    inhabitedAllDepthPolicyConstructed : Bool
    allDepthIterationExistsGivenPolicy : Bool
    carrySeedUniquelyDeterminesPolicy : Bool
    empiricalDynamicsClaimed : Bool

open TrialecticPolicyIndexedAllDepthBoundary public

canonicalTrialecticPolicyIndexedAllDepthBoundary :
  TrialecticPolicyIndexedAllDepthBoundary
canonicalTrialecticPolicyIndexedAllDepthBoundary =
  trialectic-policy-indexed-all-depth-boundary
    true true true true true true false false
