module DASHI.Core.ReopenableQuotientForestExact where

------------------------------------------------------------------------
-- Branch compression must retain residual ancestry.  Computational exclusion
-- is not refutation: members hidden behind a quotient representative remain
-- individually reopenable unless domain evidence actually refutes them.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base

record ReopenableQuotientForest
    (Branch Coarse : Set) : Set₁ where
  constructor reopenableQuotientForest
  field
    project : Branch → Coarse
    Parent : Branch → Branch → Set
    status : Branch → Base.AlternativeStatus
    provenance : Branch → List String
    activeBranches : List Branch
    activeBound : Nat

open ReopenableQuotientForest public

record ResidualQuotientMember
    {Branch Coarse : Set}
    (forest : ReopenableQuotientForest Branch Coarse) : Set₁ where
  constructor residualQuotientMember
  field
    representative : Branch
    residual : Branch
    sameCoarseClass :
      project forest representative ≡ project forest residual
    residualIsReopenable : status forest residual ≡ Base.reopenable

open ResidualQuotientMember public

reopenableIsNotRefuted : Base.reopenable ≡ Base.refuted → ⊥
reopenableIsNotRefuted ()

residualCompressionDoesNotRefuteMember :
  ∀ {Branch Coarse}
    {forest : ReopenableQuotientForest Branch Coarse} →
  (member : ResidualQuotientMember forest) →
  status forest (residual member) ≡ Base.refuted →
  ⊥
residualCompressionDoesNotRefuteMember member claimedRefuted =
  reopenableIsNotRefuted
    (trans (sym (residualIsReopenable member)) claimedRefuted)

record BranchSplit
    {Branch Coarse : Set}
    (forest : ReopenableQuotientForest Branch Coarse)
    (parent : Branch) : Set₁ where
  constructor branchSplit
  field
    left right : Branch
    leftChild : Parent forest parent left
    rightChild : Parent forest parent right
    distinctChildren : left ≡ right → ⊥

open BranchSplit public

record ReopenableQuotientForestBoundary : Set where
  constructor reopenableQuotientForestBoundary
  field
    quotientingNeedNotEraseBranchIdentity : Bool
    residualMemberCanRemainReopenable : Bool
    pruningFromActiveSetIsNotRefutation : Bool
    branchAncestryIsRetained : Bool
    boundedActiveSetDoesNotImplyBoundedResidualHistory : Bool

canonicalReopenableQuotientForestBoundary :
  ReopenableQuotientForestBoundary
canonicalReopenableQuotientForestBoundary =
  reopenableQuotientForestBoundary true true true true true
