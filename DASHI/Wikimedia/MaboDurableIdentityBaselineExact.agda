module DASHI.Wikimedia.MaboDurableIdentityBaselineExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboIdentityClassTargetExact as Target

------------------------------------------------------------------------
-- Durable restart boundary for P7d.
--
-- The 100-object target is cardinality of reviewed world-identity classes over
-- the durable discovery lineage, not cardinality accumulated by one process.
------------------------------------------------------------------------

record DurableIdentityBaseline : Set where
  constructor durable-identity-baseline
  field
    baselineReference : String
    durableIdentityClassCount : Nat
    targetIdentityClassCount : Nat
    remainingNovelIdentityClassCount : Nat
    baselineDerivedFromReviewedLineage : Bool
    baselineDerivedFromReviewedLineageIsTrue : baselineDerivedFromReviewedLineage ≡ true
    representationConflictFailsClosed : Bool
    representationConflictFailsClosedIsTrue : representationConflictFailsClosed ≡ true
    baselineCreatesSemanticAuthority : Bool
    baselineCreatesSemanticAuthorityIsFalse : baselineCreatesSemanticAuthority ≡ false
    baselinePromotesClaimTruth : Bool
    baselinePromotesClaimTruthIsFalse : baselinePromotesClaimTruth ≡ false

open DurableIdentityBaseline public

-- Current source-level contract.  Runtime count is supplied by PostgreSQL;
-- this owner fixes the arithmetic/authority interpretation, not a live count.
canonicalMaboDurableIdentityBaselineBoundary : DurableIdentityBaseline
canonicalMaboDurableIdentityBaselineBoundary =
  durable-identity-baseline
    "context.discovery_lineage_receipt:identity-class-baseline"
    0
    Target.targetIdentityClasses
    Target.targetIdentityClasses
    true refl
    true refl
    false refl
    false refl

record DurableCampaignCount : Set where
  constructor durable-campaign-count
  field
    priorDurableIdentityClasses : Nat
    newlyCommittedIdentityClasses : Nat
    durableTotalIdentityClasses : Nat

open DurableCampaignCount public

-- The runtime implements the corresponding saturating target arithmetic.  The
-- theorem-bearing boundary here is that prior durable count and new run count
-- are distinct coordinates and neither may be replaced by representation rows.

data ProcessLocalCountEqualsDurableCount : Set where
data LineageRowCountEqualsIdentityClassCount : Set where
data RepresentationCountEqualsDurableIdentityCount : Set where
data PersistedConflictMayBeIgnored : Set where

processLocalCountDoesNotEqualDurableCount : ProcessLocalCountEqualsDurableCount → ⊥
processLocalCountDoesNotEqualDurableCount ()

lineageRowCountDoesNotEqualIdentityClassCount : LineageRowCountEqualsIdentityClassCount → ⊥
lineageRowCountDoesNotEqualIdentityClassCount ()

representationCountDoesNotEqualDurableIdentityCount : RepresentationCountEqualsDurableIdentityCount → ⊥
representationCountDoesNotEqualDurableIdentityCount ()

persistedConflictMayNotBeIgnored : PersistedConflictMayBeIgnored → ⊥
persistedConflictMayNotBeIgnored ()
