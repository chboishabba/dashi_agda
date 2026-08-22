{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.HybridWildcardTemporalEligibilityRegression where

open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DEMAND-LOCAL ELIGIBILITY REGRESSION
--
-- A global representative is not generally a safe substitute for the nearest
-- representative eligible at one demand position.  This finite witness pins the
-- exact failure mode found while preparing consumer-tuple parity:
-- an object can have an earlier admissible occurrence and a later occurrence
-- after the demand.  Collapsing globally first hides the admissible occurrence.
------------------------------------------------------------------------

data Occurrence : Set where
  earlierOccurrence laterOccurrence : Occurrence

data Demand : Set where
  demandBetweenOccurrences : Demand

data Eligible : Demand → Occurrence → Set where
  earlierIsEligible : Eligible demandBetweenOccurrences earlierOccurrence

data GloballyLatest : Occurrence → Set where
  laterIsGloballyLatest : GloballyLatest laterOccurrence

laterIsNotEligible :
  Eligible demandBetweenOccurrences laterOccurrence → ⊥
laterIsNotEligible ()

globalLatestCanHideDemandLocalWitness :
  GloballyLatest laterOccurrence
  × Eligible demandBetweenOccurrences earlierOccurrence
  × (Eligible demandBetweenOccurrences laterOccurrence → ⊥)
globalLatestCanHideDemandLocalWitness =
  laterIsGloballyLatest , earlierIsEligible , laterIsNotEligible

------------------------------------------------------------------------
-- Consequently any bounded theorem using one globally-collapsed object row must
-- carry an additional proof that no eligible earlier representative is shadowed,
-- or compute the representative after applying the demand-local time predicate.
------------------------------------------------------------------------

data GlobalCollapseWithoutShadowProofPermission : Set where

globalCollapseNeedsTemporalShadowProof :
  GlobalCollapseWithoutShadowProofPermission → ⊥
globalCollapseNeedsTemporalShadowProof ()
