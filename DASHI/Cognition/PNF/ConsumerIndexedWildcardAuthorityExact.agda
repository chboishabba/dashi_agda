{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.ConsumerIndexedWildcardAuthorityExact where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- CONSUMER-INDEXED AUTHORITY
--
-- Planner coordinates may be retained for execution/history without becoming
-- semantic authority.  A compression is exact for a declared consumer when the
-- observation seen by that consumer is unchanged; this does not reconstruct
-- every planner field.
------------------------------------------------------------------------

record ConsumerIndexedAuthority (Fine Coarse Observation : Set) : Set₁ where
  field
    observeFine : Fine → Observation
    observeCoarse : Coarse → Observation

open ConsumerIndexedAuthority public

record ConsumerExact
  {Fine Coarse Observation : Set}
  (authority : ConsumerIndexedAuthority Fine Coarse Observation)
  (fine : Fine)
  (coarse : Coarse) : Set where
  field
    observationParity :
      observeCoarse authority coarse ≡ observeFine authority fine

open ConsumerExact public

consumerExactnessIsObservationRelative :
  ∀ {Fine Coarse Observation : Set}
    {authority : ConsumerIndexedAuthority Fine Coarse Observation}
    {fine : Fine} {coarse : Coarse} →
  ConsumerExact authority fine coarse →
  observeCoarse authority coarse ≡ observeFine authority fine
consumerExactnessIsObservationRelative = observationParity

------------------------------------------------------------------------
-- Runtime specialization.
-- Membership/count/unique-target/outcome/provenance form the semantic resolution
-- observation.  Ordinal/distance/rank/score may remain execution observations.
------------------------------------------------------------------------

record ResolutionAuthorityObservation
  (Membership Count UniqueTarget Outcome Provenance : Set) : Set where
  constructor resolutionAuthorityObservation
  field
    membership : Membership
    candidateCount : Count
    uniqueTarget : UniqueTarget
    outcome : Outcome
    membershipProvenance : Provenance

record PlannerExecutionObservation
  (Ordinal Distance Rank Score : Set) : Set where
  constructor plannerExecutionObservation
  field
    ordinal : Ordinal
    distance : Distance
    rank : Rank
    score : Score

------------------------------------------------------------------------
-- No eliminator permits semantic parity to manufacture equality of planner
-- observations.  This pins the migration-086 boundary formally.
------------------------------------------------------------------------

data SemanticParityImpliesPlannerIdentityPermission : Set where

semanticParityCannotManufacturePlannerIdentity :
  SemanticParityImpliesPlannerIdentityPermission →
  ∀ {A : Set} → A
semanticParityCannotManufacturePlannerIdentity ()
