module DASHI.Core.AuthorityPreservingFutureAbstractionExact where

------------------------------------------------------------------------
-- AUTHORITY-PRESERVING FUTURE ABSTRACTION
--
-- ConsumerIndexedGovernedTransitionExact already proves the key action,
-- observation and authority commuting square.  The attached cross-domain notes
-- identify one missing coordinate: a consumer decision may be a strict
-- downstream projection of the observation and should be preserved explicitly,
-- not assumed from authority or observational equality by prose.
--
-- Calibration:
-- Patrick Cousot and Radhia Cousot, "Abstract interpretation: a unified lattice
-- model for static analysis of programs by construction or approximation of
-- fixpoints", POPL 1977. DOI: 10.1145/512950.512973.
-- David Blackwell, "Equivalent Comparisons of Experiments", Annals of
-- Mathematical Statistics 24(2), 1953. DOI: 10.1214/aoms/1177729032.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed

------------------------------------------------------------------------
-- Decision projection on fine and coarse carriers.
------------------------------------------------------------------------

record DecisionPreservingAbstraction
    {Fine Coarse Action Consumer Observation Decision : Set}
    (fine : Governed.ConsumerIndexedGovernedTransition
      Fine Action Consumer Observation)
    (project : Fine → Coarse)
    (safe : Governed.ConsumerSafeAbstraction fine project) : Set₁ where
  constructor decisionPreservingAbstraction
  field
    fineDecision : Consumer → Fine → Decision
    coarseDecision : Consumer → Coarse → Decision
    decisionDescends :
      ∀ consumer state →
      fineDecision consumer state
      ≡ coarseDecision consumer (project state)

open DecisionPreservingAbstraction public

sameProjectionSameDecision :
  ∀ {Fine Coarse Action Consumer Observation Decision}
    {fine : Governed.ConsumerIndexedGovernedTransition
      Fine Action Consumer Observation}
    {project : Fine → Coarse}
    {safe : Governed.ConsumerSafeAbstraction fine project}
    (decision : DecisionPreservingAbstraction fine project safe)
    (consumer : Consumer)
    {left right : Fine} →
  project left ≡ project right →
  fineDecision decision consumer left
  ≡ fineDecision decision consumer right
sameProjectionSameDecision decision consumer {left} {right} same
  rewrite decisionDescends decision consumer left
        | decisionDescends decision consumer right
        | same = refl

------------------------------------------------------------------------
-- The full same-fibre obligation at a declared horizon: future observations,
-- current decision and current authority all agree.
------------------------------------------------------------------------

record GovernedFutureAgreement
    {Fine Action Consumer Observation Decision : Set}
    (fine : Governed.ConsumerIndexedGovernedTransition
      Fine Action Consumer Observation)
    (decision : Consumer → Fine → Decision)
    (consumer : Consumer)
    (depth : Nat)
    (left right : Fine) : Set where
  constructor governedFutureAgreement
  field
    futureEquivalent :
      Governed.FutureEquivalent fine consumer depth left right
    sameDecision : decision consumer left ≡ decision consumer right
    sameAuthority :
      Governed.authority fine consumer left
      ≡ Governed.authority fine consumer right

open GovernedFutureAgreement public

sameProjectionGivesGovernedFutureAgreement :
  ∀ {Fine Coarse Action Consumer Observation Decision}
    {fine : Governed.ConsumerIndexedGovernedTransition
      Fine Action Consumer Observation}
    {project : Fine → Coarse}
    (safe : Governed.ConsumerSafeAbstraction fine project)
    (decision : DecisionPreservingAbstraction fine project safe)
    (consumer : Consumer)
    (depth : Nat)
    {left right : Fine} →
  project left ≡ project right →
  GovernedFutureAgreement fine (fineDecision decision)
    consumer depth left right
sameProjectionGivesGovernedFutureAgreement safe decision consumer depth {left} {right} same =
  governedFutureAgreement
    (Governed.sameProjectionFutureEquivalent safe consumer depth same)
    (sameProjectionSameDecision decision consumer same)
    (Governed.sameProjectionSameAuthority safe consumer same)

------------------------------------------------------------------------
-- This is the intended generic safety criterion:
--
--   consumer-relative + future-safe + decision-preserving + authority-preserving
--
-- It is stronger than present-observation equality and weaker than world-state
-- identity.
------------------------------------------------------------------------
