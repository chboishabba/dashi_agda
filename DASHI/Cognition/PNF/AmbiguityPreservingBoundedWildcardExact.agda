{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact where

open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Ambiguity-preserving bounded wildcard selection.
--
-- A wildcard demand may have several equally-near physical representatives for
-- one semantic object.  If those representatives disagree in score/provenance,
-- choosing one representative merely to obtain a bounded top-k path would add
-- semantic policy.  Instead, compute a MUST/MAY membership envelope.
--
-- For every admissible representative realization r:
--
--     MUST(c)  ->  Realized r c  ->  MAY(c)
--
-- If MAY collapses into MUST, every admissible realization has exactly the
-- same consumer-visible membership.  Otherwise the correct outcome is an
-- explicit ambiguity residual / abstention, not negative evidence.
------------------------------------------------------------------------

infix 2 _↔_
record _↔_ (A B : Set) : Set where
  constructor iff
  field
    to : A → B
    from : B → A

open _↔_ public

record MembershipEnvelope (Candidate Realization : Set) : Set₁ where
  field
    mustMembership : Candidate → Set
    mayMembership : Candidate → Set
    realizedMembership : Realization → Candidate → Set

    mustSound :
      ∀ realization candidate →
      mustMembership candidate →
      realizedMembership realization candidate

    mayComplete :
      ∀ realization candidate →
      realizedMembership realization candidate →
      mayMembership candidate

open MembershipEnvelope public

-- This is the exact certificate the runtime must establish.  It is stronger
-- than agreement between two particular endpoint realizations: every MAY member
-- must already be a MUST member.
record InvariantTopK
  {Candidate Realization : Set}
  (envelope : MembershipEnvelope Candidate Realization) : Set where
  field
    mayCollapsesToMust :
      ∀ candidate →
      mayMembership envelope candidate →
      mustMembership envelope candidate

open InvariantTopK public

allAdmissibleRealizationsHaveCertifiedMembership :
  ∀ {Candidate Realization : Set}
    (envelope : MembershipEnvelope Candidate Realization) →
    InvariantTopK envelope →
    (realization : Realization) →
    (candidate : Candidate) →
    realizedMembership envelope realization candidate
      ↔ mustMembership envelope candidate
allAdmissibleRealizationsHaveCertifiedMembership envelope invariant realization candidate =
  iff
    (λ realized →
      mayCollapsesToMust invariant candidate
        (mayComplete envelope realization candidate realized))
    (mustSound envelope realization candidate)

------------------------------------------------------------------------
-- Outcome boundary.
--
-- Failure to establish InvariantTopK is not candidate absence and is not a
-- failed demand.  The unresolved ambiguity remains explicit so the existing
-- DemandResolutionState / ReferenceModeOutcomes machinery can keep the demand
-- open or route it to a slower authority-preserving fallback.
------------------------------------------------------------------------

data BoundedWildcardOutcome
  {Candidate Realization : Set}
  (envelope : MembershipEnvelope Candidate Realization) : Set where
  certifiedTopK :
    InvariantTopK envelope →
    BoundedWildcardOutcome envelope
  ambiguousResidual :
    BoundedWildcardOutcome envelope

certifiedOutcomePreservesEveryRealization :
  ∀ {Candidate Realization : Set}
    {envelope : MembershipEnvelope Candidate Realization} →
    InvariantTopK envelope →
    (realization : Realization) →
    (candidate : Candidate) →
    realizedMembership envelope realization candidate
      ↔ mustMembership envelope candidate
certifiedOutcomePreservesEveryRealization {envelope = envelope} =
  allAdmissibleRealizationsHaveCertifiedMembership envelope

------------------------------------------------------------------------
-- Consumer-safe compression bridge.
--
-- A bounded physical carrier is permitted to replace the broad wildcard
-- relation only when it carries a certified invariant membership.  Ambiguous
-- fibres stay explicit rather than being compressed into a chosen score row.
------------------------------------------------------------------------

record AmbiguityPreservingBoundedWildcard
  (Candidate Realization Provenance Residual : Set) : Set₁ where
  field
    envelope : MembershipEnvelope Candidate Realization
    provenance : Provenance
    residual : Residual
    outcome : BoundedWildcardOutcome envelope

open AmbiguityPreservingBoundedWildcard public
