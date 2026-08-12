module DASHI.Core.PossibilityAccessibilitySupport where

------------------------------------------------------------------------
-- Three independent axes used throughout bounded inference.
--
-- Semantic possibility, current computational accessibility, and current
-- evidentiary support are separate indexed propositions.  The core supplies no
-- implication between them; any such implication must be application evidence.
------------------------------------------------------------------------

record PossibilityAccessibilitySupport (Candidate : Set) : Set₁ where
  constructor possibilityAccessibilitySupport
  field
    SemanticallyPossible : Candidate → Set
    ComputationallyAccessible : Candidate → Set
    EvidentiallySupported : Candidate → Set

open PossibilityAccessibilitySupport public

record CandidateAxisWitness
    {Candidate : Set}
    (axes : PossibilityAccessibilitySupport Candidate)
    (candidate : Candidate) : Set₁ where
  constructor candidateAxisWitness
  field
    semanticPossibility : SemanticallyPossible axes candidate
    computationalAccessibility : ComputationallyAccessible axes candidate
    evidentiarySupport : EvidentiallySupported axes candidate

open CandidateAxisWitness public
