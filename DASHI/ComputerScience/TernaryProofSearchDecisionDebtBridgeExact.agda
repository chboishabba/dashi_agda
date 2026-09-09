module DASHI.ComputerScience.TernaryProofSearchDecisionDebtBridgeExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.ComputerScience.TernarySemanticDecisionRefinementExact as Refinement

------------------------------------------------------------------------
-- TERNARY FINITE PROOF-SEARCH STATUS × PROOF-DEBT ROUTING
--
-- Search status is not theorem truth and not certification status:
--
--   pos : at least one candidate in the inspected list pays the declared
--         Boolean proof-search consumer;
--   neg : the declared candidate space is complete and every inspected
--         candidate fails that consumer;
--   zer : no paying candidate has been found, but the search space is not
--         certified complete/exhausted.
--
-- This preserves the proof-debt router's existing separation between
-- mathematical status, statement alignment, certification and scheduling.
------------------------------------------------------------------------

anyPassing :
  ∀ {A : Set} →
  (A → Bool) →
  List A →
  Bool
anyPassing checker [] = false
anyPassing checker (candidate ∷ candidates) with checker candidate
... | true = true
... | false = anyPassing checker candidates

finiteSearchDecisionTrit :
  ∀ {A : Set} →
  (A → Bool) →
  List A →
  Bool →
  Trit
finiteSearchDecisionTrit checker candidates searchSpaceComplete
  with anyPassing checker candidates
... | true = pos
... | false with searchSpaceComplete
...   | true = neg
...   | false = zer

------------------------------------------------------------------------
-- Existing proof-search fixture: authoritative frontier reduction rather than
-- lemma count is the declared consumer.
------------------------------------------------------------------------

canonicalSearchCandidates : List ProofSearch.SearchState
canonicalSearchCandidates =
  ProofSearch.manyLemmasNoClosure
  ∷ ProofSearch.fewerLemmasTrueClosure
  ∷ []

nonClosingCandidateOnly : List ProofSearch.SearchState
nonClosingCandidateOnly =
  ProofSearch.manyLemmasNoClosure ∷ []

canonicalCompleteSearchFindsClosure :
  finiteSearchDecisionTrit
    ProofSearch.authoritativeFrontierReduced
    canonicalSearchCandidates
    true
  ≡ pos
canonicalCompleteSearchFindsClosure = refl

completeNonClosingSearchIsNegative :
  finiteSearchDecisionTrit
    ProofSearch.authoritativeFrontierReduced
    nonClosingCandidateOnly
    true
  ≡ neg
completeNonClosingSearchIsNegative = refl

incompleteNonClosingSearchStaysUnresolved :
  finiteSearchDecisionTrit
    ProofSearch.authoritativeFrontierReduced
    nonClosingCandidateOnly
    false
  ≡ zer
incompleteNonClosingSearchStaysUnresolved = refl

-- The same candidate evidence can therefore refine zer -> neg solely when an
-- explicit completeness/exhaustion coordinate becomes available.
incompleteToCompleteNegativeRefinement : Refinement.DecisionRefines zer neg
incompleteToCompleteNegativeRefinement = Refinement.unresolvedBecomesNegative

-- And adding the paying candidate refines an unresolved search to positive.
unresolvedToPositiveProofSearchRefinement : Refinement.DecisionRefines zer pos
unresolvedToPositiveProofSearchRefinement = Refinement.unresolvedBecomesPositive

------------------------------------------------------------------------
-- Search status is a product coordinate beside proof-debt routing.
------------------------------------------------------------------------

record ProofSearchDecisionPacket : Set where
  constructor proofSearchDecisionPacket
  field
    searchDecision : Trit
    debtRoute : Debt.ProofDebtRoutingReceipt
    routeAdmission : ProofSearch.RouteAdmission

open ProofSearchDecisionPacket public

-- A source-established, source-aligned theorem may remain certification debt
-- regardless of whether a local finite candidate search is still unresolved.
canonicalDeferredUnresolvedPacket : ProofSearchDecisionPacket
canonicalDeferredUnresolvedPacket =
  proofSearchDecisionPacket
    zer
    Debt.canonicalEstablishedDeferredRoute
    ProofSearch.canonicalRouteAdmission

canonicalDeferredPositiveSearchPacket : ProofSearchDecisionPacket
canonicalDeferredPositiveSearchPacket =
  proofSearchDecisionPacket
    pos
    Debt.canonicalEstablishedDeferredRoute
    ProofSearch.canonicalRouteAdmission

canonicalDeferredNegativeFiniteSearchPacket : ProofSearchDecisionPacket
canonicalDeferredNegativeFiniteSearchPacket =
  proofSearchDecisionPacket
    neg
    Debt.canonicalEstablishedDeferredRoute
    ProofSearch.canonicalRouteAdmission

-- All three search statuses can coexist with the same certification-debt route.
unresolvedPacketRemainsCertificationDebt :
  Debt.routedDebt (debtRoute canonicalDeferredUnresolvedPacket)
  ≡ Debt.certificationDebt
unresolvedPacketRemainsCertificationDebt = refl

positiveSearchPacketRemainsCertificationDebt :
  Debt.routedDebt (debtRoute canonicalDeferredPositiveSearchPacket)
  ≡ Debt.certificationDebt
positiveSearchPacketRemainsCertificationDebt = refl

negativeFiniteSearchPacketRemainsCertificationDebt :
  Debt.routedDebt (debtRoute canonicalDeferredNegativeFiniteSearchPacket)
  ≡ Debt.certificationDebt
negativeFiniteSearchPacketRemainsCertificationDebt = refl

------------------------------------------------------------------------
-- Least-privilege / epistemic firewalls.
------------------------------------------------------------------------

data NegativeFiniteSearchMeansTheoremFalse : Set where
data PositiveSearchMeansKernelCertified : Set where
data UnresolvedSearchMeansMathematicalDebt : Set where
data SearchDecisionReplacesDebtRouting : Set where
data TheoremNameIsSearchWitness : Set where

data IncompleteSearchFailureMayBeNegative : Set where

negativeFiniteSearchDoesNotMeanTheoremFalse :
  NegativeFiniteSearchMeansTheoremFalse → ⊥
negativeFiniteSearchDoesNotMeanTheoremFalse ()

positiveSearchDoesNotMeanKernelCertified :
  PositiveSearchMeansKernelCertified → ⊥
positiveSearchDoesNotMeanKernelCertified ()

unresolvedSearchDoesNotMeanMathematicalDebt :
  UnresolvedSearchMeansMathematicalDebt → ⊥
unresolvedSearchDoesNotMeanMathematicalDebt ()

searchDecisionDoesNotReplaceDebtRouter :
  SearchDecisionReplacesDebtRouting → ⊥
searchDecisionDoesNotReplaceDebtRouter ()

theoremNameDoesNotBecomeSearchWitness :
  TheoremNameIsSearchWitness → ⊥
theoremNameDoesNotBecomeSearchWitness ()

incompleteFailureCannotBePromotedNegative :
  IncompleteSearchFailureMayBeNegative → ⊥
incompleteFailureCannotBePromotedNegative ()

record TernaryProofSearchDecisionDebtBoundary : Set where
  constructor ternaryProofSearchDecisionDebtBoundary
  field
    positiveMeansPayingCandidateFound : Bool
    negativeRequiresCompleteFiniteSearch : Bool
    incompleteNoCandidateStaysUnresolved : Bool
    searchStatusSeparateFromTheoremTruth : Bool
    searchStatusSeparateFromCertification : Bool
    proofDebtRouterReused : Bool
    leastPrivilegeAdmissionReused : Bool
    negativeFiniteSearchPromotedToTheoremRefutation : Bool
    positiveSearchPromotedToKernelCertification : Bool

canonicalTernaryProofSearchDecisionDebtBoundary :
  TernaryProofSearchDecisionDebtBoundary
canonicalTernaryProofSearchDecisionDebtBoundary =
  ternaryProofSearchDecisionDebtBoundary
    true true true true true true true false false
