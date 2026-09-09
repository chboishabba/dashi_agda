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
--   pos : at least one inspected candidate pays the declared Boolean consumer;
--   neg : a typed complete finite search domain has been exhausted and no
--         admissible candidate pays that consumer;
--   zer : no paying candidate has been found in an open/incomplete scope.
--
-- This preserves the proof-debt router's existing separation between
-- mathematical status, statement alignment, certification and scheduling.
------------------------------------------------------------------------

-- Local finite membership avoids adding an equality/decidability requirement
-- to the candidate carrier.
data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- A complete finite domain must state which candidates are admissible and prove
-- that every admissible candidate occurs in the inspected list.
record CompleteFiniteSearchDomain (A : Set) : Set₁ where
  constructor completeFiniteSearchDomain
  field
    candidates : List A
    Admissible : A → Set
    coversEveryAdmissible : (candidate : A) → Admissible candidate → candidate ∈ candidates

open CompleteFiniteSearchDomain public

data SearchScope (A : Set) : Set₁ where
  openFiniteScope : List A → SearchScope A
  completeFiniteScope : CompleteFiniteSearchDomain A → SearchScope A

scopeCandidates : ∀ {A : Set} → SearchScope A → List A
scopeCandidates (openFiniteScope candidates) = candidates
scopeCandidates (completeFiniteScope domain) = candidates domain

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
  SearchScope A →
  Trit
finiteSearchDecisionTrit checker scope with anyPassing checker (scopeCandidates scope)
... | true = pos
... | false with scope
...   | openFiniteScope _ = zer
...   | completeFiniteScope _ = neg

------------------------------------------------------------------------
-- Existing proof-search fixture: authoritative frontier reduction rather than
-- lemma count is the declared consumer.
------------------------------------------------------------------------

canonicalSearchCandidates : List ProofSearch.SearchState
canonicalSearchCandidates =
  ProofSearch.manyLemmasNoClosure
  ∷ ProofSearch.fewerLemmasTrueClosure
  ∷ []

allSearchStatesAdmissible : ProofSearch.SearchState → Set
allSearchStatesAdmissible _ = ⊤

canonicalSearchCoverage :
  (candidate : ProofSearch.SearchState) →
  allSearchStatesAdmissible candidate →
  candidate ∈ canonicalSearchCandidates
canonicalSearchCoverage ProofSearch.manyLemmasNoClosure admissible = here
canonicalSearchCoverage ProofSearch.fewerLemmasTrueClosure admissible = there here

canonicalCompleteDomain : CompleteFiniteSearchDomain ProofSearch.SearchState
canonicalCompleteDomain =
  completeFiniteSearchDomain
    canonicalSearchCandidates
    allSearchStatesAdmissible
    canonicalSearchCoverage

nonClosingCandidateOnly : List ProofSearch.SearchState
nonClosingCandidateOnly = ProofSearch.manyLemmasNoClosure ∷ []

-- This complete domain is intentionally restricted to one declared admissible
-- candidate.  Its negative result is therefore only about this bounded domain,
-- not about all possible proof routes or theorem truth.
nonClosingOnlyAdmissible : ProofSearch.SearchState → Set
nonClosingOnlyAdmissible ProofSearch.manyLemmasNoClosure = ⊤
nonClosingOnlyAdmissible ProofSearch.fewerLemmasTrueClosure = ⊥

nonClosingOnlyCoverage :
  (candidate : ProofSearch.SearchState) →
  nonClosingOnlyAdmissible candidate →
  candidate ∈ nonClosingCandidateOnly
nonClosingOnlyCoverage ProofSearch.manyLemmasNoClosure admissible = here
nonClosingOnlyCoverage ProofSearch.fewerLemmasTrueClosure ()

nonClosingCompleteDomain : CompleteFiniteSearchDomain ProofSearch.SearchState
nonClosingCompleteDomain =
  completeFiniteSearchDomain
    nonClosingCandidateOnly
    nonClosingOnlyAdmissible
    nonClosingOnlyCoverage

canonicalCompleteSearchFindsClosure :
  finiteSearchDecisionTrit
    ProofSearch.authoritativeFrontierReduced
    (completeFiniteScope canonicalCompleteDomain)
  ≡ pos
canonicalCompleteSearchFindsClosure = refl

completeNonClosingSearchIsNegative :
  finiteSearchDecisionTrit
    ProofSearch.authoritativeFrontierReduced
    (completeFiniteScope nonClosingCompleteDomain)
  ≡ neg
completeNonClosingSearchIsNegative = refl

incompleteNonClosingSearchStaysUnresolved :
  finiteSearchDecisionTrit
    ProofSearch.authoritativeFrontierReduced
    (openFiniteScope nonClosingCandidateOnly)
  ≡ zer
incompleteNonClosingSearchStaysUnresolved = refl

-- The same inspected candidate list can therefore refine zer -> neg only when
-- a typed finite-domain coverage receipt is supplied.
incompleteToCompleteNegativeRefinement : Refinement.DecisionRefines zer neg
incompleteToCompleteNegativeRefinement = Refinement.unresolvedBecomesNegative

-- And adding a paying candidate can refine an unresolved search to positive.
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
-- regardless of whether a local finite candidate search is unresolved,
-- successful, or exhausted within a declared bounded domain.
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
data OpenSearchFailureMayBeNegative : Set where

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

openSearchFailureCannotBePromotedNegative :
  OpenSearchFailureMayBeNegative → ⊥
openSearchFailureCannotBePromotedNegative ()

record TernaryProofSearchDecisionDebtBoundary : Set where
  constructor ternaryProofSearchDecisionDebtBoundary
  field
    positiveMeansPayingCandidateFound : Bool
    negativeRequiresTypedFiniteCoverage : Bool
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
