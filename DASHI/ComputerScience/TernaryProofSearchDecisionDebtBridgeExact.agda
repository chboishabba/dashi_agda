module DASHI.ComputerScience.TernaryProofSearchDecisionDebtBridgeExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.ComputerScience.ConsumerIndexedTernarySearchKernelExact as Search
import DASHI.ComputerScience.TernarySemanticDecisionRefinementExact as Refinement

------------------------------------------------------------------------
-- PROOF-SEARCH SPECIALISATION OF THE GENERIC TERNARY SEARCH KERNEL
--
-- The generic kernel owns finite scope, coverage and ternary aggregation.
-- This module owns proof-search semantics: least-privilege route admission,
-- proof-debt routing, and the exact frontier-reduction consumer.
------------------------------------------------------------------------

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
  Search._∈_ candidate canonicalSearchCandidates
canonicalSearchCoverage ProofSearch.manyLemmasNoClosure admissible = Search.here
canonicalSearchCoverage ProofSearch.fewerLemmasTrueClosure admissible = Search.there Search.here

canonicalCompleteDomain : Search.CompleteFiniteSearchDomain ProofSearch.SearchState
canonicalCompleteDomain =
  Search.completeFiniteSearchDomain
    canonicalSearchCandidates
    allSearchStatesAdmissible
    canonicalSearchCoverage

nonClosingCandidateOnly : List ProofSearch.SearchState
nonClosingCandidateOnly = ProofSearch.manyLemmasNoClosure ∷ []

nonClosingOnlyAdmissible : ProofSearch.SearchState → Set
nonClosingOnlyAdmissible ProofSearch.manyLemmasNoClosure = ⊤
nonClosingOnlyAdmissible ProofSearch.fewerLemmasTrueClosure = ⊥

nonClosingOnlyCoverage :
  (candidate : ProofSearch.SearchState) →
  nonClosingOnlyAdmissible candidate →
  Search._∈_ candidate nonClosingCandidateOnly
nonClosingOnlyCoverage ProofSearch.manyLemmasNoClosure admissible = Search.here
nonClosingOnlyCoverage ProofSearch.fewerLemmasTrueClosure ()

nonClosingCompleteDomain : Search.CompleteFiniteSearchDomain ProofSearch.SearchState
nonClosingCompleteDomain =
  Search.completeFiniteSearchDomain
    nonClosingCandidateOnly
    nonClosingOnlyAdmissible
    nonClosingOnlyCoverage

canonicalCompleteSearchFindsClosure :
  Search.searchDecision
    ProofSearch.authoritativeFrontierReduced
    (Search.completeFiniteScope canonicalCompleteDomain)
  ≡ pos
canonicalCompleteSearchFindsClosure = refl

completeNonClosingSearchIsNegative :
  Search.searchDecision
    ProofSearch.authoritativeFrontierReduced
    (Search.completeFiniteScope nonClosingCompleteDomain)
  ≡ neg
completeNonClosingSearchIsNegative = refl

incompleteNonClosingSearchStaysUnresolved :
  Search.searchDecision
    ProofSearch.authoritativeFrontierReduced
    (Search.openFiniteScope nonClosingCandidateOnly)
  ≡ zer
incompleteNonClosingSearchStaysUnresolved = refl

-- Search refinement agrees with the already-established bounded semantic
-- refinement relation, while ownership of the generic search relation stays in
-- the new kernel.
incompleteToCompleteNegativeRefinement : Refinement.DecisionRefines zer neg
incompleteToCompleteNegativeRefinement = Refinement.unresolvedBecomesNegative

unresolvedToPositiveProofSearchRefinement : Refinement.DecisionRefines zer pos
unresolvedToPositiveProofSearchRefinement = Refinement.unresolvedBecomesPositive

kernelIncompleteToCompleteNegative : Search.SearchDecisionRefines zer neg
kernelIncompleteToCompleteNegative = Search.unresolvedBecomesNegative

kernelUnresolvedToPositive : Search.SearchDecisionRefines zer pos
kernelUnresolvedToPositive = Search.unresolvedBecomesPositive

------------------------------------------------------------------------
-- Search status is a product coordinate beside proof-debt routing.
------------------------------------------------------------------------

record ProofSearchProvenance : Set where
  constructor proofSearchProvenance
  field
    debtRoute : Debt.ProofDebtRoutingReceipt
    routeAdmission : ProofSearch.RouteAdmission

open ProofSearchProvenance public

ProofSearchDecisionPacket : Set₁
ProofSearchDecisionPacket =
  Search.SearchDecisionPacket ProofSearch.SearchState ProofSearchProvenance

canonicalDeferredUnresolvedPacket : ProofSearchDecisionPacket
canonicalDeferredUnresolvedPacket =
  Search.searchDecisionPacket
    ProofSearch.authoritativeFrontierReduced
    (Search.openFiniteScope nonClosingCandidateOnly)
    zer
    refl
    (proofSearchProvenance
      Debt.canonicalEstablishedDeferredRoute
      ProofSearch.canonicalRouteAdmission)

canonicalDeferredPositiveSearchPacket : ProofSearchDecisionPacket
canonicalDeferredPositiveSearchPacket =
  Search.searchDecisionPacket
    ProofSearch.authoritativeFrontierReduced
    (Search.completeFiniteScope canonicalCompleteDomain)
    pos
    refl
    (proofSearchProvenance
      Debt.canonicalEstablishedDeferredRoute
      ProofSearch.canonicalRouteAdmission)

canonicalDeferredNegativeFiniteSearchPacket : ProofSearchDecisionPacket
canonicalDeferredNegativeFiniteSearchPacket =
  Search.searchDecisionPacket
    ProofSearch.authoritativeFrontierReduced
    (Search.completeFiniteScope nonClosingCompleteDomain)
    neg
    refl
    (proofSearchProvenance
      Debt.canonicalEstablishedDeferredRoute
      ProofSearch.canonicalRouteAdmission)

packetDebtRoute : ProofSearchDecisionPacket → Debt.ProofDebtRoutingReceipt
packetDebtRoute packet = debtRoute (Search.provenance packet)

unresolvedPacketRemainsCertificationDebt :
  Debt.routedDebt (packetDebtRoute canonicalDeferredUnresolvedPacket)
  ≡ Debt.certificationDebt
unresolvedPacketRemainsCertificationDebt = refl

positiveSearchPacketRemainsCertificationDebt :
  Debt.routedDebt (packetDebtRoute canonicalDeferredPositiveSearchPacket)
  ≡ Debt.certificationDebt
positiveSearchPacketRemainsCertificationDebt = refl

negativeFiniteSearchPacketRemainsCertificationDebt :
  Debt.routedDebt (packetDebtRoute canonicalDeferredNegativeFiniteSearchPacket)
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
    genericSearchKernelReused : Bool
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
    true true true true true true true true false false
