module DASHI.Core.ConsumerRelativeMinimalFidelityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as FutureBridge

------------------------------------------------------------------------
-- MINIMAL SUFFICIENT FIDELITY FOR A DECLARED CONSUMER
--
-- A selected model is not minimal because it is simple, low-rank or cheap in
-- the abstract.  It is minimal only relative to a declared portfolio/search
-- order when it is certified and every declared strictly cheaper candidate has
-- a consumer-specific future counterexample.
------------------------------------------------------------------------

record MinimalCertifiedCandidate
    {Fine Action Observation : Set}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    (selected : Search.ReductionCandidate
      Fine Action Observation fineStep observe) : Set₁ where
  constructor minimalCertifiedCandidate
  field
    Declared :
      Search.ReductionCandidate Fine Action Observation fineStep observe → Set
    selectedDeclared : Declared selected
    selectedCertificate : Search.CandidateCertification selected

    cheaperDeclaredRefuted :
      (candidate : Search.ReductionCandidate
        Fine Action Observation fineStep observe) →
      Declared candidate →
      suc (Search.costRank candidate) ≤ Search.costRank selected →
      Search.CandidateRefutation candidate

    portfolioReference : String
    searchOrderReference : String
    consumerReference : String

open MinimalCertifiedCandidate public

minimalSelectedIsCanonicalFutureSafe :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {selected : Search.ReductionCandidate
      Fine Action Observation fineStep observe} →
  MinimalCertifiedCandidate selected →
  (actionLabel : Action → String) →
  Future.FutureLanguageSafeProjection
    (FutureBridge.deterministicSystem fineStep actionLabel)
    observe
    (Search.project selected)
minimalSelectedIsCanonicalFutureSafe minimal actionLabel =
  Search.certifiedCandidateCanonicalFutureSafe
    (selectedCertificate minimal)
    actionLabel

cheaperDeclaredCandidateHasCounterexample :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {selected : Search.ReductionCandidate
      Fine Action Observation fineStep observe}
    (minimal : MinimalCertifiedCandidate selected)
    (candidate : Search.ReductionCandidate
      Fine Action Observation fineStep observe) →
  Declared minimal candidate →
  suc (Search.costRank candidate) ≤ Search.costRank selected →
  Search.CandidateRefutation candidate
cheaperDeclaredCandidateHasCounterexample minimal =
  cheaperDeclaredRefuted minimal

record MinimalFidelityBoundary : Set where
  constructor minimalFidelityBoundary
  field
    minimalityIsConsumerAndPortfolioRelative : Bool
    minimalityRequiresSelectedCertification : Bool
    minimalityRequiresCheaperDeclaredCounterexamples : Bool
    lowestCostCandidateAutomaticallySufficient : Bool
    lowestCostCandidateAutomaticallySufficientIsFalse :
      lowestCostCandidateAutomaticallySufficient ≡ false
    highestFidelityAutomaticallySelected : Bool
    highestFidelityAutomaticallySelectedIsFalse :
      highestFidelityAutomaticallySelected ≡ false

canonicalMinimalFidelityBoundary : MinimalFidelityBoundary
canonicalMinimalFidelityBoundary =
  minimalFidelityBoundary true true true false refl false refl
