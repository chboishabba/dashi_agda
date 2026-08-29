module DASHI.Environment.LESAdaptiveSPACModelSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact as Canonical
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as FutureBridge
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.FiniteSPACCalibrationExperimentExact as Experiment

------------------------------------------------------------------------
-- PURPOSE
--
-- Application-facing model-search ladder for the current LES physical stack.
-- All candidates reduce the SAME fine DomainMechanismSocket and must answer the
-- SAME declared consumer observation.  The tiers are names/search intentions,
-- not automatic certifications and not claims that every site needs the most
-- detailed model.
------------------------------------------------------------------------

data SPACFidelityTier : Set where
  empiricalWaterBalance
  richardsPorousFlow
  hydraulicSPAC
  electroBiogeochemicalSPAC
  : SPACFidelityTier

record TieredSPACCandidate
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor tieredSPACCandidate
  field
    tier : SPACFidelityTier
    candidate : Search.ReductionCandidate
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)
      (Basis.evolve mechanism)
      (Basis.observe mechanism)
    physicalReductionReference : String
    retainedStateReference : String
    omittedResidualReference : String

open TieredSPACCandidate public

record SPACReductionPortfolio
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor spacReductionPortfolio
  field
    bucket : TieredSPACCandidate mechanism
    richards : TieredSPACCandidate mechanism
    spac : TieredSPACCandidate mechanism
    electroBiogeochemical : TieredSPACCandidate mechanism

    bucketTier : tier bucket ≡ empiricalWaterBalance
    richardsTier : tier richards ≡ richardsPorousFlow
    spacTier : tier spac ≡ hydraulicSPAC
    electroBiogeochemicalTier :
      tier electroBiogeochemical ≡ electroBiogeochemicalSPAC

    bucketToRichardsCostOrder :
      Search.costRank (candidate bucket)
      ≤ Search.costRank (candidate richards)
    richardsToSPACCostOrder :
      Search.costRank (candidate richards)
      ≤ Search.costRank (candidate spac)
    spacToElectroBiogeochemicalCostOrder :
      Search.costRank (candidate spac)
      ≤ Search.costRank (candidate electroBiogeochemical)

    portfolioScopeReference : String
    commonFineStateReference : String
    commonConsumerReference : String

open SPACReductionPortfolio public

------------------------------------------------------------------------
-- Counterexample-driven escalation edges.  These consume exact future
-- separation witnesses; a missing certification is not itself a refutation.
------------------------------------------------------------------------

bucketToRichardsEscalation :
  ∀ {mechanism}
    (portfolio : SPACReductionPortfolio mechanism) →
  Search.CandidateRefutation (candidate (bucket portfolio)) →
  Search.ReductionEscalationEdge
    (candidate (bucket portfolio))
    (candidate (richards portfolio))
bucketToRichardsEscalation portfolio failure =
  Search.reductionEscalationEdge
    failure
    (bucketToRichardsCostOrder portfolio)
    "retain bucket future-separating counterexample"
    "bucket consumer collision requires richer state"

richardsToSPACEscalation :
  ∀ {mechanism}
    (portfolio : SPACReductionPortfolio mechanism) →
  Search.CandidateRefutation (candidate (richards portfolio)) →
  Search.ReductionEscalationEdge
    (candidate (richards portfolio))
    (candidate (spac portfolio))
richardsToSPACEscalation portfolio failure =
  Search.reductionEscalationEdge
    failure
    (richardsToSPACCostOrder portfolio)
    "retain Richards future-separating counterexample"
    "soil-only dynamics erase a declared plant/atmosphere consumer distinction"

spacToElectroBiogeochemicalEscalation :
  ∀ {mechanism}
    (portfolio : SPACReductionPortfolio mechanism) →
  Search.CandidateRefutation (candidate (spac portfolio)) →
  Search.ReductionEscalationEdge
    (candidate (spac portfolio))
    (candidate (electroBiogeochemical portfolio))
spacToElectroBiogeochemicalEscalation portfolio failure =
  Search.reductionEscalationEdge
    failure
    (spacToElectroBiogeochemicalCostOrder portfolio)
    "retain hydraulic-SPAC future-separating counterexample"
    "declared nutrient/electrochemical/biogeochemical consumer needs retained residual"

------------------------------------------------------------------------
-- A staged selection receipt: one cheaper candidate is genuinely falsified for
-- the declared consumer while the next candidate is exactly certified.
------------------------------------------------------------------------

record EscalatedCertifiedModel
    {mechanism : Basis.DomainMechanismSocket}
    (from to : TieredSPACCandidate mechanism) : Set₁ where
  constructor escalatedCertifiedModel
  field
    failedCheaper : Search.CandidateRefutation (candidate from)
    certifiedRicher : Search.CandidateCertification (candidate to)
    escalationReference : String
    calibrationReference : String
    heldOutValidationReference : String

open EscalatedCertifiedModel public

richerCertificationIsCanonicalFutureSafe :
  ∀ {mechanism}
    {from to : TieredSPACCandidate mechanism} →
  (receipt : EscalatedCertifiedModel from to) →
  (controlLabel : Basis.Control mechanism → String) →
  Future.FutureLanguageSafeProjection
    (FutureBridge.deterministicSystem
      (Basis.evolve mechanism) controlLabel)
    (Basis.observe mechanism)
    (Search.project (candidate to))
richerCertificationIsCanonicalFutureSafe receipt controlLabel =
  Search.certifiedCandidateCanonicalFutureSafe
    (certifiedRicher receipt)
    controlLabel

cheaperCounterexampleCannotBePromotedToSafeROM :
  ∀ {mechanism}
    {from to : TieredSPACCandidate mechanism} →
  (receipt : EscalatedCertifiedModel from to) →
  (controlLabel : Basis.Control mechanism → String) →
  Future.FutureLanguageSafeProjection
    (FutureBridge.deterministicSystem
      (Basis.evolve mechanism) controlLabel)
    (Basis.observe mechanism)
    (Search.project (candidate from)) →
  ⊥
cheaperCounterexampleCannotBePromotedToSafeROM receipt controlLabel safe =
  Canonical.candidateFailureContradictsCanonicalFutureSafety
    controlLabel
    (failedCheaper receipt)
    safe

------------------------------------------------------------------------
-- The finite calibration design and the model-search portfolio are separate.
-- An experiment supplies observations/parameters; it does not by itself certify
-- any candidate reduction.
------------------------------------------------------------------------

record FiniteSPACModelSearchCampaign
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor finiteSPACModelSearchCampaign
  field
    experiment : Experiment.FiniteSPACCalibrationExperiment
    portfolio : SPACReductionPortfolio mechanism
    candidateCalibrationPlanReference : String
    counterexampleSearchReference : String
    consumerDeclarationReference : String
    activeMeasurementPlanReference : String
    finalModelSelectionReference : String

open FiniteSPACModelSearchCampaign public

record LESAdaptiveSPACModelSearchBoundary : Set where
  constructor lesAdaptiveSPACModelSearchBoundary
  field
    cheapModelIsPreferredWithoutConsumerCertificate : Bool
    cheapModelIsPreferredWithoutConsumerCertificateIsFalse :
      cheapModelIsPreferredWithoutConsumerCertificate ≡ false
    expensiveModelIsScientificallyTruerByCostRank : Bool
    expensiveModelIsScientificallyTruerByCostRankIsFalse :
      expensiveModelIsScientificallyTruerByCostRank ≡ false
    oneCounterexampleCanRefuteConsumerSafetyForCandidate : Bool
    oneCounterexampleCanRefuteConsumerSafetyForCandidateIsTrue :
      oneCounterexampleCanRefuteConsumerSafetyForCandidate ≡ true
    experimentDesignAloneCertifiesReduction : Bool
    experimentDesignAloneCertifiesReductionIsFalse :
      experimentDesignAloneCertifiesReduction ≡ false
    sameFineStateAcrossTiersRequired : Bool
    sameFineStateAcrossTiersRequiredIsTrue : sameFineStateAcrossTiersRequired ≡ true

canonicalLESAdaptiveSPACModelSearchBoundary :
  LESAdaptiveSPACModelSearchBoundary
canonicalLESAdaptiveSPACModelSearchBoundary =
  lesAdaptiveSPACModelSearchBoundary
    false refl false refl true refl false refl true refl
