module DASHI.Biology.BH4FluxCandidateRankingExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Ranking boundary for Phase-4 kinetic evidence.
--
-- The executable ranking layer orders SABIO candidates by how directly their
-- parameter type could inform a reaction-flux bound:
--   direct-rate-candidate      : Vmax / measured-rate-like
--   capacity-candidate         : kcat / turnover-like, requiring enzyme amount
--   kinetic-shape-candidate    : Km/Ki/Kd-like
--   assay-context-only         : concentrations/conditions
--   not-flux-informative       : unclassified at this layer
--
-- Ranking is triage, not payment.  Four independent gates remain mandatory:
-- same-assay reaction identity; same-object/compartment/time translation;
-- normalized solver flux unit; kinetic-to-network-flux justification.
------------------------------------------------------------------------

data FluxRelevanceClass : Set where
  directRateCandidate : FluxRelevanceClass
  capacityCandidate : FluxRelevanceClass
  kineticShapeCandidate : FluxRelevanceClass
  assayContextOnly : FluxRelevanceClass
  notFluxInformative : FluxRelevanceClass

record FluxCandidatePaymentGates : Set where
  constructor flux-candidate-payment-gates
  field
    assayReactionIdentityPaid : Bool
    sameObjectCompartmentTimePaid : Bool
    normalizedSolverFluxUnitPaid : Bool
    kineticToFluxTranslationPaid : Bool

open FluxCandidatePaymentGates public

canonicalUnpaidFluxCandidateGates : FluxCandidatePaymentGates
canonicalUnpaidFluxCandidateGates = flux-candidate-payment-gates false false false false

record BH4FluxCandidateRankingBoundary : Set where
  constructor bh4-flux-candidate-ranking-boundary
  field
    rankCreatesFluxBound : Bool
    rankCreatesFluxBoundIsFalse : rankCreatesFluxBound ≡ false
    rateLikeClassCreatesFluxBound : Bool
    rateLikeClassCreatesFluxBoundIsFalse : rateLikeClassCreatesFluxBound ≡ false
    catalyticConstantCreatesFluxWithoutEnzymeAbundance : Bool
    catalyticConstantCreatesFluxWithoutEnzymeAbundanceIsFalse :
      catalyticConstantCreatesFluxWithoutEnzymeAbundance ≡ false
    affinityConstantCreatesFluxBound : Bool
    affinityConstantCreatesFluxBoundIsFalse : affinityConstantCreatesFluxBound ≡ false
    assayContextMayBeDropped : Bool
    assayContextMayBeDroppedIsFalse : assayContextMayBeDropped ≡ false
    missingPaymentGateDefaultsTrue : Bool
    missingPaymentGateDefaultsTrueIsFalse : missingPaymentGateDefaultsTrue ≡ false

open BH4FluxCandidateRankingBoundary public

canonicalBH4FluxCandidateRankingBoundary : BH4FluxCandidateRankingBoundary
canonicalBH4FluxCandidateRankingBoundary =
  bh4-flux-candidate-ranking-boundary
    false refl false refl false refl false refl false refl false refl

canonicalBH4FluxCandidateRankingReceipt : Receipt.GenericReceipt
canonicalBH4FluxCandidateRankingReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 kinetic candidate flux-relevance ranking"
    "DASHI.Biology.BH4FluxCandidateRankingExact"
    "schema-v2 SABIO candidates -> per-Rhea flux-relevance ranking -> explicit four-gate payable/blocked ledger"
    "prioritizes direct rate and catalytic-capacity evidence for manual/source adjudication without turning parameter type, rank or database coverage into a quantitative solver bound"
    "rank is not payment; kcat needs enzyme abundance/state; Km/Ki/Kd are kinetic-shape evidence; assay context cannot be dropped; absent payment coordinates default false"
    "python3 scripts/rank_bh4_flux_candidates.py"
