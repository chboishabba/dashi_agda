module DASHI.Interop.PNFTechSystemicStressBridge where

open import DASHI.Core.Prelude

import DASHI.Interop.PNFBraidTransportField as PNFTransport
import DASHI.Interop.PNFSpectralFieldArchitectureReceipt as PNFArchitecture
import DASHI.Promotion.PNFSpectralEmpiricalBasinValidation as Basin
import DASHI.Promotion.TechSystemicStressScenarioBoundary as Tech
import DASHI.Economics.SystemicCrisisCompressionBridge as Compression
import DASHI.Interop.TechSystemicStressCompressionBridge as Cross

------------------------------------------------------------------------
-- PNF / tech-systemic-stress cross-pollination.
--
-- PNF contributes a receipted evidence-navigation layer:
--
--   source event -> revision slice -> braid crossings -> candidate refs
--   -> spectral/reference neighbourhood -> resolver/selector/ITIR validation.
--
-- The crisis stack contributes a distinct mechanism layer:
--
--   market observations -> compression regime -> transmission chain
--   -> MDL/holdout gate -> promotion level.
--
-- These layers are deliberately not identified.  A PNF braid may organise,
-- revise, contradict, terminate, and rank evidence.  It cannot manufacture a
-- funding observation, forced seller, Treasury dysfunction, sovereign link,
-- causal attribution, or profitable trading signal.
------------------------------------------------------------------------

infixr 6 _and_

_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

------------------------------------------------------------------------
-- What PNF can contribute to the scenario layer.
------------------------------------------------------------------------

data PNFEvidenceRole : Set where
  sourceEventRole : PNFEvidenceRole
  temporalRevisionRole : PNFEvidenceRole
  contradictionRole : PNFEvidenceRole
  supportStrengtheningRole : PNFEvidenceRole
  supportWeakeningRole : PNFEvidenceRole
  residualTerminationRole : PNFEvidenceRole
  historicalNeighbourhoodRole : PNFEvidenceRole
  candidateAttributionRole : PNFEvidenceRole

data PNFStressProjection : Set where
  narrativeRevisionProjection : PNFStressProjection
  evidenceConflictProjection : PNFStressProjection
  supportDriftProjection : PNFStressProjection
  unresolvedEvidenceProjection : PNFStressProjection
  historicalAnalogueProjection : PNFStressProjection
  noDirectMarketMechanismProjection : PNFStressProjection

projectPNFRole : PNFEvidenceRole → PNFStressProjection
projectPNFRole sourceEventRole = historicalAnalogueProjection
projectPNFRole temporalRevisionRole = narrativeRevisionProjection
projectPNFRole contradictionRole = evidenceConflictProjection
projectPNFRole supportStrengtheningRole = supportDriftProjection
projectPNFRole supportWeakeningRole = supportDriftProjection
projectPNFRole residualTerminationRole = unresolvedEvidenceProjection
projectPNFRole historicalNeighbourhoodRole = historicalAnalogueProjection
projectPNFRole candidateAttributionRole = noDirectMarketMechanismProjection

pnfProjectionDoesNotSupplyFundingStress :
  projectPNFRole candidateAttributionRole ≡ noDirectMarketMechanismProjection
pnfProjectionDoesNotSupplyFundingStress = refl

------------------------------------------------------------------------
-- PNF evidence receipt for one BAD-window/scenario candidate.
--
-- The architecture and braid receipts preserve source, time-slice, revision,
-- crossing, residual, and candidate-ref structure.  The remaining booleans are
-- runtime obligations which the canonical architecture does not discharge.
------------------------------------------------------------------------

record PNFScenarioEvidenceReceipt : Set where
  constructor pnfScenarioEvidenceReceipt
  field
    transportArchitecture : PNFTransport.PNFBraidTransportFieldReceipt
    spectralArchitecture : PNFArchitecture.PNFSpectralFieldArchitectureReceipt
    scenarioCandidate : Tech.ScenarioAttributionCandidate
    empiricalWindow : Basin.FieldWindowFeature

    sourceEventBound : Bool
    revisionLineageBound : Bool
    braidSignatureBound : Bool
    resolverReceiptSupplied : Bool
    selectorReceiptSupplied : Bool
    itirReceiptSupplied : Bool
    eventAndMarketClocksAligned : Bool
    noLookaheadLeakage : Bool
    completeSourceSideInformationCounted : Bool

    pnfTransportTreatedAsNavigationOnly : Bool
    pnfResidualNotIdentifiedWithEconomicResidual : Bool
    vectorSimilarityNotTreatedAsSemanticTruth : Bool
    historicalAnalogueNotTreatedAsCausalAttribution : Bool
    newsAlignmentNotTreatedAsPrediction : Bool

open PNFScenarioEvidenceReceipt public

pnfEvidenceReady : PNFScenarioEvidenceReceipt → Bool
pnfEvidenceReady r =
  sourceEventBound r
  and revisionLineageBound r
  and braidSignatureBound r
  and resolverReceiptSupplied r
  and selectorReceiptSupplied r
  and itirReceiptSupplied r
  and eventAndMarketClocksAligned r
  and noLookaheadLeakage r
  and completeSourceSideInformationCounted r
  and pnfTransportTreatedAsNavigationOnly r
  and pnfResidualNotIdentifiedWithEconomicResidual r
  and vectorSimilarityNotTreatedAsSemanticTruth r
  and historicalAnalogueNotTreatedAsCausalAttribution r
  and newsAlignmentNotTreatedAsPrediction r

canonicalPNFCandidateEvidence : PNFScenarioEvidenceReceipt
canonicalPNFCandidateEvidence =
  pnfScenarioEvidenceReceipt
    PNFTransport.canonicalPNFBraidTransportFieldReceipt
    PNFArchitecture.canonicalPNFSpectralFieldArchitectureReceipt
    Tech.canonicalAIStressAttributionCandidate
    Basin.canonicalFieldWindowFeature
    true
    true
    true
    false
    false
    false
    false
    true
    false
    true
    true
    true
    true
    true

canonicalPNFCandidateEvidenceIsNotCommitReady :
  pnfEvidenceReady canonicalPNFCandidateEvidence ≡ false
canonicalPNFCandidateEvidenceIsNotCommitReady = refl

------------------------------------------------------------------------
-- PNF-only evidence cannot promote a plumbing mechanism.
------------------------------------------------------------------------

pnfScenarioOnlySystemicReceipt :
  PNFScenarioEvidenceReceipt → Compression.SystemicSignalReceipt
pnfScenarioOnlySystemicReceipt r =
  Cross.scenarioOnlySystemicReceipt (scenarioCandidate r)

pnfOnlyCannotPromoteMechanism :
  (r : PNFScenarioEvidenceReceipt) →
  Compression.promotionLevel (pnfScenarioOnlySystemicReceipt r)
    ≡ Compression.unsupportedLevel
pnfOnlyCannotPromoteMechanism r = refl

canonicalPNFAIAttributionCannotPromoteMechanism :
  Compression.promotionLevel
    (pnfScenarioOnlySystemicReceipt canonicalPNFCandidateEvidence)
    ≡ Compression.unsupportedLevel
canonicalPNFAIAttributionCannotPromoteMechanism = refl

------------------------------------------------------------------------
-- Distinguish the two residual meanings.
--
-- PNF residuals concern typed meet/join, support, contradiction, and transport
-- termination between evidence fibres.  Economic residuals concern failure of
-- the selected quotient/model to compress observed market structure.  A bridge
-- may compare them, but neither is definitionally the other.
------------------------------------------------------------------------

data ResidualLayerRelation : Set where
  evidenceResidualOnly : ResidualLayerRelation
  economicResidualOnly : ResidualLayerRelation
  corroboratedButDistinctResiduals : ResidualLayerRelation
  residualRelationUnresolved : ResidualLayerRelation

relateResidualLayers : Bool → Bool → ResidualLayerRelation
relateResidualLayers true true = corroboratedButDistinctResiduals
relateResidualLayers true false = evidenceResidualOnly
relateResidualLayers false true = economicResidualOnly
relateResidualLayers false false = residualRelationUnresolved

bothResidualsRemainDistinct :
  relateResidualLayers true true ≡ corroboratedButDistinctResiduals
bothResidualsRemainDistinct = refl

------------------------------------------------------------------------
-- Joined PNF + scenario + crisis/MDL receipt.
--
-- PNF supplies source governance and candidate attribution.  The existing
-- cross-layer receipt independently supplies market mechanism and MDL status.
------------------------------------------------------------------------

record PNFTechCrisisReceipt : Set where
  constructor pnfTechCrisisReceipt
  field
    pnfEvidence : PNFScenarioEvidenceReceipt
    techCrisisReceipt : Cross.TechCrisisCompressionReceipt
    pnfWindowMatchesScenarioWindow : Bool
    pnfAttributionIndependentOfForwardOutcome : Bool
    pnfDoesNotReplaceMarketObservations : Bool
    pnfDoesNotReplaceTransmissionChain : Bool
    pnfDoesNotReplaceMDLValidation : Bool

open PNFTechCrisisReceipt public

pnfTechCrisisGate : PNFTechCrisisReceipt → Bool
pnfTechCrisisGate r =
  pnfEvidenceReady (pnfEvidence r)
  and pnfWindowMatchesScenarioWindow r
  and pnfAttributionIndependentOfForwardOutcome r
  and pnfDoesNotReplaceMarketObservations r
  and pnfDoesNotReplaceTransmissionChain r
  and pnfDoesNotReplaceMDLValidation r
  and Cross.validatedCrossLayerGate (techCrisisReceipt r)

joinedPromotionLevel :
  PNFTechCrisisReceipt → Compression.PromotionLevel
joinedPromotionLevel r =
  Cross.joinedPromotionLevel (techCrisisReceipt r)

-- PNF attachment never upgrades the mechanism level by itself; the level is
-- projected entirely from the independently constructed crisis/MDL receipt.
pnfAttachmentDoesNotChangePromotion :
  (r : PNFTechCrisisReceipt) →
  joinedPromotionLevel r
    ≡ Cross.joinedPromotionLevel (techCrisisReceipt r)
pnfAttachmentDoesNotChangePromotion r = refl

------------------------------------------------------------------------
-- Recommended empirical interpretation.
------------------------------------------------------------------------

data PNFSystemicUse : Set where
  organiseBADWindowEvidence : PNFSystemicUse
  preserveNewsRevisionHistory : PNFSystemicUse
  exposeContradictionAndSupportDrift : PNFSystemicUse
  rankHistoricalAnalogueCandidates : PNFSystemicUse
  bindAttributionToReceipts : PNFSystemicUse
  blockUnreceiptedNarrativePromotion : PNFSystemicUse

pnfTechSystemicStressBridgeSummary : String
pnfTechSystemicStressBridgeSummary =
  "PNF organises source events, revisions, braid crossings, residual terminations, and historical analogue candidates around BAD windows; resolver, selector, ITIR, time alignment, side-information, independent market plumbing, transmission, and MDL receipts remain mandatory, and PNF attachment cannot itself promote a systemic mechanism."