module DASHI.Interop.PNFTechSystemicStressBridgeRegression where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Interop.PNFBraidTransportField as PNFTransport
import DASHI.Interop.PNFSpectralFieldArchitectureReceipt as PNFArchitecture
import DASHI.Promotion.PNFSpectralEmpiricalBasinValidation as Basin
import DASHI.Promotion.TechSystemicStressScenarioBoundary as Tech
import DASHI.Economics.SystemicCrisisSignalKernel as Crisis
import DASHI.Economics.SystemicCrisisCompressionBridge as Compression
import DASHI.Interop.TechSystemicStressCompressionBridge as Cross
import DASHI.Interop.PNFTechSystemicStressBridge as Bridge

------------------------------------------------------------------------
-- Canonical PNF architecture remains candidate-only.
------------------------------------------------------------------------

canonicalPNFNeedsResolverSelectorITIR :
  Bridge.pnfEvidenceReady Bridge.canonicalPNFCandidateEvidence ≡ false
canonicalPNFNeedsResolverSelectorITIR = refl

canonicalPNFCannotPromote :
  Compression.promotionLevel
    (Bridge.pnfScenarioOnlySystemicReceipt Bridge.canonicalPNFCandidateEvidence)
    ≡ Compression.unsupportedLevel
canonicalPNFCannotPromote = refl

pnfCandidateRoleHasNoDirectMechanism :
  Bridge.projectPNFRole Bridge.candidateAttributionRole
    ≡ Bridge.noDirectMarketMechanismProjection
pnfCandidateRoleHasNoDirectMechanism = refl

bothResidualLayersRemainDistinct :
  Bridge.relateResidualLayers true true
    ≡ Bridge.corroboratedButDistinctResiduals
bothResidualLayersRemainDistinct = refl

------------------------------------------------------------------------
-- Independently validated crisis/MDL fixture.
------------------------------------------------------------------------

fracturedResiduals : Compression.ResidualDepthProfile
fracturedResiduals = Compression.residualProfile pos pos pos pos pos pos

activeObservation : Crisis.CrisisObservation
activeObservation = Crisis.observation pos pos pos pos pos neg neg

activeChain : Compression.TransmissionChain
activeChain = Compression.transmission pos pos pos pos pos pos zer

closedModelReceipt : Compression.ModelSelectionReceipt
closedModelReceipt =
  Compression.modelReceipt true true true true true true true

validatedSystemicReceipt : Compression.SystemicSignalReceipt
validatedSystemicReceipt =
  Compression.systemicReceipt
    activeObservation
    fracturedResiduals
    activeChain
    closedModelReceipt
    true
    true
    true

validatedCrossReceipt : Cross.TechCrisisCompressionReceipt
validatedCrossReceipt =
  Cross.techCrisisCompressionReceipt
    Tech.canonicalTechSystemicStressMachine
    validatedSystemicReceipt
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Fully receipted PNF attachment.
------------------------------------------------------------------------

readyPNFEvidence : Bridge.PNFScenarioEvidenceReceipt
readyPNFEvidence =
  Bridge.pnfScenarioEvidenceReceipt
    PNFTransport.canonicalPNFBraidTransportFieldReceipt
    PNFArchitecture.canonicalPNFSpectralFieldArchitectureReceipt
    Tech.canonicalAIStressAttributionCandidate
    Basin.canonicalFieldWindowFeature
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true

readyPNFEvidenceCloses : Bridge.pnfEvidenceReady readyPNFEvidence ≡ true
readyPNFEvidenceCloses = refl

joinedReceipt : Bridge.PNFTechCrisisReceipt
joinedReceipt =
  Bridge.pnfTechCrisisReceipt
    readyPNFEvidence
    validatedCrossReceipt
    true
    true
    true
    true
    true

joinedGateCloses : Bridge.pnfTechCrisisGate joinedReceipt ≡ true
joinedGateCloses = refl

joinedLevelStillComesFromMechanism :
  Bridge.joinedPromotionLevel joinedReceipt
    ≡ Compression.validatedModelLevel
joinedLevelStillComesFromMechanism = refl

pnfAttachmentDoesNotUpgradeLevel :
  Bridge.joinedPromotionLevel joinedReceipt
    ≡ Cross.joinedPromotionLevel (Bridge.techCrisisReceipt joinedReceipt)
pnfAttachmentDoesNotUpgradeLevel = refl
