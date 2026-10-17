module DASHI.Culture.PowersPlantationParadiseFrontierGenealogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.PowersPlantationParadiseMinetteMicrohistoryExact as Minette
import DASHI.Culture.PowersPlantationParadiseEnslavedDistributionEvidenceExact as Enslaved

------------------------------------------------------------------------
-- POWERS EMPIRICAL FRONTIER GENEALOGY
--
-- Domain-specific adapter inspired by current repo-history/frontier tooling.
-- Development history may explain why a residual changed. It is advisory and
-- cannot become historical evidence, theorem truth or source authority.
------------------------------------------------------------------------

data FrontierStatus : Set where
  openResidual : FrontierStatus
  partiallyPaidResidual : FrontierStatus
  narrowedResidual : FrontierStatus
  closedResidual : FrontierStatus
  gatedResidual : FrontierStatus

data FrontierTransitionKind : Set where
  newEvidenceNarrowedResidual : FrontierTransitionKind
  discriminatorRefinedQuestion : FrontierTransitionKind
  sourceConflictReopenedResidual : FrontierTransitionKind
  prerequisiteGateRetained : FrontierTransitionKind

record FrontierGenealogyReceipt : Set where
  constructor frontier-genealogy-receipt
  field
    frontierId : String
    earlierStatus : FrontierStatus
    laterStatus : FrontierStatus
    transitionKind : FrontierTransitionKind
    evidenceOrReasonReference : String
    earlierFrontierReference : String
    laterFrontierReference : String
    deletesEarlierSourceReceipt : Bool
    deletesEarlierSourceReceiptIsFalse : deletesEarlierSourceReceipt ≡ false
    createsHistoricalTruth : Bool
    createsHistoricalTruthIsFalse : createsHistoricalTruth ≡ false
    createsSourceAuthority : Bool
    createsSourceAuthorityIsFalse : createsSourceAuthority ≡ false

open FrontierGenealogyReceipt public

compensationFrontierGenealogy : FrontierGenealogyReceipt
compensationFrontierGenealogy =
  frontier-genealogy-receipt
    "powers:minette-compensation"
    openResidual
    narrowedResidual
    newEvidenceNarrowedResidual
    "Prest 2019 / Saint-Martin testament pays three-year 8000-livres/year contract plus documented nonpayment; actual executor/estate settlement remains open"
    "earlier frontier: compensation mechanism/payment unresolved"
    "current residual: actual estate/executor transfer and benefit-night realised proceeds"
    false refl
    false refl
    false refl

distributionFrontierGenealogy : FrontierGenealogyReceipt
distributionFrontierGenealogy =
  frontier-genealogy-receipt
    "powers:actor-distribution"
    openResidual
    partiallyPaidResidual
    newEvidenceNarrowedResidual
    "Prest 2023 pays category-level enslaved participation; Julien 1781 pays same-record theatre contribution × coercive sale status"
    "earlier frontier: distributional incidence lacked same-object evidence"
    "current residual: actor × venue × time benefit, voice and finer status/payment joins"
    false refl
    false refl
    false refl

chronologyFrontierGenealogy : FrontierGenealogyReceipt
chronologyFrontierGenealogy =
  frontier-genealogy-receipt
    "powers:minette-july-1790-chronology"
    partiallyPaidResidual
    narrowedResidual
    sourceConflictReopenedResidual
    "Prest 1 July and Laméca 17 July coordinates are retained as same-incident competing accounts; primary Affiches manifestation is the discriminator"
    "secondary chronology appeared singular before the disagreement was retained"
    "current residual: direct primary issue/page/image inspection; no winning secondary date selected"
    false refl
    false refl
    false refl

causalFrontierGenealogy : FrontierGenealogyReceipt
causalFrontierGenealogy =
  frontier-genealogy-receipt
    "powers:causal-mobility"
    gatedResidual
    gatedResidual
    prerequisiteGateRetained
    "Minette/Lise descriptive comparison and mobility coordinates enrich the observational panel but do not yet pay an admissible causal-identification design"
    "causal identification gated pending comparable fibres"
    "causal identification remains gated pending comparable longitudinal fibres and an explicit identification family"
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing same-object owners remain the evidence authorities behind the
-- genealogy; the genealogy itself only records the change in research state.
------------------------------------------------------------------------

minetteSalaryEvidenceAnchor : Minette.MinetteSalaryNonpaymentReceipt
minetteSalaryEvidenceAnchor = Minette.minette1784SalaryNonpaymentReceipt

julienDistributionEvidenceAnchor : Enslaved.EnslavedMusicianContributionBurdenReceipt
julienDistributionEvidenceAnchor = Enslaved.julien1781ContributionBurdenReceipt

data FrontierNarrativeCreatesHistoricalTruth : Set where

data StaleRoadmapErasesPriorEvidence : Set where

frontierNarrativeDoesNotCreateHistoricalTruth :
  FrontierNarrativeCreatesHistoricalTruth → ⊥
frontierNarrativeDoesNotCreateHistoricalTruth ()

staleRoadmapDoesNotErasePriorEvidence :
  StaleRoadmapErasesPriorEvidence → ⊥
staleRoadmapDoesNotErasePriorEvidence ()

record PowersFrontierGenealogyBoundary : Set where
  constructor powers-frontier-genealogy-boundary
  field
    frontierHistoryIsAdvisory : Bool
    frontierHistoryIsAdvisoryIsTrue : frontierHistoryIsAdvisory ≡ true
    laterEvidenceMayNarrowResidualWithoutDeletingPriorReceipts : Bool
    laterEvidenceMayNarrowResidualWithoutDeletingPriorReceiptsIsTrue :
      laterEvidenceMayNarrowResidualWithoutDeletingPriorReceipts ≡ true
    staleRoadmapLanguageCreatesHistoricalFalsehood : Bool
    staleRoadmapLanguageCreatesHistoricalFalsehoodIsFalse :
      staleRoadmapLanguageCreatesHistoricalFalsehood ≡ false
    frontierPriorityCreatesHistoricalTruth : Bool
    frontierPriorityCreatesHistoricalTruthIsFalse :
      frontierPriorityCreatesHistoricalTruth ≡ false
    boundedDevelopmentHistoryAuthorizesGlobalNegativeClaim : Bool
    boundedDevelopmentHistoryAuthorizesGlobalNegativeClaimIsFalse :
      boundedDevelopmentHistoryAuthorizesGlobalNegativeClaim ≡ false
    causalGateMayRemainAfterDescriptiveEvidenceImproves : Bool
    causalGateMayRemainAfterDescriptiveEvidenceImprovesIsTrue :
      causalGateMayRemainAfterDescriptiveEvidenceImproves ≡ true

canonicalPowersFrontierGenealogyBoundary : PowersFrontierGenealogyBoundary
canonicalPowersFrontierGenealogyBoundary =
  powers-frontier-genealogy-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
