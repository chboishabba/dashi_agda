module DASHI.Governance.OriginalThreadParetoMaxCut20261008Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.OriginalThreadParetoAcquisitionExact as Previous
import DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact as Hansard
import DASHI.Governance.IRISDenaSameObjectAcquisitionMaxCutExact as IRIS
import DASHI.Governance.AUKUSOnboardConductSovereigntyBoundaryExact as Sovereignty
import DASHI.Governance.AUKUSEmbeddedAuthorityCommandNoncollapseExact as Authority
import DASHI.Governance.IRISDenaMinisterialBriefingFOIBoundaryExact as Briefing
import DASHI.Governance.IranThreatRepressionCaseNarrowingExact as Iran

------------------------------------------------------------------------
-- 2026-10-08 ORIGINAL-THREAD PARETO RECOMPUTATION
--
-- Prior paid cells remain paid in Previous. This owner recomputes only the
-- residual programme after discovering:
--   * transcript ref. 29619 is published in full;
--   * later Chief of Navy correction documents exist;
--   * the correct primary hearing object is correction-aware;
--   * leaked secondary reproductions narrow the 2024 embedded-authority
--     directive while leaving the directive/MOU primary documents unacquired;
--   * statutory coverage, direction authority, formal command, national-policy
--     constraint and actual duty are separate sovereignty coordinates.
------------------------------------------------------------------------

data LiveRequirement : Set where
  irisCorrectionAwareHansardContent : LiveRequirement
  irisEmbeddingProtocolText : LiveRequirement
  irisExactOperationalRecord : LiveRequirement
  iranMarginalRepressionIncrement : LiveRequirement
  broadHistoricalExpansion : LiveRequirement

hansardContentCell : Pareto.RequirementCandidate LiveRequirement
hansardContentCell = Pareto.requirement-candidate
  irisCorrectionAwareHansardContent
  true true true true
  1 5
  "Read FADT transcript ref. 29619 pp. 49-52 together with any applicable Chief of Navy correction; promote/correct the defensive/platform-maintenance duty class only from that primary bundle."

embeddingProtocolCell : Pareto.RequirementCandidate LiveRequirement
embeddingProtocolCell = Pareto.requirement-candidate
  irisEmbeddingProtocolText
  true true true true
  2 6
  "Acquire the complete December 2024 Chief of Navy directive and September 2023 exchange-personnel MOU/operative annexes. Secondary reporting already attributes mandatory lawful/reasonable USN direction authority plus an explicit no-command clause, so the fibre is narrower but primary-document authority remains unpaid."

exactOperationalCell : Pareto.RequirementCandidate LiveRequirement
exactOperationalCell = Pareto.requirement-candidate
  irisExactOperationalRecord
  true true true true
  5 8
  "Acquire watchbill/duty assignment, action log, debrief or equivalent same-episode record identifying what the three Australians actually did during the IRIS Dena engagement."

iranMarginalCell : Pareto.RequirementCandidate LiveRequirement
iranMarginalCell = Pareto.requirement-candidate
  iranMarginalRepressionIncrement
  true true true true
  5 5
  "Still required: identify the marginal 2026 Iranian repression increment attributable to external threat; qualitative wartime routing is already paid."

broadExpansionCell : Pareto.RequirementCandidate LiveRequirement
broadExpansionCell = Pareto.requirement-candidate
  broadHistoricalExpansion
  false true true false
  5 2
  "More countries/actors/theories are deferred until the live same-object IRIS acquisition cells are paid or shown acquisition-blocked."

livePortfolio : List (Pareto.RequirementCandidate LiveRequirement)
livePortfolio =
  hansardContentCell
  ∷ embeddingProtocolCell
  ∷ exactOperationalCell
  ∷ iranMarginalCell
  ∷ broadExpansionCell
  ∷ []

hansardContentOnFrontier :
  Pareto.onParetoFrontier? livePortfolio hansardContentCell ≡ true
hansardContentOnFrontier = refl

embeddingProtocolOnFrontier :
  Pareto.onParetoFrontier? livePortfolio embeddingProtocolCell ≡ true
embeddingProtocolOnFrontier = refl

exactOperationalOnFrontier :
  Pareto.onParetoFrontier? livePortfolio exactOperationalCell ≡ true
exactOperationalOnFrontier = refl

iranMarginalCurrentlyDominated :
  Pareto.onParetoFrontier? livePortfolio iranMarginalCell ≡ false
iranMarginalCurrentlyDominated = refl

broadExpansionDeferred :
  Pareto.eligible? broadExpansionCell ≡ false
broadExpansionDeferred = refl

frontierExactlyIRISThreeStage :
  Pareto.paretoFrontier livePortfolio ≡
    hansardContentCell ∷ embeddingProtocolCell ∷ exactOperationalCell ∷ []
frontierExactlyIRISThreeStage = refl

------------------------------------------------------------------------
-- Source/authority payloads remain separate from routing scores.
------------------------------------------------------------------------

correctionAwarePrimaryBundle : Hansard.CorrectionAwarePrimaryBundle
correctionAwarePrimaryBundle = Hansard.canonicalPrimaryBundle

irisMinCut : IRIS.RemainingMinCut
irisMinCut = IRIS.currentMinCut

sovereigntyBoundary : Sovereignty.AUKUSCommandSovereigntyBoundary
sovereigntyBoundary = Sovereignty.canonicalBoundary

embeddedAuthorityBoundary : Authority.DirectionCommandBoundary
embeddedAuthorityBoundary = Authority.canonicalBoundary

embeddedDirectiveResidual : Authority.PrimaryDocumentResidual
embeddedDirectiveResidual = Authority.directiveResidual

ministerialBriefingFOIBoundary : Briefing.MinisterialBriefingFOIReceipt
ministerialBriefingFOIBoundary = Briefing.canonicalReceipt

iranResidual : Iran.SameEpisodeResidual
iranResidual = Iran.sameEpisodeResidual

previousPortfolio :
  List (Pareto.RequirementCandidate Previous.OriginalThreadRequirement)
previousPortfolio = Previous.originalThreadPortfolio
