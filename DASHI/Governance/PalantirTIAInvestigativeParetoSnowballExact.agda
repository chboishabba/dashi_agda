module DASHI.Governance.PalantirTIAInvestigativeParetoSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.PalantirTIAHistoricalGenealogyExact as Genealogy

------------------------------------------------------------------------
-- PALANTIR / TIA INVESTIGATIVE PARETO + IBRAHIM-STYLE SNOWBALL ROUTER
--
-- One source/object can pay several declared residuals, but routing priority
-- does not create evidence, truth, authority, intent, culpability or causal
-- closure.  Snowball hops must expose an explicit named next object.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Newly acquired official source anchors.
------------------------------------------------------------------------

publicLaw10887 : Source.AttributedSource
publicLaw10887 = Source.mkNoDOISource
  "United States Congress"
  "Department of Defense Appropriations Act, 2004, Public Law 108-87, section 8131"
  "United States Statutes at Large / GovInfo"
  "2003"
  "https://www.govinfo.gov/content/pkg/PLAW-108publ87/html/PLAW-108publ87.htm"
  Source.governmentSource
  "primary statutory disposition: bars TIA funding while excepting expressly funded NFIP processing, analysis and collaboration tools for counterterrorism foreign intelligence; defines TIA to include successors and individual components"
  Source.publicAttribution

senateIntelligence2003 : Source.AttributedSource
senateIntelligence2003 = Source.mkNoDOISource
  "United States Senate Select Committee on Intelligence"
  "Conference Report on H.R. 2417, Intelligence Authorization Act for Fiscal Year 2004"
  "Senate Select Committee on Intelligence"
  "2003-11-19"
  "https://www.intelligence.senate.gov/2003/11/19/publications-conference-report-hr-2417-intelligence-authorization-act-fiscal-year-2004-november-19/"
  Source.governmentSource
  "primary congressional interpretation: DARPA TIA was terminated; requested funds were expressly provided to the National Foreign Intelligence Program to develop processing, analysis and collaboration tools for counterterrorism foreign intelligence"
  Source.publicAttribution

iqtPalantirPortfolio : Source.AttributedSource
iqtPalantirPortfolio = Source.mkNoDOISource
  "In-Q-Tel"
  "Portfolio snapshot: Palantir"
  "In-Q-Tel"
  "current portfolio page accessed 2026"
  "https://www.iqt.org/portfolio?company-name=palantir"
  Source.institutionalSource
  "first-party portfolio surface confirming Palantir appears in the In-Q-Tel investment portfolio; this page alone does not pay original investment date, amount, contract scope, Alan Wade participation or TIA continuity"
  Source.publicAttribution

acquisitionSourceAtlas : Source.AttributedSourceAtlas
acquisitionSourceAtlas = Source.mkSourceAtlas
  "Palantir/TIA Pareto acquisition source atlas"
  "DASHI.Governance.PalantirTIAInvestigativeParetoSnowballExact"
  (publicLaw10887 ∷ senateIntelligence2003 ∷ iqtPalantirPortfolio ∷ [])
  "official TIA disposition; congressional interpretation; first-party In-Q-Tel portfolio identity"

data Requirement : Set where
  officialWadeTIARole : Requirement
  tiaComponentDisposition : Requirement
  earlyPalantirCIAIQTObject : Requirement
  personnelAssetTransfer : Requirement
  contractDecisionAuthorityContinuity : Requirement
  subjectBurdenContestability : Requirement
  broadKeywordSweep : Requirement

officialWadeCell : Pareto.RequirementCandidate Requirement
officialWadeCell = Pareto.requirement-candidate
  officialWadeTIARole true true true true 2 9
  "primary/official Alan Wade <-> TIA role receipt; same-person role and authority"

tiaDispositionCell : Pareto.RequirementCandidate Requirement
tiaDispositionCell = Pareto.requirement-candidate
  tiaComponentDisposition true true true true 1 8
  "Public Law 108-87 + Senate Intelligence conference report: terminated TIA, excepted NFIP processing/analysis/collaboration tools; next hop is classified-annex/programme identity"

earlyPalantirCell : Pareto.RequirementCandidate Requirement
earlyPalantirCell = Pareto.requirement-candidate
  earlyPalantirCIAIQTObject true true true true 3 10
  "exact In-Q-Tel investment/development/customer objects, dates, terms, participants and product scope"

personnelAssetTransferCell : Pareto.RequirementCandidate Requirement
personnelAssetTransferCell = Pareto.requirement-candidate
  personnelAssetTransfer true true true true 5 7
  "same-object personnel/code/asset/requirement transfer from TIA/IAO or successor programmes"

contractAuthorityCell : Pareto.RequirementCandidate Requirement
contractAuthorityCell = Pareto.requirement-candidate
  contractDecisionAuthorityContinuity true true true true 4 6
  "same-object procurement/contract-scope and institutional decision-authority continuity"

subjectBurdenCell : Pareto.RequirementCandidate Requirement
subjectBurdenCell = Pareto.requirement-candidate
  subjectBurdenContestability true true true true 4 5
  "deployment-specific subject burden, notice, contestability, oversight and remedy records"

broadSweepCell : Pareto.RequirementCandidate Requirement
broadSweepCell = Pareto.requirement-candidate
  broadKeywordSweep true true true true 8 2
  "broad Palantir/TIA/Chiliad keyword sweep without an explicit source-genealogy hop"

portfolio : List (Pareto.RequirementCandidate Requirement)
portfolio =
  officialWadeCell ∷
  tiaDispositionCell ∷
  earlyPalantirCell ∷
  personnelAssetTransferCell ∷
  contractAuthorityCell ∷
  subjectBurdenCell ∷
  broadSweepCell ∷ []

officialWadeTIARoleOnFrontier : Bool
officialWadeTIARoleOnFrontier = Pareto.onParetoFrontier? portfolio officialWadeCell

tiaDispositionOnFrontier : Bool
tiaDispositionOnFrontier = Pareto.onParetoFrontier? portfolio tiaDispositionCell

earlyPalantirCIAIQTOnFrontier : Bool
earlyPalantirCIAIQTOnFrontier = Pareto.onParetoFrontier? portfolio earlyPalantirCell

broadKeywordSweepOffFrontier : Bool
broadKeywordSweepOffFrontier = Pareto.not (Pareto.onParetoFrontier? portfolio broadSweepCell)

officialWadeTIARoleOnFrontierIsTrue : officialWadeTIARoleOnFrontier ≡ true
officialWadeTIARoleOnFrontierIsTrue = refl

tiaDispositionOnFrontierIsTrue : tiaDispositionOnFrontier ≡ true
tiaDispositionOnFrontierIsTrue = refl

earlyPalantirCIAIQTOnFrontierIsTrue : earlyPalantirCIAIQTOnFrontier ≡ true
earlyPalantirCIAIQTOnFrontierIsTrue = refl

broadKeywordSweepOffFrontierIsTrue : broadKeywordSweepOffFrontier ≡ true
broadKeywordSweepOffFrontierIsTrue = refl

------------------------------------------------------------------------
-- Explicit snowball hops.  Traversal coordinates are leads, never promotion.
------------------------------------------------------------------------

data HopClass : Set where
  namedPersonRole : HopClass
  statuteOrCongressionalRecord : HopClass
  programmeOrClassifiedAnnex : HopClass
  contractOrProcurement : HopClass
  corporateOrInvestmentRecord : HopClass
  technicalArtifact : HopClass
  oversightOrContestabilityRecord : HopClass

record SnowballHop : Set where
  constructor snowball-hop
  field
    fromObject : String
    nextObject : String
    hopClass : HopClass
    expectedPayment : String
    sourceClassNeeded : String
    mayPromoteWithoutInspection : Bool

open SnowballHop public

wadeRoleHop : SnowballHop
wadeRoleHop = snowball-hop
  "Webb/Wade candidate assertion + Wade official CIO biography"
  "official TIA/IAO participant, meeting, node-governance or inter-agency role record naming Alan Wade"
  namedPersonRole
  "same-person Wade/TIA role, scope and authority; or a falsifying/limiting role receipt"
  "official memorandum, testimony, government report, contemporaneous meeting/participant record"
  false

tiaDispositionHop : SnowballHop
tiaDispositionHop = snowball-hop
  "Public Law 108-87 section 8131 + 2003 Senate Intelligence conference report"
  "classified-annex-derived named processing/analysis/collaboration programme or declassified successor/component record"
  programmeOrClassifiedAnnex
  "component identity, custodian, funding, scope and transfer/continuation status"
  "declassified annex, appropriations/programme record, inspector-general/GAO/congressional or agency record"
  false

earlyPalantirHop : SnowballHop
earlyPalantirHop = snowball-hop
  "Wired Poindexter/Karp/Thiel + In-Q-Tel/CIA development history + current first-party IQT portfolio identity"
  "contemporaneous In-Q-Tel investment agreement/portfolio record, CIA customer/development contract or named early deployment object"
  corporateOrInvestmentRecord
  "investment date/scope, customer authority, product object, participants, contract/development boundary"
  "In-Q-Tel/Palantir corporate record, procurement/contract record, contemporaneous testimony or authenticated archive"
  false

subjectSideHop : SnowballHop
subjectSideHop = snowball-hop
  "deployment-specific Palantir government customer object"
  "notice/privacy/impact/oversight/audit/challenge/remedy record for affected data subjects"
  oversightOrContestabilityRecord
  "burden, voice, contestability and remedy coordinates on the same deployment"
  "official policy, audit, court/tribunal, inspector-general, legislative or authenticated operational record"
  false

snowballFrontier : List SnowballHop
snowballFrontier = wadeRoleHop ∷ tiaDispositionHop ∷ earlyPalantirHop ∷ subjectSideHop ∷ []

------------------------------------------------------------------------
-- Acquisition/promotion firewalls.
------------------------------------------------------------------------

paretoPriorityCreatesHistoricalTruth : Bool
paretoPriorityCreatesHistoricalTruth = false

offFrontierDeletesRequirement : Bool
offFrontierDeletesRequirement = false

sourceMentionCreatesSameObjectEdge : Bool
sourceMentionCreatesSameObjectEdge = false

networkPathCreatesDirectTransfer : Bool
networkPathCreatesDirectTransfer = false

beneficiaryCreatesIntentOrMotive : Bool
beneficiaryCreatesIntentOrMotive = false

------------------------------------------------------------------------
-- Existing genealogy payment remains the strong-claim gate.
------------------------------------------------------------------------

privatizationPromotionStillBlocked :
  Genealogy.promotionReady Genealogy.currentPromotionReceipt ≡ false
privatizationPromotionStillBlocked = refl
