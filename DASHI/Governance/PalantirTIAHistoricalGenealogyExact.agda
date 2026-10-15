module DASHI.Governance.PalantirTIAHistoricalGenealogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Governance.IranContraCovertFlowHistoricalMechanismExact as IranContra
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir

------------------------------------------------------------------------
-- PALANTIR / TOTAL INFORMATION AWARENESS HISTORICAL GENEALOGY
--
-- Purpose: separate documented programme/contact/capital/capability edges from
-- the stronger interpretive claim that Palantir was literally a privatised or
-- successor implementation of TIA.
--
-- Existing owners remain authoritative for:
--   * Iran/Contra covert-routing topology and its non-analogy boundaries;
--   * generic Palantir platform capability and deployment-specific gaps.
------------------------------------------------------------------------

govInfoTIA : Source.AttributedSource
govInfoTIA = Source.mkNoDOISource
  "United States Congress"
  "Congressional Record, amendment limiting Total Information Awareness"
  "Congressional Record"
  "2003"
  "https://www.govinfo.gov/content/pkg/CRECB-2003-pt2/html/CRECB-2003-pt2-issue-2003-01-23.htm"
  Source.governmentSource
  "primary legislative record: TIA programme, Poindexter direction, privacy/civil-liberties concerns, and definition including related/successor/transferred programme components"
  Source.publicAttribution

wiredJoiningDots : Source.AttributedSource
wiredJoiningDots = Source.mkNoDOISource
  "Noah Shachtman"
  "Palantir Technologies spots patterns to solve crimes and track terrorists"
  "Wired"
  "2012"
  "https://www.wired.com/story/joining-the-dots/"
  Source.newsSource
  "near-primary company history including Poindexter's own account of meeting Karp and Thiel at Richard Perle's home; records TIA similarity, In-Q-Tel investment and CIA-facing development history"
  Source.publicAttribution

wiredPoindexter : Source.AttributedSource
wiredPoindexter = Source.mkNoDOISource
  "Wired"
  "Poindexter Confidential"
  "Wired"
  "2004"
  "https://www.wired.com/2004/05/poindexter/"
  Source.newsSource
  "contemporaneous interview identifying Poindexter as former head of DARPA's Information Awareness Office after Congress forced his departure"
  Source.publicAttribution

bloombergWade : Source.AttributedSource
bloombergWade = Source.mkNoDOISource
  "Bloomberg Markets"
  "Alan C Wade, Chiliad Inc: Profile and Biography"
  "Bloomberg"
  "undated profile accessed 2026"
  "https://www.bloomberg.com/profile/person/15334046"
  Source.newsSource
  "bounded biographical receipt identifying Alan C. Wade as Chairman/Founder of Chiliad Inc.; does not establish his TIA role"
  Source.publicAttribution

maxwellISGAP : Source.AttributedSource
maxwellISGAP = Source.mkNoDOISource
  "Institute for the Study of Global Antisemitism and Policy"
  "Summer Institute 2021 Digital Program: Christine Malina Maxwell biography"
  "ISGAP"
  "2021"
  "https://isgap.org/wp-content/uploads/2021/09/Summer-Institute-2021-Digital-Program.pdf"
  Source.institutionalSource
  "Christine Maxwell self-biographical programme entry: co-founded Chiliad; describes Bayesian/natural-language software for analysis across clouds, defence agencies, departments and other stovepipes"
  Source.publicAttribution

mccormackWebb : Source.AttributedSource
mccormackWebb = Source.mkNoDOISource
  "Peter McCormack; Whitney Webb"
  "Epstein, Intelligence and the Global Network of Power"
  "The Peter McCormack Show, episode 110"
  "2025-09-25"
  "https://www.petermccormack.com/episodes/110-whitney-webb-epstein-intelligence-and-the-global-network-of-power"
  Source.practitionerSource
  "source object for Webb's Palantir/TIA/Wade/Chiliad claims; interview attribution does not independently prove those historical propositions"
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Palantir/TIA historical genealogy source atlas"
  "DASHI.Governance.PalantirTIAHistoricalGenealogyExact"
  (govInfoTIA ∷ wiredJoiningDots ∷ wiredPoindexter ∷ bloombergWade ∷ maxwellISGAP ∷ mccormackWebb ∷ [])
  "programme existence/governance; direct contact; capital/development; Chiliad identities/capability; interview-attributed stronger claims"

data GenealogyEdgeKind : Set where
  programmeGovernanceEdge : GenealogyEdgeKind
  interpersonalContactEdge : GenealogyEdgeKind
  investmentAccessEdge : GenealogyEdgeKind
  engineeringFeedbackEdge : GenealogyEdgeKind
  personnelRoleEdge : GenealogyEdgeKind
  productCapabilityEdge : GenealogyEdgeKind
  institutionalSuccessionEdge : GenealogyEdgeKind

record HistoricalGenealogyEdge : Set where
  constructor historical-genealogy-edge
  field
    edgeKind : GenealogyEdgeKind
    fromNode : String
    toNode : String
    source : Source.AttributedSource
    boundedReading : String
    documented : Bool

open HistoricalGenealogyEdge public

tiaCongressionalEdge : HistoricalGenealogyEdge
tiaCongressionalEdge = historical-genealogy-edge
  programmeGovernanceEdge
  "DARPA Information Awareness Office / Total Information Awareness"
  "Congressional oversight / successor-component restrictions"
  govInfoTIA
  "Congress documented and regulated TIA and expressly contemplated related, successor and transferred programme components."
  true

perleMeetingEdge : HistoricalGenealogyEdge
perleMeetingEdge = historical-genealogy-edge
  interpersonalContactEdge
  "Alex Karp + Peter Thiel"
  "John Poindexter"
  wiredJoiningDots
  "Wired reports Poindexter's own account that Karp and Thiel met him at Richard Perle's home shortly after Palantir was formed."
  true

inQTelEdge : HistoricalGenealogyEdge
inQTelEdge = historical-genealogy-edge
  investmentAccessEdge
  "In-Q-Tel"
  "Palantir"
  wiredJoiningDots
  "Wired records In-Q-Tel investment and CIA-facing access during Palantir's early development."
  true

ciaFeedbackEdge : HistoricalGenealogyEdge
ciaFeedbackEdge = historical-genealogy-edge
  engineeringFeedbackEdge
  "CIA analysts"
  "Palantir early product development"
  wiredJoiningDots
  "Wired records iterative CIA analyst testing/feedback as part of Palantir's early development history."
  true

wadeChiliadEdge : HistoricalGenealogyEdge
wadeChiliadEdge = historical-genealogy-edge
  personnelRoleEdge
  "Alan C. Wade"
  "Chiliad Inc."
  bloombergWade
  "Bloomberg identifies Wade as Chairman/Founder of Chiliad Inc.; this receipt does not establish a TIA role."
  true

maxwellChiliadEdge : HistoricalGenealogyEdge
maxwellChiliadEdge = historical-genealogy-edge
  personnelRoleEdge
  "Christine Maxwell"
  "Chiliad Inc."
  maxwellISGAP
  "Maxwell's institutional biography identifies her as a Chiliad co-founder."
  true

chiliadCapabilityEdge : HistoricalGenealogyEdge
chiliadCapabilityEdge = historical-genealogy-edge
  productCapabilityEdge
  "Chiliad"
  "cross-stovepipe data analysis"
  maxwellISGAP
  "Institutional biography describes Bayesian/natural-language analysis across clouds, defence agencies, departments and other stovepipes."
  true

------------------------------------------------------------------------
-- Same-capability comparison: structural similarity is not genealogy.
------------------------------------------------------------------------

record CapabilityContinuityObservation : Set where
  constructor capability-continuity-observation
  field
    tiaCrossSourceIntegrationDocumented : Bool
    palantirObjectLinkIntegrationDocumented : Bool
    chiliadCrossStovepipeAnalysisDocumented : Bool
    sharedCapabilityFamilyObserved : Bool
    sharedCapabilityProvesDirectSuccession : Bool

open CapabilityContinuityObservation public

canonicalCapabilityContinuity : CapabilityContinuityObservation
canonicalCapabilityContinuity = capability-continuity-observation
  true
  Palantir.genericPlatformCapabilityEstablished Palantir.ontologyGraphCapability
  true
  true
  false

------------------------------------------------------------------------
-- Terminal evidence ledger.
------------------------------------------------------------------------

record TIAPalantirGenealogy : Set where
  constructor tia-palantir-genealogy
  field
    tiaProgrammeDocumented : Bool
    poindexterDirectedTIA : Bool
    perleHouseMeetingDocumented : Bool
    inQTelPalantirInvestmentDocumented : Bool
    ciaIterativeFeedbackDocumented : Bool
    chiliadMaxwellCofounderDocumented : Bool
    chiliadWadeFounderDocumented : Bool
    sharedDataIntegrationCapabilityObserved : Bool

    -- Explicit unpaid / non-promoted edges.
    wadeTIAPointManPrimaryReceiptInstalled : Bool
    sameObjectPersonnelTransferReceiptInstalled : Bool
    sameObjectProgrammeAssetTransferReceiptInstalled : Bool
    sameObjectContractScopeContinuationReceiptInstalled : Bool
    palantirIsPrivatizedTIAPromoted : Bool

    -- Existing historical analogy does not create this genealogy.
    iranContraAnalogyCreatesGenealogy : Bool

open TIAPalantirGenealogy public

canonicalTIAGenealogy : TIAPalantirGenealogy
canonicalTIAGenealogy = tia-palantir-genealogy
  true
  true
  true
  true
  true
  true
  true
  true
  false
  false
  false
  false
  false
  false

------------------------------------------------------------------------
-- Strong-claim promotion requires same-object receipts rather than topology.
------------------------------------------------------------------------

record PrivatizedTIAPromotionReceipt : Set where
  constructor privatized-tia-promotion-receipt
  field
    programmeIdentityReceipt : Bool
    assetOrCodeTransferReceipt : Bool
    personnelAuthorityContinuityReceipt : Bool
    procurementOrContractScopeReceipt : Bool
    institutionalDecisionAuthorityReceipt : Bool

open PrivatizedTIAPromotionReceipt public

promotionReady : PrivatizedTIAPromotionReceipt → Bool
promotionReady (privatized-tia-promotion-receipt true true true true true) = true
promotionReady _ = false

currentPromotionReceipt : PrivatizedTIAPromotionReceipt
currentPromotionReceipt = privatized-tia-promotion-receipt
  false false false false false

currentPromotionBlocked : promotionReady currentPromotionReceipt ≡ false
currentPromotionBlocked = refl

data SimilarCapabilityMeansSameProgramme : Set where
data PerleMeetingMeansProgrammeTransfer : Set where
data InQTelInvestmentMeansPrivatizedTIA : Set where
data WadeChiliadFounderMeansWadeTIAPointMan : Set where
data IranContraTopologyMeansTIAPalantirGenealogy : Set where

similarCapabilityDoesNotCreateProgrammeIdentity :
  SimilarCapabilityMeansSameProgramme → ⊥
similarCapabilityDoesNotCreateProgrammeIdentity ()

meetingDoesNotCreateTransfer :
  PerleMeetingMeansProgrammeTransfer → ⊥
meetingDoesNotCreateTransfer ()

investmentDoesNotCreatePrivatization :
  InQTelInvestmentMeansPrivatizedTIA → ⊥
investmentDoesNotCreatePrivatization ()

chiliadFounderReceiptDoesNotCreateTIARole :
  WadeChiliadFounderMeansWadeTIAPointMan → ⊥
chiliadFounderReceiptDoesNotCreateTIARole ()

iranContraDoesNotCreateThisGenealogy :
  IranContraTopologyMeansTIAPalantirGenealogy → ⊥
iranContraDoesNotCreateThisGenealogy ()

------------------------------------------------------------------------
-- Explicit cross-pollination receipts to existing owners.
------------------------------------------------------------------------

palantirCapabilityBoundaryReused :
  Palantir.genericCapabilityEqualsAbuse Palantir.canonicalPalantirCapabilityBoundary ≡ false
palantirCapabilityBoundaryReused = refl

iranContraNonAnalogyBoundaryReused :
  IranContra.publicPolicyAndOperationalPracticeDiverged IranContra.iranContraTopology ≡ true
iranContraNonAnalogyBoundaryReused = refl
