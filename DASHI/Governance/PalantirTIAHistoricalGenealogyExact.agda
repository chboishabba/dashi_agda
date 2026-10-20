module DASHI.Governance.PalantirTIAHistoricalGenealogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Governance.IranContraCovertFlowHistoricalMechanismExact as IranContra
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir

------------------------------------------------------------------------
-- PALANTIR / TOTAL INFORMATION AWARENESS HISTORICAL GENEALOGY
--
-- This owner is an attributed, evidence-graded specialisation of the existing
-- EvidenceGradedGenealogyCore.  It does not create a parallel genealogy
-- calculus.  A/B remain the repository's strong historical grades; C/D/E do
-- not become strong edges merely because a speaker, article or analogy names
-- them.
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
  "contemporaneous interview identifying Poindexter as former head of DARPA's Information Awareness Office after congressional termination pressure"
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
  "Christine Maxwell biography: co-founded Chiliad; describes Bayesian/natural-language software for analysis across clouds, defence agencies, departments and other stovepipes"
  Source.publicAttribution

mccormackWebb : Source.AttributedSource
mccormackWebb = Source.mkNoDOISource
  "Peter McCormack; Whitney Webb"
  "Epstein, Intelligence and the Global Network of Power"
  "The Peter McCormack Show, episode 110"
  "2025-09-25"
  "https://www.petermccormack.com/episodes/110-whitney-webb-epstein-intelligence-and-the-global-network-of-power"
  Source.practitionerSource
  "source object for Webb's Palantir/TIA/Wade/Chiliad assertions; interview attribution does not independently prove those historical propositions"
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Palantir/TIA historical genealogy source atlas"
  "DASHI.Governance.PalantirTIAHistoricalGenealogyExact"
  (govInfoTIA ∷ wiredJoiningDots ∷ wiredPoindexter ∷ bloombergWade ∷ maxwellISGAP ∷ mccormackWebb ∷ [])
  "programme governance; direct contact; capital/development; Chiliad identity/capability; interview-attributed stronger claims"

------------------------------------------------------------------------
-- Attributed edge wrapper: reuse Genealogy grade/relation types while keeping
-- the repository-wide AttributedSourceCore provenance object.
------------------------------------------------------------------------

record AttributedGenealogyEdge : Set where
  constructor attributed-genealogy-edge
  field
    fromNode : String
    toNode : String
    relation : Genealogy.PathwayRelation
    grade : Genealogy.EvidenceGrade
    source : Source.AttributedSource
    boundedClaim : String

open AttributedGenealogyEdge public

tiaCongressionalEdge : AttributedGenealogyEdge
tiaCongressionalEdge = attributed-genealogy-edge
  "DARPA Information Awareness Office / TIA"
  "Congressional oversight / successor-component restriction"
  Genealogy.directDocumentedTransfer
  Genealogy.gradeA
  govInfoTIA
  "Congress documented/regimented TIA and expressly contemplated related, successor and transferred programme components."

perleMeetingEdge : AttributedGenealogyEdge
perleMeetingEdge = attributed-genealogy-edge
  "Alex Karp + Peter Thiel"
  "John Poindexter, meeting at Richard Perle's home"
  Genealogy.personnelInstitutionalContinuity
  Genealogy.gradeB
  wiredJoiningDots
  "Wired records Poindexter's own account of the meeting shortly after Palantir was formed."

inQTelEdge : AttributedGenealogyEdge
inQTelEdge = attributed-genealogy-edge
  "In-Q-Tel"
  "Palantir"
  Genealogy.fundingOrganisationalLink
  Genealogy.gradeB
  wiredJoiningDots
  "Wired records In-Q-Tel investment and intelligence-community access during Palantir's early development."

ciaFeedbackEdge : AttributedGenealogyEdge
ciaFeedbackEdge = attributed-genealogy-edge
  "CIA analysts"
  "Palantir early product development"
  Genealogy.personnelInstitutionalContinuity
  Genealogy.gradeB
  wiredJoiningDots
  "Wired records iterative CIA analyst testing/feedback during Palantir's early development."

wadeChiliadEdge : AttributedGenealogyEdge
wadeChiliadEdge = attributed-genealogy-edge
  "Alan C. Wade"
  "Chiliad Inc."
  Genealogy.personnelInstitutionalContinuity
  Genealogy.gradeB
  bloombergWade
  "Bloomberg identifies Wade as Chairman/Founder of Chiliad; this receipt does not establish a TIA role."

maxwellChiliadEdge : AttributedGenealogyEdge
maxwellChiliadEdge = attributed-genealogy-edge
  "Christine Maxwell"
  "Chiliad Inc."
  Genealogy.personnelInstitutionalContinuity
  Genealogy.gradeB
  maxwellISGAP
  "Maxwell's institutional biography identifies her as a Chiliad co-founder."

chiliadCapabilityEdge : AttributedGenealogyEdge
chiliadCapabilityEdge = attributed-genealogy-edge
  "Chiliad"
  "cross-stovepipe data analysis"
  Genealogy.sharedMethodOnly
  Genealogy.gradeD
  maxwellISGAP
  "Institutional biography describes Bayesian/natural-language analysis across clouds, defence agencies, departments and other stovepipes."

webbWadeTIACandidateEdge : AttributedGenealogyEdge
webbWadeTIACandidateEdge = attributed-genealogy-edge
  "Alan C. Wade"
  "Total Information Awareness intelligence-community participation"
  Genealogy.audienceContentAdjacency
  Genealogy.gradeC
  mccormackWebb
  "Webb attributes an intimate TIA role to Wade; a primary/official same-person TIA-role receipt remains unpaid here."

------------------------------------------------------------------------
-- Capability observation: evidence of similarity is not programme identity.
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

    -- Iran/Contra is a reusable routing precedent, not evidence for this edge.
    iranContraAnalogyCreatesGenealogy : Bool

open TIAPalantirGenealogy public

canonicalTIAGenealogy : TIAPalantirGenealogy
canonicalTIAGenealogy = tia-palantir-genealogy
  true true true true true true true true
  false false false false false false

------------------------------------------------------------------------
-- Promotion contract: strong rhetoric requires same-object continuity payment.
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

meetingDoesNotCreateTransfer : PerleMeetingMeansProgrammeTransfer → ⊥
meetingDoesNotCreateTransfer ()

investmentDoesNotCreatePrivatization : InQTelInvestmentMeansPrivatizedTIA → ⊥
investmentDoesNotCreatePrivatization ()

chiliadFounderReceiptDoesNotCreateTIARole :
  WadeChiliadFounderMeansWadeTIAPointMan → ⊥
chiliadFounderReceiptDoesNotCreateTIARole ()

iranContraDoesNotCreateThisGenealogy :
  IranContraTopologyMeansTIAPalantirGenealogy → ⊥
iranContraDoesNotCreateThisGenealogy ()

------------------------------------------------------------------------
-- Cross-pollination receipts to prior art.
------------------------------------------------------------------------

genealogyBoundaryReused :
  Genealogy.gradeAorBRequiredForStrongHistoricalEdge
    Genealogy.canonicalEvidenceGradedGenealogyBoundary
  ≡ true
genealogyBoundaryReused = refl

palantirCapabilityBoundaryReused :
  Palantir.genericCapabilityEqualsAbuse Palantir.canonicalPalantirCapabilityBoundary ≡ false
palantirCapabilityBoundaryReused = refl

iranContraRoutingPrecedentReused :
  IranContra.publicPolicyAndOperationalPracticeDiverged IranContra.iranContraTopology ≡ true
iranContraRoutingPrecedentReused = refl
