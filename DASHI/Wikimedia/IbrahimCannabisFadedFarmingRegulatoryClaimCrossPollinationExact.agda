module DASHI.Wikimedia.IbrahimCannabisFadedFarmingRegulatoryClaimCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisContaminantToxicantAssayParetoExact as Contaminant
import DASHI.Wikimedia.IbrahimCannabisTerpenePubChemCIDAuthorityExact as TerpeneRegistry
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- FADEDFARMING SOCIAL-CLAIM / REGULATORY CROSS-POLLINATION OWNER
--
-- The attached discovery snapshot gives concrete Instagram reel URLs and
-- snippets for @fadedfarming / S. Exotic.  Those social objects are retained
-- as source-bounded claims, never as toxicology authority.  Regulatory and
-- chemical identity payments are made separately from primary public sources.
------------------------------------------------------------------------

data SocialCarrierKind : Set where
  instagramProfile
  instagramReel
  googleDiscoverySnapshot : SocialCarrierKind

data SocialClaimTopic : Set where
  thcaExperience
  organicPesticides
  pesticideUseOnCannabis
  soilMicrobiology
  blacklistWhitelistArchitecture : SocialClaimTopic

record SocialClaimCarrier : Set where
  constructor social-claim-carrier
  field
    handle : String
    displayName : String
    carrierKind : SocialCarrierKind
    topic : SocialClaimTopic
    exactURL : String
    displayedDateReference : String
    visibleSnippet : String
    snapshotSource : String
    exactPostObjectPaid : Bool
    fullTranscriptPaid : Bool
    authorLegalIdentityPaid : Bool
    scientificAuthorityPaid : Bool
open SocialClaimCarrier public

fadedProfile : SocialClaimCarrier
fadedProfile = social-claim-carrier
  "@fadedfarming" "S. Exotic" instagramProfile pesticideUseOnCannabis
  "https://www.instagram.com/fadedfarming/"
  "current public profile surface in attached Google discovery snapshot"
  "profile is described as cannabis cultivation/agricultural education content"
  "user-attached Google AI/search snapshot"
  true false false false

fadedThcaReel : SocialClaimCarrier
fadedThcaReel = social-claim-carrier
  "@fadedfarming" "S. Exotic" instagramReel thcaExperience
  "https://www.instagram.com/reel/DcLnDzDxYAX/"
  "public discovery snapshot; exact post date not retained in attached snippet"
  "My personal experience with THCA #agricultureworldwide ..."
  "user-attached Google AI/search snapshot"
  true false false false

fadedOrganicPesticidesReel : SocialClaimCarrier
fadedOrganicPesticidesReel = social-claim-carrier
  "@fadedfarming" "S. Exotic" instagramReel organicPesticides
  "https://www.instagram.com/reel/Db_d-oXPdTu/"
  "14 Aug 2026"
  "Organic pesticides??"
  "user-attached Google AI/search snapshot"
  true false false false

fadedPesticideIndustryReel : SocialClaimCarrier
fadedPesticideIndustryReel = social-claim-carrier
  "@fadedfarming" "S. Exotic" instagramReel pesticideUseOnCannabis
  "https://www.instagram.com/reel/Dc9ru24vk-S/"
  "7 Sept 2026"
  "Admire Systemic Pro + Previcur Flex Fungicide a major issue; visible snippet says not to use on weed unless research permits are submitted to a controlled public database"
  "user-attached Google AI/search snapshot"
  true false false false

fadedSoilMicrobiologyReel : SocialClaimCarrier
fadedSoilMicrobiologyReel = social-claim-carrier
  "@fadedfarming" "S. Exotic" instagramReel soilMicrobiology
  "https://www.instagram.com/reel/Dc5q63AR_GI/"
  "5 Sept 2026"
  "visible snippet: no soil health recommendation without soil microbiology"
  "user-attached Google AI/search snapshot"
  true false false false

------------------------------------------------------------------------
-- Candidate chemical identities from the attached social-content summary.
-- These rows pay PubChem identity only.  They do not prove that a particular
-- @fadedfarming reel contains the entire summarized claim, nor occurrence in a
-- cannabis sample, nor toxic dose.
------------------------------------------------------------------------

data CandidateChemical : Set where
  imidacloprid
  propamocarb
  paclobutrazol
  daminozide
  abamectin
  azadirachtinA
  glyphosate : CandidateChemical

record ChemicalRegistryReceipt : Set where
  constructor chemical-registry-receipt
  field
    chemical : CandidateChemical
    label : String
    pubChemCID : String
    pubChemLink : String
    formula : String
    registryPaid : Bool
    occurrenceInCannabisPaid : Bool
    toxicExposurePaid : Bool
open ChemicalRegistryReceipt public

imidaclopridRegistry : ChemicalRegistryReceipt
imidaclopridRegistry = chemical-registry-receipt
  imidacloprid "imidacloprid" "86287518"
  "https://pubchem.ncbi.nlm.nih.gov/compound/86287518"
  "C9H10ClN5O2" true false false

propamocarbRegistry : ChemicalRegistryReceipt
propamocarbRegistry = chemical-registry-receipt
  propamocarb "propamocarb" "32490"
  "https://pubchem.ncbi.nlm.nih.gov/compound/32490"
  "C9H20N2O2" true false false

paclobutrazolRegistry : ChemicalRegistryReceipt
paclobutrazolRegistry = chemical-registry-receipt
  paclobutrazol "paclobutrazol" "73671"
  "https://pubchem.ncbi.nlm.nih.gov/compound/73671"
  "C15H20ClN3O" true false false

daminozideRegistry : ChemicalRegistryReceipt
daminozideRegistry = chemical-registry-receipt
  daminozide "daminozide" "15331"
  "https://pubchem.ncbi.nlm.nih.gov/compound/15331"
  "C6H12N2O3" true false false

abamectinRegistry : ChemicalRegistryReceipt
abamectinRegistry = chemical-registry-receipt
  abamectin "abamectin mixture" "9920327"
  "https://pubchem.ncbi.nlm.nih.gov/compound/9920327"
  "C95H142O28" true false false

azadirachtinRegistry : ChemicalRegistryReceipt
azadirachtinRegistry = chemical-registry-receipt
  azadirachtinA "azadirachtin / azadirachtin A" "5281303"
  "https://pubchem.ncbi.nlm.nih.gov/compound/5281303"
  "C35H44O16" true false false

glyphosateRegistry : ChemicalRegistryReceipt
glyphosateRegistry = chemical-registry-receipt
  glyphosate "glyphosate" "3496"
  "https://pubchem.ncbi.nlm.nih.gov/compound/3496"
  "C3H8NO5P" true false false

------------------------------------------------------------------------
-- Product label and regulatory architecture.
------------------------------------------------------------------------

data RegulatoryArchitecture : Set where
  prohibitedCriteria
  positiveLegalUseCriteria
  residueTestingPanel
  pharmacopoeialQualityStandard
  pureBlacklist
  pureWhitelist : RegulatoryArchitecture

record RegulatoryReceipt : Set where
  constructor regulatory-receipt
  field
    jurisdiction : String
    source : String
    directLink : String
    architecture : RegulatoryArchitecture
    boundedReading : String
    excludedPromotion : String
    currentSourcePaid : Bool
open RegulatoryReceipt public

californiaLegalUseCriteria : RegulatoryReceipt
californiaLegalUseCriteria = regulatory-receipt
  "California, USA"
  "California Department of Pesticide Regulation, List of Products Legal to Use on Cannabis, ENF 24-19 (2024)"
  "https://www.cdpr.ca.gov/cac-letter/list-of-products-legal-to-use-on-cannabis/"
  positiveLegalUseCriteria
  "California publishes criteria and a positive list of products meeting state legal-use criteria for cannabis; the list is explicitly not exhaustive and not an endorsement."
  "Do not reduce California to a pure blacklist or infer inhalation safety merely from legal-use status."
  true

californiaCannotUse : RegulatoryReceipt
californiaCannotUse = regulatory-receipt
  "California, USA"
  "California Department of Pesticide Regulation, Pesticides That Cannot Be Used on Cannabis"
  "https://www.cdpr.ca.gov/docs/cannabis/cannot_use_pesticide.pdf"
  prohibitedCriteria
  "Representative cannot-use criteria include non-food-use products, restricted materials, groundwater-protection chemicals and certain signal-word categories; examples include paclobutrazol and daminozide as non-food-use, abamectin as restricted, and imidacloprid on the groundwater-protection list."
  "Representative examples are not an exhaustive universe of prohibited chemistry and do not establish occurrence in a specific cannabis product."
  true

australiaTGO93 : RegulatoryReceipt
australiaTGO93 = regulatory-receipt
  "Australia"
  "Therapeutic Goods Administration, TGO 93 medicinal cannabis quality requirements"
  "https://www.tga.gov.au/resources/guidance/complying-quality-requirements-medicinal-cannabis"
  pharmacopoeialQualityStandard
  "TGO 93 requires batch-level quality controls including aflatoxins, ochratoxin A, foreign matter, heavy metals, pesticides and total ash, plus active-ingredient assay requirements."
  "TGO 93 is not literally a universal cultivation-input whitelist; it is a medicinal-product quality standard with specified tests, limits, validated methods and GMP obligations."
  true

------------------------------------------------------------------------
-- Specific product-label discriminator for the visible Admire/Previcur claim.
------------------------------------------------------------------------

record ProductLabelReceipt : Set where
  constructor product-label-receipt
  field
    productName : String
    activeIngredient : String
    registrationReference : String
    labelledCropsReference : String
    cannabisOnLabelPaid : Bool
    systemicOrMobilityReference : String
    labelSource : String
open ProductLabelReceipt public

previcurFlexLabel : ProductLabelReceipt
previcurFlexLabel = product-label-receipt
  "Previcur Flex"
  "propamocarb hydrochloride"
  "EPA Reg. No. 264-678"
  "US label lists cucurbits, leafy greens, guava, lima beans, peppers/eggplants, starfruit, tomatoes and tuberous/corm vegetables; cannabis is not listed"
  false
  "manufacturer describes Previcur Flex as systemic / penetrating plant tissues"
  "Bayer / EPA-approved US product label"

------------------------------------------------------------------------
-- Blacklist/whitelist claim repair.
------------------------------------------------------------------------

record RegulatoryDesignClaim : Set where
  constructor regulatory-design-claim
  field
    socialClaimReference : String
    candidateReading : String
    californiaPureBlacklistPaid : Bool
    californiaHasPositiveLegalCriteriaPaid : Bool
    australiaPureWhitelistPaid : Bool
    australiaBatchQualityStandardPaid : Bool
    repairedReading : String
open RegulatoryDesignClaim public

blacklistWhitelistRepair : RegulatoryDesignClaim
blacklistWhitelistRepair = regulatory-design-claim
  "attached Google AI summary attributes a blacklist-vs-whitelist critique to @fadedfarming"
  "finite prohibited-analyte panels can miss unlisted compounds; permissive legal-use criteria and positive product lists are a different regulatory design dimension"
  false true false true
  "model jurisdictions by explicit admission/prohibition/testing rules, not one blacklist/whitelist scalar: California combines legal-use criteria, cannot-use criteria and residue testing; Australia TGO 93 imposes pharmacopoeial batch-quality testing rather than a literal all-input whitelist"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SocialSummaryCreatesExactTranscript : Set where
data SocialClaimCreatesToxicology : Set where
data ProductNotOnLabelCreatesPoisoning : Set where
data LegalUseCreatesInhalationSafety : Set where
data RegulatoryListCreatesOccurrence : Set where
data TGO93CreatesPureWhitelist : Set where

socialSummaryDoesNotCreateExactTranscript : SocialSummaryCreatesExactTranscript → ⊥
socialSummaryDoesNotCreateExactTranscript ()

socialClaimDoesNotCreateToxicology : SocialClaimCreatesToxicology → ⊥
socialClaimDoesNotCreateToxicology ()

productNotOnLabelDoesNotCreatePoisoning : ProductNotOnLabelCreatesPoisoning → ⊥
productNotOnLabelDoesNotCreatePoisoning ()

legalUseDoesNotCreateInhalationSafety : LegalUseCreatesInhalationSafety → ⊥
legalUseDoesNotCreateInhalationSafety ()

regulatoryListDoesNotCreateOccurrence : RegulatoryListCreatesOccurrence → ⊥
regulatoryListDoesNotCreateOccurrence ()

tgo93DoesNotCreatePureWhitelist : TGO93CreatesPureWhitelist → ⊥
tgo93DoesNotCreatePureWhitelist ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data FadedParetoTarget : Set where
  exactReelTranscript
  exactProductLabelJoin
  exactCannabisResidueOccurrence
  combustionVaporisationTransform
  routeSpecificToxicology
  regulatoryArchitectureComparison
  genericSocialSnowball : FadedParetoTarget

record FadedParetoStep : Set where
  constructor faded-pareto-step
  field
    priority : Nat
    target : FadedParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open FadedParetoStep public

pareto0 : FadedParetoStep
pareto0 = faded-pareto-step
  0 exactReelTranscript
  "acquire transcript/media snapshot for Dc9ru24vk-S and Db_d-oXPdTu; retain post timestamp/account snapshot and exact literal propositions"
  "social-source claim identity"
  "none"

pareto1 : FadedParetoStep
pareto1 = faded-pareto-step
  1 exactProductLabelJoin
  "join Admire Pro and Previcur Flex exact EPA/California labels and active ingredients to the social claim"
  "legal-use and product-identity discriminator"
  "claim text should be acquired in parallel"

pareto2 : FadedParetoStep
pareto2 = faded-pareto-step
  2 exactCannabisResidueOccurrence
  "find measured cannabis samples containing the named chemicals, with concentration, LOQ, sample identity and method uncertainty"
  "moves from possible/misuse claim to empirical occurrence"
  "registry and sample identity required"

pareto3 : FadedParetoStep
pareto3 = faded-pareto-step
  3 combustionVaporisationTransform
  "acquire analyte-specific transfer/degradation data under smoking or vaporisation rather than importing oral/agricultural hazard language"
  "route-specific exposure transformation"
  "measured starting concentration required"

pareto4 : FadedParetoStep
pareto4 = faded-pareto-step
  4 routeSpecificToxicology
  "compare transferred inhaled dose with analyte-specific toxicological evidence"
  "consumer hazard conclusion"
  "dominated by occurrence and transfer"

pareto5 : FadedParetoStep
pareto5 = faded-pareto-step
  5 regulatoryArchitectureComparison
  "compare California legal-use/prohibition/testing composition with TGO 93 pharmacopoeial quality controls without forcing either into a one-bit blacklist/whitelist label"
  "regulatory-design insight"
  "current primary sources already pay a bounded first pass"

pareto99 : FadedParetoStep
pareto99 = faded-pareto-step
  99 genericSocialSnowball
  "do not ingest more broad social summaries until they distinguish a live chemical, occurrence, route or regulatory hypothesis"
  "nothing by itself"
  "dominated by exact post and primary evidence"

------------------------------------------------------------------------
-- Temporal evidence fibre.
------------------------------------------------------------------------

data FadedTime : Set where
  attachedDiscoverySnapshot
  primaryRegistryAndLabelCheck
  currentDashi : FadedTime

data FadedInterpretation : Set where
  fadedContentExists
  exactPesticideClaimPartiallyLocated
  namedChemicalsRegistryResolved
  socialClaimScientificallyProven
  regulatoryArchitectureRequiresMoreThanBlacklistWhitelist : FadedInterpretation

data FadedSummary : Set where socialAndPrimaryEvidenceRemainSeparate : FadedSummary

FadedCompatible : FadedTime → FadedInterpretation → Set
FadedCompatible attachedDiscoverySnapshot fadedContentExists = ⊤
FadedCompatible attachedDiscoverySnapshot exactPesticideClaimPartiallyLocated = ⊤
FadedCompatible attachedDiscoverySnapshot namedChemicalsRegistryResolved = ⊥
FadedCompatible attachedDiscoverySnapshot socialClaimScientificallyProven = ⊥
FadedCompatible attachedDiscoverySnapshot regulatoryArchitectureRequiresMoreThanBlacklistWhitelist = ⊤
FadedCompatible primaryRegistryAndLabelCheck fadedContentExists = ⊤
FadedCompatible primaryRegistryAndLabelCheck exactPesticideClaimPartiallyLocated = ⊤
FadedCompatible primaryRegistryAndLabelCheck namedChemicalsRegistryResolved = ⊤
FadedCompatible primaryRegistryAndLabelCheck socialClaimScientificallyProven = ⊥
FadedCompatible primaryRegistryAndLabelCheck regulatoryArchitectureRequiresMoreThanBlacklistWhitelist = ⊤
FadedCompatible currentDashi fadedContentExists = ⊤
FadedCompatible currentDashi exactPesticideClaimPartiallyLocated = ⊤
FadedCompatible currentDashi namedChemicalsRegistryResolved = ⊤
FadedCompatible currentDashi socialClaimScientificallyProven = ⊥
FadedCompatible currentDashi regulatoryArchitectureRequiresMoreThanBlacklistWhitelist = ⊤

fadedTemporalSystem : Temporal.TemporalEvidenceSystem
fadedTemporalSystem = record
  { Time = FadedTime
  ; Interpretation = FadedInterpretation
  ; Compatible = FadedCompatible
  ; Summary = FadedSummary
  ; summarize = λ _ → socialAndPrimaryEvidenceRemainSeparate
  ; timeReference = λ
      { attachedDiscoverySnapshot → "user-attached Google discovery snapshot for @fadedfarming, September 2026"
      ; primaryRegistryAndLabelCheck → "PubChem + California DPR + Bayer/EPA label + Australian TGA primary-source check"
      ; currentDashi → "current DASHI fadedfarming/cannabis contaminant cross-pollination frontier"
      }
  }

currentFadedFibre : Temporal.EvidenceFibre fadedTemporalSystem currentDashi
currentFadedFibre = Temporal.liveInterpretationAt regulatoryArchitectureRequiresMoreThanBlacklistWhitelist tt

record FadedFarmingCrossPollinationBoundary : Set where
  constructor faded-farming-crosspollination-boundary
  field
    socialSourceRetained : Bool
    exactReelURLsRetained : Bool
    pubChemOwnsChemicalCID : Bool
    socialClaimCreatesAuthority : Bool
    californiaReducedToPureBlacklist : Bool
    australiaReducedToPureWhitelist : Bool
    occurrenceRequiredBeforeExposure : Bool
    routeSpecificToxicologyRequired : Bool
open FadedFarmingCrossPollinationBoundary public

canonicalFadedFarmingCrossPollinationBoundary : FadedFarmingCrossPollinationBoundary
canonicalFadedFarmingCrossPollinationBoundary =
  faded-farming-crosspollination-boundary
    true true true false false false true true
