module DASHI.Cognition.PsychologicalInfluenceParetoRound20261013Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.NickLandProvocationOverreactionPopulistTransferExact as Acceleration
import DASHI.Cognition.BannonFaragePalmerAutomatedInfluenceReceiptsExact as Receipts
import DASHI.Cognition.EpsteinMasterPlanAttributionBoundaryExact as MasterPlan
import DASHI.Cognition.BannonPlaybookBondiMobilisationCrossPollinationExact as Mobilisation
import DASHI.Cognition.PsychologicalInfluenceInfrastructureCrossPollinationExact as Psych

------------------------------------------------------------------------
-- PSYCHOLOGICAL / POLITICAL INFLUENCE MAX-CUT PARETO — 2026-10-13
------------------------------------------------------------------------

data ParetoLane : Set where
  bannonPalmerAustraliaTransfer : ParetoLane
  palmerMassTargetingVendorStack : ParetoLane
  farageBannonMovementTransfer : ParetoLane
  epsteinBannonPoliticalPlanning : ParetoLane
  post9_11ProvocationInstitutionalLockIn : ParetoLane
  oneNationOfficialAIAutomation : ParetoLane
  bannonLandYarvinLineage : ParetoLane
  bondiFomentationPersistentCapacity : ParetoLane
  foreignProOneNationEngagementFarms : ParetoLane
  lnpTrumpBannonTechniqueTransfer : ParetoLane
  epsteinBlackmailLeverageArtifactChain : ParetoLane
  epsteinIntelligenceTasking : ParetoLane

record ParetoItem : Set where
  constructor pareto-item
  field
    lane : ParetoLane
    priority : Nat
    directReceiptStrength : Nat
    networkLeverage : Nat
    downstreamCapacity : Nat
    attributionDebt : Nat
    reading : String
open ParetoItem public

canonicalPsychologicalInfluenceFront : List ParetoItem
canonicalPsychologicalInfluenceFront =
  pareto-item bannonPalmerAustraliaTransfer 100 88 97 96 96
    "DOJ-released Bannon message explicitly claims he caused Palmer's anti-China/anti-climate ad spend; Palmer confirms one Bannon call but denies direction. High-value because the claimed transfer is same-object, contemporaneous and tied to a massive real campaign, while the decisive control edge remains disputed."
  ∷ pareto-item palmerMassTargetingVendorStack 99 98 97 95 90
    "The campaign's millions-scale geo-targeted SMS/robocall and saturation-media deployment is established. The missing object is the vendor/data/analytics stack: who supplied numbers, segmentation, creative, scheduling, optimisation and measurement."
  ∷ pareto-item farageBannonMovementTransfer 99 96 98 95 82
    "Filmed direct planning establishes Farage-Bannon collaboration around a transnational populist clearing-house with polling, funding and campaign-support ambitions. Resolve which Movement methods/assets actually entered Brexit Party/Reform operations."
  ∷ pareto-item epsteinBannonPoliticalPlanning 99 98 99 96 89
    "Almost 1,500 Bannon/Epstein emails plus WhatsApp traffic and direct discussion of The Movement, media projects, introductions and global political strategy make this one of the strongest live political-influence seams in the Epstein corpus."
  ∷ pareto-item post9_11ProvocationInstitutionalLockIn 98 95 100 100 84
    "Terrorist-provocation scholarship plus the durable War-on-Terror surveillance/intelligence/security architecture provides the canonical overreaction-to-lock-in comparator. Trace persistence into current Five Eyes, border, data and contractor systems."
  ∷ pareto-item oneNationOfficialAIAutomation 98 94 94 90 88
    "Official One Nation AI-generated campaign content is established. Resolve the party's own generation, targeting, CRM, scheduling, ad-tech and analytics stack separately from organic or monetised supporter ecosystems."
  ∷ pareto-item bannonLandYarvinLineage 97 82 96 91 90
    "Bannon's Yarvin readership and the literature's Land/Yarvin Dark-Enlightenment coupling pay an intellectual lineage stronger than analogy. Primary Bannon-by-name credit to Nick Land remains an acquisition debt despite secondary attributions that Land influenced or mentored Bannon-world."
  ∷ pareto-item epsteinBlackmailLeverageArtifactChain 97 78 100 100 100
    "Victims and their lawyers attribute leverage/control functions to trafficking; cameras and recording infrastructure are documented; the 2025 DOJ/FBI review rejected credible systematic-blackmail evidence. Resolve concrete artifact->person->request->benefit chains rather than arguing at theory level."
  ∷ pareto-item bondiFomentationPersistentCapacity 96 94 96 98 84
    "Treat the attack as genuine while tracing amplification/fomentation, agenda mobilisation, laws, policing/intelligence capacity, advocacy gains, reversals and persistent burden."
  ∷ pareto-item foreignProOneNationEngagementFarms 94 92 90 76 95
    "ABC/Guardian establish large foreign AI/engagement-farm ecosystems amplifying Hanson/One Nation to genuine Australian audiences. Current evidence does not establish party commissioning, so payment/instruction/shared-admin receipts are the decisive cut."
  ∷ pareto-item lnpTrumpBannonTechniqueTransfer 93 65 93 96 98
    "Queensland LNP crisis-to-capacity mobilisation is strong structurally. A Trump/Bannon method-transfer claim remains weak until consultants, vendors, advisers, training or campaign artefacts are found."
  ∷ pareto-item epsteinIntelligenceTasking 91 55 100 100 100
    "Raw CHS reports and public allegations keep intelligence-tasking worth acquiring, but no located primary service tasking/payment/handler record closes it. This stays below the better evidenced political, financial and brokerage lanes."
  ∷ []

------------------------------------------------------------------------
-- Top acquisition order: concrete same-object receipts first.
------------------------------------------------------------------------

data NextCut : Set where
  getPalmerVendorRecords : NextCut
  getBannonPalmerContactRecords : NextCut
  getFarageMovementOperationalRecords : NextCut
  getBannonEpsteinProjectMap : NextCut
  getOneNationOfficialAdTechStack : NextCut
  getLandPrimaryCredit : NextCut
  getBondiCapacityPersistence : NextCut
  getForeignFarmCommissioningEvidence : NextCut
  getEpsteinLeverageChains : NextCut
  getIntelligenceTaskingRecords : NextCut

record NextCutItem : Set where
  constructor next-cut-item
  field
    cut : NextCut
    priority : Nat
    sameObjectRequired : Bool
    instruction : String
open NextCutItem public

canonicalNextCuts : List NextCutItem
canonicalNextCuts =
  next-cut-item getBannonPalmerContactRecords 100 true
    "Acquire exact Bannon-Palmer communications/intermediaries and timestamp them against Palmer campaign creative and media-buy decisions."
  ∷ next-cut-item getPalmerVendorRecords 100 true
    "Acquire UAP/Palmer campaign expenditure, agency, SMS provider, data broker, targeting and analytics records for 2019 and 2020 Queensland campaigns."
  ∷ next-cut-item getFarageMovementOperationalRecords 99 true
    "Acquire Movement/Brexit Party/Reform polling, consultancy, vendor, funding and digital-campaign transfer records."
  ∷ next-cut-item getBannonEpsteinProjectMap 99 true
    "Map every Bannon-Epstein project/introduction/advice thread to downstream actions, money, meetings, media output and political beneficiaries."
  ∷ next-cut-item getOneNationOfficialAdTechStack 98 true
    "Resolve official One Nation AI/video studio, CRM, social scheduling, paid targeting, audience acquisition and analytics infrastructure."
  ∷ next-cut-item getLandPrimaryCredit 97 true
    "Find the primary Bannon statement naming Nick Land/Landian accelerationism; until then keep explicit-credit narrower than the paid Yarvin/Dark-Enlightenment lineage."
  ∷ next-cut-item getBondiCapacityPersistence 96 true
    "Trace post-Bondi exceptional measures through enactment, judicial review, persistence, budgets, procurement and institutional beneficiaries."
  ∷ next-cut-item getForeignFarmCommissioningEvidence 94 true
    "Test whether foreign pro-One-Nation engagement farms are paid/commissioned or merely independently monetising political outrage."
  ∷ next-cut-item getEpsteinLeverageChains 93 true
    "Resolve specific recording/leverage chains from artifact to identified subject to request/benefit, preserving allegation and counter-evidence."
  ∷ next-cut-item getIntelligenceTaskingRecords 90 true
    "Acquire service-tasking, handler, reporting or payment records before promoting any intelligence-employment theory."
  ∷ []
