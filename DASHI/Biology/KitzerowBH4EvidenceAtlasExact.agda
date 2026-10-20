module DASHI.Biology.KitzerowBH4EvidenceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- KITZEROW BH4 / AUTISM EVIDENCE ATLAS
--
-- This is a bounded evidence/provenance owner, not a clinical theory owner.
-- It records later studies against the earlier Kitzerow candidate architecture
-- while refusing three common promotions:
--   (1) support for a node/edge -> confirmation of the complete graph;
--   (2) temporal priority -> proof of access/copying;
--   (3) claimed contact/access -> proof of plagiarism.
--
-- Primary Kitzerow source family acquired for this pass:
--   2024-01  "Autism & the Comorbidities Along the BH4 Pathway"
--             DOI 10.13140/RG.2.2.23124.37761/1
--   2024-08  "The BH4 Pathway as an Allostatic Mechanism in the Pathology
--             of Autism and Systemic Comorbidities"
--             ResearchGate preprint / DOI metadata varies by revision.
--   2025-07  "Neurodivergent Biochemistry and the Autism and the
--             Comorbidities Theory"
--             DOI 10.13140/RG.2.2.30248.89606
--
-- Earlier biochemical prior art remains explicit: BH4 cofactor biology,
-- GCH1/redox control, NOS coupling/uncoupling, aromatic amino-acid
-- hydroxylases, AGMO/ether-lipid biology, E/I hypotheses, allostasis and
-- cellular stress-response biology all predate the candidate synthesis.
------------------------------------------------------------------------

data ScientificSupport : Set where
  backgroundPriorArt : ScientificSupport
  compatible : ScientificSupport
  structuralConvergence : ScientificSupport
  boundedMechanisticSupport : ScientificSupport
  directInterventionSupport : ScientificSupport
  reviewLevelSupport : ScientificSupport
  policyFrameworkConvergence : ScientificSupport
  unresolvedScientificRelation : ScientificSupport

data PriorityStatus : Set where
  priorArtBeforeKitzerow : PriorityStatus
  publicDisclosure2023 : PriorityStatus
  formalPreprint2024 : PriorityStatus
  laterThanKitzerowDisclosure : PriorityStatus
  chronologyUnresolved : PriorityStatus

data ContactStatus : Set where
  noContactEvidenceAcquired : ContactStatus
  explicitContactClaim : ContactStatus
  verifiedPrimaryContact : ContactStatus
  institutionalComplaintAfterPublication : ContactStatus
  contactChronologyUnresolved : ContactStatus

data AttributionStatus : Set where
  independentConvergence : AttributionStatus
  attributionConcern : AttributionStatus
  attributionInvestigationReported : AttributionStatus
  noAttributionBreachEstablished : AttributionStatus
  attributionStatusUnresolved : AttributionStatus

data EvidenceScale : Set where
  molecular : EvidenceScale
  cellular : EvidenceScale
  circuit : EvidenceScale
  systems : EvidenceScale
  clinical : EvidenceScale
  policy : EvidenceScale

data EvidenceDesign : Set where
  primaryExperiment : EvidenceDesign
  interventionExperiment : EvidenceDesign
  transcriptomicClassification : EvidenceDesign
  connectivityClassification : EvidenceDesign
  systematicReview : EvidenceDesign
  narrativeSystemsModel : EvidenceDesign
  institutionalFramework : EvidenceDesign

data RelationTarget : Set where
  bh4Availability : RelationTarget
  gch1RedoxRegulation : RelationTarget
  aaaHBranch : RelationTarget
  nosUncoupling : RelationTarget
  noTsc2Mtor : RelationTarget
  synapticProteinRegulation : RelationTarget
  excitatoryInhibitoryCircuitState : RelationTarget
  reticularThalamusCircuit : RelationTarget
  connectivitySubtype : RelationTarget
  cellStressTranslationState : RelationTarget
  neuroimmuneCascade : RelationTarget
  developmentalStressSequence : RelationTarget
  wholeCascade : RelationTarget

record EvidenceReceipt : Set where
  constructor evidenceReceipt
  field
    receiptId : String
    sourceLabel : String
    sourceDate : String
    sourceLocator : String
    design : EvidenceDesign
    scale : EvidenceScale
    target : RelationTarget
    scientificSupport : ScientificSupport
    priorityStatus : PriorityStatus
    contactStatus : ContactStatus
    attributionStatus : AttributionStatus
    boundedReading : String
    exclusion : String
    wholeModelConfirmed : Bool
    wholeModelConfirmedIsFalse : wholeModelConfirmed ≡ false

open EvidenceReceipt public

mkReceipt :
  String → String → String → String →
  EvidenceDesign → EvidenceScale → RelationTarget →
  ScientificSupport → PriorityStatus → ContactStatus → AttributionStatus →
  String → String → EvidenceReceipt
mkReceipt rid source date locator design scale target support priority contact attribution reading exclusion =
  evidenceReceipt rid source date locator design scale target support priority contact attribution reading exclusion false refl

------------------------------------------------------------------------
-- Acquired later studies / framework sources.
------------------------------------------------------------------------

ojhaNOToTSC2ToMTOR : EvidenceReceipt
ojhaNOToTSC2ToMTOR =
  mkReceipt
    "KIT-E1"
    "Ojha et al. — Nitric oxide-mediated S-nitrosylation of TSC2 drives mTOR dysregulation across autism models"
    "2026"
    "Molecular Psychiatry; primary paper acquired from Nature/Springer record"
    interventionExperiment molecular noTsc2Mtor
    directInterventionSupport laterThanKitzerowDisclosure noContactEvidenceAcquired independentConvergence
    "Pays a strong NO -> TSC2 S-nitrosylation/degradation -> mTOR dysregulation edge in autism models, including intervention structure."
    "Does not by itself identify a BH4 shunt as the upstream cause of the NO state and does not confirm the complete Kitzerow cascade."

stanfordReticularThalamus : EvidenceReceipt
stanfordReticularThalamus =
  mkReceipt
    "KIT-E2"
    "Jang, Takahashi & Huguenard — reticular thalamic hyperexcitability intervention in Cntnap2 autism model"
    "2025"
    "Science Advances / PMC"
    interventionExperiment circuit reticularThalamusCircuit
    directInterventionSupport laterThanKitzerowDisclosure explicitContactClaim attributionConcern
    "Supports a causal circuit-level E/I relation: reducing reticular-thalamic hyperexcitability improves measured behavioral/seizure outcomes in the model. Kitzerow's public timeline separately claims Stanford Neurodiversity Project outreach on 2023-11-27 requesting information on her framework."
    "The acquired public timeline is secondary/self-published evidence for the outreach unless the underlying email is independently inspected; contact by one Stanford-affiliated group does not establish access, derivation, or misconduct by the later paper authors."

italyConnectivitySubtypes : EvidenceReceipt
italyConnectivitySubtypes =
  mkReceipt
    "KIT-E3"
    "2026 Nature Neuroscience connectivity-subtype study across autism genetic mouse models and human data"
    "2026"
    "Nature Neuroscience"
    connectivityClassification circuit connectivitySubtype
    structuralConvergence laterThanKitzerowDisclosure noContactEvidenceAcquired independentConvergence
    "Supports context- and genotype-dependent hypo/hyper-connectivity subtypes and heterogeneous pathway signatures."
    "Does not uniquely identify BH4, E/I balance, or a single upstream shunt as the cause of those states."

japanCellularStress : EvidenceReceipt
japanCellularStress =
  mkReceipt
    "KIT-E4"
    "Nomura et al. — autism-linked CNV neural-cell translational / stress vulnerability study"
    "2025"
    "Cell Genomics"
    primaryExperiment cellular cellStressTranslationState
    structuralConvergence laterThanKitzerowDisclosure noContactEvidenceAcquired independentConvergence
    "Supports convergent cell-type-specific regulatory/translation vulnerability across multiple autism-linked genetic perturbations."
    "The stronger wording 'every mutation converged on the same cellular stress response' requires an adapter beyond the bounded measured translation/NMD result."

brazilBH4Review : EvidenceReceipt
brazilBH4Review =
  mkReceipt
    "KIT-E5"
    "Colpani Filho et al. — Tetrahydrobiopterin and Autism Spectrum Disorder: A Systematic Review of a Promising Therapeutic Pathway"
    "2025"
    "Brain Sciences 15(2):151; DOI 10.3390/brainsci15020151"
    systematicReview systems bh4Availability
    reviewLevelSupport laterThanKitzerowDisclosure noContactEvidenceAcquired attributionConcern
    "Synthesizes older evidence that BH4 metabolism, neopterin/NO measures and BH4-related intervention literature are relevant to ASD."
    "Its underlying search window substantially predates Kitzerow's formal model; it cannot be treated as a prospective experimental test of the complete 2023-24 architecture. Similarity/priority concerns require separate provenance evidence."

naviauxThreeHit : EvidenceReceipt
naviauxThreeHit =
  mkReceipt
    "KIT-E6"
    "Naviaux — A 3-hit metabolic signaling model for the core symptoms of autism spectrum disorder"
    "2025"
    "Autism Research / Wiley"
    narrativeSystemsModel systems developmentalStressSequence
    structuralConvergence laterThanKitzerowDisclosure noContactEvidenceAcquired attributionConcern
    "Shows substantial structural overlap around susceptibility, stress/cell-danger response, persistence, developmental timing, multisystem metabolic signaling and plasticity."
    "It is itself a systems model and descends from Naviaux's much earlier cell-danger-response program; overlap is not by itself evidence of copying."

melilloNeuroimmuneCascade : EvidenceReceipt
melilloNeuroimmuneCascade =
  mkReceipt
    "KIT-E7"
    "Leisman, Melillo & Alfasi — developmental neuroimmune cascade model of autism spectrum disorder"
    "2026"
    "International Journal of Molecular Sciences / PubMed"
    narrativeSystemsModel systems neuroimmuneCascade
    structuralConvergence laterThanKitzerowDisclosure noContactEvidenceAcquired attributionConcern
    "Converges on an ordered susceptibility -> immune/glial/barrier -> pruning/E-I/connectivity -> trait cascade."
    "A review/model paper does not experimentally establish that the Kitzerow BH4 shunt is the unique upstream driver."

iaccDevelopmentalSystems : EvidenceReceipt
iaccDevelopmentalSystems =
  mkReceipt
    "KIT-E8"
    "IACC developmental-systems strategic-plan material"
    "2026"
    "US Interagency Autism Coordinating Committee"
    institutionalFramework policy developmentalStressSequence
    policyFrameworkConvergence laterThanKitzerowDisclosure noContactEvidenceAcquired attributionStatusUnresolved
    "Institutional convergence toward developmental timing, interacting biological systems and multisystem dysregulation is relevant context for the architecture."
    "Policy/research-priority structure is not a biological experiment and cannot confirm the causal graph."

------------------------------------------------------------------------
-- Earlier prior-art anchors deliberately prevent novelty overclaim.
------------------------------------------------------------------------

bh4CytoprotectionPriorArt : EvidenceReceipt
bh4CytoprotectionPriorArt =
  mkReceipt
    "KIT-P1"
    "Eichwald et al. — Tetrahydrobiopterin: Beyond Its Traditional Role as a Cofactor"
    "2023"
    "Antioxidants 12(5):1037; DOI 10.3390/antiox12051037"
    systematicReview systems bh4Availability
    backgroundPriorArt priorArtBeforeKitzerow noContactEvidenceAcquired independentConvergence
    "Pre-Kitzerow review treats BH4 as a regulated cytoprotective/metabolic factor with roles in mitochondrial activity, oxidative stress and inflammation beyond canonical cofactor chemistry."
    "This prior art means broad claims that BH4 participates in stress/redox biology are not uniquely attributable to the later autism architecture."

record AtlasBoundary : Set where
  constructor atlasBoundary
  field
    nodeSupportConfirmsWholeGraph : Bool
    chronologyProvesAccess : Bool
    contactProvesDerivation : Bool
    contactProvesPlagiarism : Bool
    policyConvergenceIsMechanisticProof : Bool
    priorArtSubtractedBeforeNoveltyClaim : Bool

canonicalAtlasBoundary : AtlasBoundary
canonicalAtlasBoundary = atlasBoundary false false false false false true

allReceipts : List EvidenceReceipt
allReceipts =
  bh4CytoprotectionPriorArt
  ∷ brazilBH4Review
  ∷ japanCellularStress
  ∷ stanfordReticularThalamus
  ∷ naviauxThreeHit
  ∷ italyConnectivitySubtypes
  ∷ ojhaNOToTSC2ToMTOR
  ∷ melilloNeuroimmuneCascade
  ∷ iaccDevelopmentalSystems
  ∷ []
