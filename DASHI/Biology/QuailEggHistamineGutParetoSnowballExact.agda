module DASHI.Biology.QuailEggHistamineGutParetoSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.QuailEggHistamineGutSnowballExact as Gut
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball
import DASHI.Biology.GABANeuroAIContextParetoSnowballExact as Pareto

------------------------------------------------------------------------
-- QUAIL / GUT-HISTAMINE ACQUISITION FRONTIER
------------------------------------------------------------------------

yang2020PHSource : Source.AttributedSource
yang2020PHSource = Source.mkDOISource
  "Qin Yang; Ju Meng; Wei Zhang; Lu Liu; Laping He; Li Deng; Xuefeng Zeng; Chun Ye"
  "Effects of Amino Acid Decarboxylase Genes and pH on the Amine Formation of Enteric Bacteria From Chinese Traditional Fermented Fish (Suan Yu)"
  "Frontiers in Microbiology 11:1130" "2020"
  "10.3389/fmicb.2020.01130" "https://doi.org/10.3389/fmicb.2020.01130"
  Source.academicArticleSource
  "Pays strain- and medium-specific evidence that pH materially changes microbial biogenic-amine/histamine production. Fermented-fish culture conditions are not a human gut pH theorem."
  Source.publicAttribution

record PHHistamineReceipt : Set where
  constructor ph-histamine-receipt
  field source : Source.AttributedSource
        pHDependenceObserved : Bool
        strainSpecificityRetained : Bool
        humanGutTransferPaid : Bool
        boundary : String

microbialPHHistamineReceipt : PHHistamineReceipt
microbialPHHistamineReceipt = ph-histamine-receipt
  yang2020PHSource true true false
  "Microbial histamine production is pH-sensitive in the tested enteric strains/media; gut transfer requires local pH, substrate, strain abundance/expression and in-vivo validation."

data GutAcquisitionStatus : Set where
  paidBounded : GutAcquisitionStatus
  experimentRequired : GutAcquisitionStatus
  transportOrExposureRequired : GutAcquisitionStatus
  replicationRequired : GutAcquisitionStatus

data GutAuthorityCeiling : Set where
  sourceBound : GutAuthorityCeiling
  preclinicalOnly : GutAuthorityCeiling
  proposalOnly : GutAuthorityCeiling

record GutAcquisitionNode : Set where
  constructor gut-acquisition-node
  field label : String
        status : GutAcquisitionStatus
        route : Snowball.DiscoveryRoute
        ceiling : GutAuthorityCeiling
        paidReference : String
        residual : String

quailAlbumenNode : GutAcquisitionNode
quailAlbumenNode = gut-acquisition-node
  "quail egg albumen mast-cell degranulation"
  paidBounded Snowball.externalKnowledgeComparison preclinicalOnly
  "Lianto 2018 mouse PCA + HMC-1: reduced histamine/tryptase/degranulation under tested conditions"
  "human digestion/exposure, dose-response, IBS phenotype, safety/allergenicity and replicated clinical endpoint"

ovomucoidNode : GutAcquisitionNode
ovomucoidNode = gut-acquisition-node
  "quail ovomucoid molecular/cell mechanism"
  paidBounded Snowball.externalKnowledgeComparison preclinicalOnly
  "Hao 2023 recombinant ovomucoid: trypsin inhibition and RBL-2H3 degranulation inhibition"
  "same-object bridge from recombinant protein to digested food exposure and human intestinal target engagement"

ibsHistamineMechanismNode : GutAcquisitionNode
ibsHistamineMechanismNode = gut-acquisition-node
  "IBS histamine neuroimmune mechanism"
  paidBounded Snowball.externalKnowledgeComparison sourceBound
  "De Palma 2022 microbial histamine/H4/mast-cell/visceral-hypersensitivity plus Wouters 2016 H1/TRPV1 human biopsy/RCT evidence"
  "phenotype stratification: determine which IBS subgroups are histamine-driven and which source term dominates"

gutDAOCompartmentNode : GutAcquisitionNode
gutDAOCompartmentNode = gut-acquisition-node
  "intestinal DAO versus serum/central histamine compartments"
  transportOrExposureRequired Snowball.experimentalDesign proposalOnly
  "existing HistamineCompartmentClearanceExact plus Schnedl 2021 serum-DAO != gut-DAO boundary"
  "paired/local intestinal DAO activity with luminal/mucosal histamine, timing, diet, microbiome and symptom endpoints"

microbialPHNode : GutAcquisitionNode
microbialPHNode = gut-acquisition-node
  "microbial histamine pH dependence"
  paidBounded Snowball.externalKnowledgeComparison preclinicalOnly
  "Yang 2020 shows pH- and strain-dependent histamine production in cultured enteric bacteria"
  "measure gut-relevant local pH + substrate + hdc expression + strain-resolved histamine flux in vivo; do not transfer fermented-food optima directly"

quailIBSTrialNode : GutAcquisitionNode
quailIBSTrialNode = gut-acquisition-node
  "quail egg / ovomucoid IBS intervention"
  experimentRequired Snowball.experimentalDesign proposalOnly
  "preclinical anti-degranulation evidence plus independent human IBS histamine-mechanism evidence coexist but are not yet welded by intervention data"
  "controlled human IBS study with exposure/comparator, symptom/visceral endpoints, mast-cell/histamine/DAO assays and allergy/tolerability surveillance"

canonicalGutAcquisitionFrontier : List GutAcquisitionNode
canonicalGutAcquisitionFrontier =
  quailAlbumenNode ∷ ovomucoidNode ∷ ibsHistamineMechanismNode ∷
  gutDAOCompartmentNode ∷ microbialPHNode ∷ quailIBSTrialNode ∷ []

record QuailEggHistamineParetoBoundary : Set where
  constructor quail-egg-histamine-pareto-boundary
  field existingGlobalParetoOwner : Pareto.AcquisitionParetoBoundary
        frontier : List GutAcquisitionNode
        preclinicalDoesNotCreateClinicalEfficacy : Bool
        preclinicalDoesNotCreateClinicalEfficacyIsTrue : preclinicalDoesNotCreateClinicalEfficacy ≡ true
        pHStudyDoesNotCreateGutPHLaw : Bool
        pHStudyDoesNotCreateGutPHLawIsTrue : pHStudyDoesNotCreateGutPHLaw ≡ true
        compartmentAndSourceTermsRemainSeparate : Bool
        compartmentAndSourceTermsRemainSeparateIsTrue : compartmentAndSourceTermsRemainSeparate ≡ true
        nextPromotionRequiresNewData : Bool
        nextPromotionRequiresNewDataIsTrue : nextPromotionRequiresNewData ≡ true

canonicalQuailEggHistamineParetoBoundary : QuailEggHistamineParetoBoundary
canonicalQuailEggHistamineParetoBoundary = quail-egg-histamine-pareto-boundary
  Pareto.canonicalAcquisitionParetoBoundary canonicalGutAcquisitionFrontier
  true refl true refl true refl true refl
