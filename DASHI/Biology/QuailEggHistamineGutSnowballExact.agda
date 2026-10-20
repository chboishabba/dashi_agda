module DASHI.Biology.QuailEggHistamineGutSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.HistamineCompartmentClearanceExact as Histamine
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Design

------------------------------------------------------------------------
-- QUAIL EGG / HISTAMINE / GUT SNOWBALL
------------------------------------------------------------------------

lianto2018Source : Source.AttributedSource
lianto2018Source = Source.mkDOISource
  "Priscilia Lianto; Fredrick O Ogutu; Yani Zhang; Feng He; Huilian Che"
  "Inhibitory effects of quail egg on mast cells degranulation by suppressing PAR2-mediated MAPK and NF-kB activation"
  "Food & Nutrition Research 62:1084" "2018"
  "10.29219/fnr.v62.1084" "https://doi.org/10.29219/fnr.v62.1084"
  Source.academicArticleSource
  "Pays mouse passive-cutaneous-anaphylaxis and HMC-1 cell evidence that quail egg, especially albumen under tested in-vitro conditions, reduced mast-cell degranulation mediators including histamine and tryptase. Does not pay human IBS treatment or oral bioavailability."
  Source.publicAttribution

ovomucoid2023Source : Source.AttributedSource
ovomucoid2023Source = Source.mkDOISource
  "Mengzhen Hao; Shuai Yang; Shiwen Han; Huilian Che"
  "The amino acids differences in epitopes may promote the different allergenicity of ovomucoid derived from hen eggs and quail eggs"
  "Food Science and Human Wellness 12(3):861-870" "2023"
  "10.1016/j.fshw.2022.09.028" "https://doi.org/10.1016/j.fshw.2022.09.028"
  Source.academicArticleSource
  "Pays recombinant quail-egg ovomucoid trypsin-inhibitory and RBL-2H3 degranulation-inhibition evidence. Recombinant-protein evidence is not whole-food, human-gut, or clinical-efficacy evidence."
  Source.publicAttribution

dePalma2022Source : Source.AttributedSource
dePalma2022Source = Source.mkDOISource
  "Giada De Palma et al."
  "Histamine production by the gut microbiota induces visceral hyperalgesia through histamine 4 receptor signaling in mice"
  "Science Translational Medicine 14(655):eabj1895" "2022"
  "10.1126/scitranslmed.abj1895" "https://doi.org/10.1126/scitranslmed.abj1895"
  Source.academicArticleSource
  "Pays a bounded microbiome-histamine IBS mechanism: high-histamine-producing IBS microbiota, Klebsiella aerogenes as a major producer in the studied cohorts, and H4-receptor-dependent visceral hypersensitivity/mast-cell accumulation in colonized mice."
  Source.publicAttribution

schnedl2021Source : Source.AttributedSource
schnedl2021Source = Source.mkDOISource
  "Wolfgang J Schnedl; Dietmar Enko"
  "Histamine Intolerance Originates in the Gut"
  "Nutrients 13(4):1262" "2021"
  "10.3390/nu13041262" "https://doi.org/10.3390/nu13041262"
  Source.academicArticleSource
  "Review-level support for intestinal DAO / histamine-intolerance framing while explicitly noting that serum DAO has not been established to correlate with gut DAO activity."
  Source.publicAttribution

wouters2016Source : Source.AttributedSource
wouters2016Source = Source.mkDOISource
  "Mira M Wouters et al."
  "Histamine Receptor H1-Mediated Sensitization of TRPV1 Mediates Visceral Hypersensitivity and Symptoms in Patients With Irritable Bowel Syndrome"
  "Gastroenterology 150(4):875-887.e9" "2016"
  "10.1053/j.gastro.2015.12.034" "https://doi.org/10.1053/j.gastro.2015.12.034"
  Source.academicArticleSource
  "Pays human-biopsy mechanistic evidence plus a randomized placebo-controlled ebastine trial supporting an H1/TRPV1 visceral-hypersensitivity pathway in the studied IBS cohort. Does not identify all IBS with histamine pathology."
  Source.publicAttribution

data EvidenceSurface : Set where
  inVitroMastCell : EvidenceSurface
  mouseAllergyModel : EvidenceSurface
  recombinantProteinCellModel : EvidenceSurface
  humanIBSBiopsyAndTrial : EvidenceSurface
  microbiomeHumanCohortPlusMouseTransfer : EvidenceSurface
  reviewLevelGutDAO : EvidenceSurface

record QuailEggMastCellEvidenceReceipt : Set where
  constructor quail-egg-mast-cell-evidence-receipt
  field source : Source.AttributedSource
        surfaces : List EvidenceSurface
        albumenHistamineReleaseSuppressed : Bool
        oralHumanIBSEfficacyPaid : Bool
        boundary : String

lianto2018QuailEggReceipt : QuailEggMastCellEvidenceReceipt
lianto2018QuailEggReceipt = quail-egg-mast-cell-evidence-receipt
  lianto2018Source (mouseAllergyModel ∷ inVitroMastCell ∷ []) true false
  "Quail-egg albumen mast-cell stabilization is bounded to tested mouse/cell systems; dose, digestion, absorption, allergenicity, human gut exposure and IBS endpoints remain unpaid."

record QuailOvomucoidEvidenceReceipt : Set where
  constructor quail-ovomucoid-evidence-receipt
  field source : Source.AttributedSource
        recombinantProteinEvidence : Bool
        trypsinInhibitionObserved : Bool
        cellDegranulationInhibitionObserved : Bool
        wholeFoodEquivalencePaid : Bool
        humanIBSEfficacyPaid : Bool

quailOvomucoid2023Receipt : QuailOvomucoidEvidenceReceipt
quailOvomucoid2023Receipt = quail-ovomucoid-evidence-receipt
  ovomucoid2023Source true true true false false

record IBSMicrobialHistamineReceipt : Set where
  constructor ibs-microbial-histamine-receipt
  field source : Source.AttributedSource
        microbialHDCSourceRetained : Bool
        humanCohortAssociationRetained : Bool
        mouseTransferMechanismRetained : Bool
        universalIBSCauseClaimed : Bool

dePalma2022IBSHistamineReceipt : IBSMicrobialHistamineReceipt
dePalma2022IBSHistamineReceipt = ibs-microbial-histamine-receipt
  dePalma2022Source true true true false

record GutHistamineCompartmentWeld : Set where
  constructor gut-histamine-compartment-weld
  field balanceCoordinates : Histamine.HistamineBalanceCoordinates
        intestinalCompartment : Histamine.HistamineCompartment
        centralCompartment : Histamine.HistamineCompartment
        microbialProductionDistinctFromMastCellRelease : Bool
        gutDAODistinctFromBrainHNMT : Bool
        bloodDoesNotEqualBrain : Bool

canonicalGutHistamineCompartmentWeld : GutHistamineCompartmentWeld
canonicalGutHistamineCompartmentWeld = gut-histamine-compartment-weld
  Histamine.canonicalHistamineBalanceCoordinates
  Histamine.intestinalEpitheliumCompartment
  Histamine.centralNervousSystemCompartment
  true true true

data SerumDAOEqualsGutDAOPermission : Set where
serumDAODoesNotEqualGutDAO : SerumDAOEqualsGutDAOPermission → ⊥
serumDAODoesNotEqualGutDAO ()

data QuailEggTreatsIBSPermission : Set where
quailEggEvidenceDoesNotPayIBSTreatment : QuailEggTreatsIBSPermission → ⊥
quailEggEvidenceDoesNotPayIBSTreatment ()

data RecombinantOvomucoidEqualsWholeFoodPermission : Set where
recombinantOvomucoidDoesNotEqualWholeFood : RecombinantOvomucoidEqualsWholeFoodPermission → ⊥
recombinantOvomucoidDoesNotEqualWholeFood ()

record QuailEggIBSExperimentRequirement : Set where
  constructor quail-egg-ibs-experiment-requirement
  field discoveryRoute : Snowball.DiscoveryRoute
        sourcePopulationSlot : Design.ExperimentalDesignSlot
        treatmentAssignmentSlot : Design.ExperimentalDesignSlot
        comparatorSlot : Design.ExperimentalDesignSlot
        endpointMeasurementSlot : Design.ExperimentalDesignSlot
        assaySlot : Design.ExperimentalDesignSlot
        mechanismIdentificationSlot : Design.ExperimentalDesignSlot
        practicalSignificanceSlot : Design.ExperimentalDesignSlot
        requirementReference : String

canonicalQuailEggIBSExperimentRequirement : QuailEggIBSExperimentRequirement
canonicalQuailEggIBSExperimentRequirement = quail-egg-ibs-experiment-requirement
  Snowball.experimentalDesign
  Design.sourcePopulationSlot Design.treatmentAssignmentSlot Design.comparatorSlot
  Design.endpointMeasurementSlot Design.assaySlot Design.mechanismIdentificationSlot
  Design.practicalSignificanceSlot
  "Human quail-egg/ovomucoid promotion requires an IBS population, controlled exposure/comparator, symptom and/or visceral-sensitivity endpoints, mast-cell/histamine/DAO mechanism assay, tolerability/allergy surveillance and practical-effect estimate. Cell or mouse degranulation does not discharge this design."

record HistamineSourceSeparation : Set where
  constructor histamine-source-separation
  field dietaryHistamine : String
        microbialHistamine : String
        mastCellHistamine : String
        clearanceDAO : String
        clearanceHNMT : String
        receptorSensitivity : String
        sourcesCollapsed : Bool

canonicalHistamineSourceSeparation : HistamineSourceSeparation
canonicalHistamineSourceSeparation = histamine-source-separation
  "food/luminal histamine input"
  "microbial HDC-dependent histamine production"
  "host mast-cell/basophil release"
  "intestinal/extracellular DAO route"
  "intracellular/CNS HNMT route"
  "H1/H4 and downstream sensory signalling such as TRPV1 where supported"
  false

record QuailEggHistamineGutBoundary : Set where
  constructor quail-egg-histamine-gut-boundary
  field quailMastCellEvidenceAcquired : Bool
        ovomucoidCellEvidenceAcquired : Bool
        ibsMicrobialHistamineEvidenceAcquired : Bool
        humanHistamineIBSMechanismAcquired : Bool
        serumDAOEqualsGutDAO : Bool
        quailEggClinicalIBSEfficacyEstablished : Bool
        recombinantProteinEqualsWholeFood : Bool
        compartmentSeparationRetained : Bool
        experimentBackpropSpecified : Bool

canonicalQuailEggHistamineGutBoundary : QuailEggHistamineGutBoundary
canonicalQuailEggHistamineGutBoundary = quail-egg-histamine-gut-boundary
  true true true true false false false true true
