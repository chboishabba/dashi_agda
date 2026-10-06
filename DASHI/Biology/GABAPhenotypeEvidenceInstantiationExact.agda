module DASHI.Biology.GABAPhenotypeEvidenceInstantiationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.GABAPhenotypeEvidenceExact as Evidence
import DASHI.Biology.GABAPhenotypeBridgeExact as Bridge
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EVIDENCE INSTANTIATION MAX-CUT
--
-- This module pays only source-bounded bridge obligations found in the
-- literature search.  It deliberately distinguishes:
--
--   * an observed synchrony/attachment association from an attachment
--     definition or classifier;
--   * a GABA/neuroimmune mechanistic literature bridge from diagnosis-level
--     causal sufficiency;
--   * heterogeneous ADHD GABA findings from a single scalar low-GABA law.
--
-- Every scientific row is an AttributedSource.  Citation imports neither proof
-- nor authority beyond the explicit relationship string.
------------------------------------------------------------------------

nguyen2024Source : Source.AttributedSource
nguyen2024Source =
  Source.mkDOISource
    "Trinh Nguyen; Melanie T Kungl; Stefanie Hoehl; Lars O White; Pascal Vrtička"
    "Visualizing the invisible tie: Linking parent-child neural synchrony to parents' and children's attachment representations"
    "Developmental Science 27(6):e13504"
    "2024"
    "10.1111/desc.13504"
    "https://doi.org/10.1111/desc.13504"
    Source.academicArticleSource
    "Pays a bounded association between fNIRS interpersonal neural synchrony during parent-child cooperation and measured attachment representations. Direction differed by parent/child subgroup and brain region; it does not define attachment security from synchrony."
    Source.publicAttribution

crowley2016Source : Source.AttributedSource
crowley2016Source =
  Source.mkDOISource
    "Tadhg Crowley; John F Cryan; Eric J Downer; Olivia F O'Leary"
    "Inhibiting neuroinflammation: The role and therapeutic potential of GABA in neuro-immune interactions"
    "Brain, Behavior, and Immunity 54:260-277"
    "2016"
    "10.1016/j.bbi.2016.02.001"
    "https://doi.org/10.1016/j.bbi.2016.02.001"
    Source.academicArticleSource
    "Review-level support for reciprocal interactions between GABAergic signalling and neuroinflammatory processes. It does not establish a diagnostic neuroinflammation state, a universal direction, or causal sufficiency for autism, ADHD, or PTSD."
    Source.publicAttribution

schur2016Source : Source.AttributedSource
schur2016Source =
  Source.mkDOISource
    "Remmelt R Schür; Luc W R Draisma; Jannie P Wijnen; Marco P Boks; Martijn G J C Koevoets; Marian Joëls; Dennis W Klomp; René S Kahn; Christiaan H Vinkers"
    "Brain GABA levels across psychiatric disorders: A systematic literature review and meta-analysis of (1) H-MRS studies"
    "Human Brain Mapping 37(9):3337-3352"
    "2016"
    "10.1002/hbm.23244"
    "https://doi.org/10.1002/hbm.23244"
    Source.academicArticleSource
    "Pays the reported meta-analytic result that ADHD did not show a significant overall brain-GABA difference from controls in the included H-MRS studies. It does not prove equality or exclude region-, age-, task-, or assay-specific effects."
    Source.publicAttribution

puts2020Source : Source.AttributedSource
puts2020Source =
  Source.mkDOISource
    "Nicolaas A Puts; Matthew Ryan; Georg Oeltzschner; Alena Horska; Richard A E Edden; E Mark Mahone"
    "Reduced striatal GABA in unmedicated children with ADHD at 7T"
    "Psychiatry Research: Neuroimaging 301:111082"
    "2020"
    "10.1016/j.pscychresns.2020.111082"
    "https://doi.org/10.1016/j.pscychresns.2020.111082"
    Source.academicArticleSource
    "Pays reduced striatal GABA/Cr in the studied unmedicated children with ADHD, while ACC, DLPFC, and premotor regions did not show the same group difference and behavioral manifestations were not significantly correlated with the measured metabolites."
    Source.publicAttribution

harris2021Source : Source.AttributedSource
harris2021Source =
  Source.mkDOISource
    "Ashley D Harris; Donald L Gilbert; Paul S Horn; Deana Crocetti; Kim M Cecil; Richard A E Edden; David A Huddleston; Stewart H Mostofsky; Nicolaas A J Puts"
    "Relationship between GABA levels and task-dependent cortical excitability in children with attention-deficit/hyperactivity disorder"
    "Clinical Neurophysiology 132(5):1163-1172"
    "2021"
    "10.1016/j.clinph.2021.01.023"
    "https://doi.org/10.1016/j.clinph.2021.01.023"
    Source.academicArticleSource
    "Pays a sensorimotor GABA+/TMS study in children with ADHD: GABA+ did not differ overall between diagnostic groups and did not correlate with ADHD clinical symptoms; task-dependent physiology remained more complex than a scalar inhibition law."
    Source.publicAttribution

cheng2026Source : Source.AttributedSource
cheng2026Source =
  Source.mkDOISource
    "Xue Cheng; Lingzhi Wang; Cong Diao; Yunhe Wang; Yuanyuan Xue"
    "The ratio of GABA/Glu as a biomarker in children with attention deficit hyperactivity disorder"
    "Physiology & Behavior 315:115445"
    "2026"
    "10.1016/j.physbeh.2026.115445"
    "https://doi.org/10.1016/j.physbeh.2026.115445"
    Source.academicArticleSource
    "Pays a serum, not brain-MRS, study in children with ADHD reporting higher serum GABA and GABA/Glu ratio and positive correlations with SNAP-IV symptom dimensions. The paper itself calls for independent validation before clinical application."
    Source.publicAttribution

canonicalInstantiationSources : List Source.AttributedSource
canonicalInstantiationSources =
  nguyen2024Source ∷
  crowley2016Source ∷
  schur2016Source ∷
  puts2020Source ∷
  harris2021Source ∷
  cheng2026Source ∷ []

canonicalInstantiationSourceAtlas : Source.AttributedSourceAtlas
canonicalInstantiationSourceAtlas =
  Source.mkSourceAtlas
    "GABA phenotype evidence-instantiation atlas"
    "DASHI.Biology.GABAPhenotypeEvidenceInstantiationExact"
    canonicalInstantiationSources
    "Claim-relative sources for synchrony/attachment, GABA/neuroimmune interaction, and heterogeneous ADHD GABA measurements. No citation creates theorem or diagnostic authority."

canonicalInstantiationSourceAtlasNonPromoting :
  Source.atlasCreatesAuthority canonicalInstantiationSourceAtlas ≡ false
canonicalInstantiationSourceAtlasNonPromoting = refl

------------------------------------------------------------------------
-- Synchrony <-> attachment: bounded association bridge.
------------------------------------------------------------------------

record SynchronyAttachmentAssociationReceipt : Set where
  constructor synchrony-attachment-association-receipt
  field
    source : Source.AttributedSource
    populationReference : String
    neuralMeasurementReference : String
    attachmentMeasurementReference : String
    associationReference : String
    subgroupAndRegionDependenceRetained : Bool
    subgroupAndRegionDependenceRetainedIsTrue :
      subgroupAndRegionDependenceRetained ≡ true
    definitionOrClassifierAuthority : Bool
    definitionOrClassifierAuthorityIsFalse :
      definitionOrClassifierAuthority ≡ false

open SynchronyAttachmentAssociationReceipt public

nguyen2024SynchronyAttachmentAssociation : SynchronyAttachmentAssociationReceipt
nguyen2024SynchronyAttachmentAssociation =
  synchrony-attachment-association-receipt
    nguyen2024Source
    "140 parents and their 5-6-year-old children in cooperative versus individual problem-solving"
    "fNIRS hyperscanning interpersonal neural synchrony in frontal and temporal regions"
    "Adult Attachment Interview for parents and story-completion attachment task for children"
    "Attachment representations were associated with interpersonal neural synchrony during cooperation; maternal insecurity and daughter security showed different regional directions."
    true refl
    false refl

nguyen2024SynchronyAttachmentBridge : Bridge.SynchronyAttachmentBridge
nguyen2024SynchronyAttachmentBridge =
  Bridge.synchrony-attachment-bridge
    (Bridge.promotion-validation
      nguyen2024Source
      "Validated only as a study-scoped synchrony/attachment association receipt; not a definitional or diagnostic promotion."
      true refl)
    "fNIRS interpersonal neural synchrony during parent-child cooperative problem-solving"
    "parent Adult Attachment Interview / child story-completion attachment representation measures"
    "Nguyen et al. 2024 subgroup- and region-dependent association model"

data SynchronyDefinesAttachmentPermission : Set where

synchronyAssociationDoesNotDefineAttachment :
  SynchronyDefinesAttachmentPermission → ⊥
synchronyAssociationDoesNotDefineAttachment ()

------------------------------------------------------------------------
-- GABA <-> neuroinflammation: mechanistic review bridge, not diagnostic cause.
------------------------------------------------------------------------

crowley2016NeuroimmuneEvidence : Evidence.RegionalGABAEvidence
crowley2016NeuroimmuneEvidence =
  Evidence.regionalGABAEvidence
    crowley2016Source
    Evidence.mixedOrMetaAnalyticPopulation
    Evidence.multipleOrMixedRegions
    Evidence.otherGABAMeasurement
    Evidence.noSingleTask
    Evidence.neuroinflammation
    Evidence.heterogeneousOrMixed
    Evidence.systematicReviewEvidence
    "Review-level reciprocal GABAergic/neuroimmune mechanism evidence. This row does not encode a diagnosis, a single direction of effect, an individual classifier, or causal sufficiency for a neurodevelopmental phenotype."

crowley2016NeuroimmuneBridge :
  Bridge.NeurochemicalInflammationBridge crowley2016NeuroimmuneEvidence
crowley2016NeuroimmuneBridge =
  Bridge.neurochemical-inflammation-bridge
    (Bridge.promotion-validation
      crowley2016Source
      "Validated as a review-level mechanistic bridge between GABAergic signalling and neuroinflammatory processes only."
      true refl)
    "glial/microglial inflammatory signalling, cytokine/chemokine responses, and immune-cell GABA receptor pathways reviewed across cited studies"
    "reciprocal neural-immune signalling; no single mediator is universalised by this adapter"
    "the review describes bidirectional interaction, so temporal direction is retained as mechanism-specific rather than collapsed to GABA -> inflammation"

data NeuroimmuneReviewIsDiagnosisCausalPermission : Set where

neuroimmuneReviewDoesNotPayDiagnosisCausation :
  NeuroimmuneReviewIsDiagnosisCausalPermission → ⊥
neuroimmuneReviewDoesNotPayDiagnosisCausation ()

------------------------------------------------------------------------
-- ADHD: heterogeneous measurement atlas.
------------------------------------------------------------------------

data ADHDMeasurementDomain : Set where
  brainMRS : ADHDMeasurementDomain
  regionSpecificBrainMRS : ADHDMeasurementDomain
  multimodalMRSTMS : ADHDMeasurementDomain
  peripheralSerum : ADHDMeasurementDomain

data ADHDDirectionFinding : Set where
  noSignificantOverallDifference : ADHDDirectionFinding
  lowerInSelectedRegion : ADHDDirectionFinding
  noGroupDifferenceInSelectedRegion : ADHDDirectionFinding
  higherPeripheralLevel : ADHDDirectionFinding

data ADHDSymptomRelationFinding : Set where
  noGeneralSymptomRelationPaid : ADHDSymptomRelationFinding
  noSignificantClinicalSymptomCorrelation : ADHDSymptomRelationFinding
  positiveSymptomCorrelation : ADHDSymptomRelationFinding

record ADHDGABAStudyReceipt : Set where
  constructor adhd-gaba-study-receipt
  field
    source : Source.AttributedSource
    domain : ADHDMeasurementDomain
    populationReference : String
    regionOrCompartmentReference : String
    assayReference : String
    directionFinding : ADHDDirectionFinding
    symptomRelationFinding : ADHDSymptomRelationFinding
    scopeBoundary : String

open ADHDGABAStudyReceipt public

schur2016ADHDMetaReceipt : ADHDGABAStudyReceipt
schur2016ADHDMetaReceipt =
  adhd-gaba-study-receipt
    schur2016Source
    brainMRS
    "ADHD subset within a seven-disorder H-MRS systematic review/meta-analysis"
    "brain H-MRS studies pooled across reported regions"
    "1H-MRS meta-analysis"
    noSignificantOverallDifference
    noGeneralSymptomRelationPaid
    "No significant pooled ADHD-control GABA difference is not evidence of exact equality and does not erase region-, age-, or assay-specific effects."

puts2020ADHDStriatalReceipt : ADHDGABAStudyReceipt
puts2020ADHDStriatalReceipt =
  adhd-gaba-study-receipt
    puts2020Source
    regionSpecificBrainMRS
    "50 unmedicated children aged 5-9 years, 26 ADHD and 24 controls"
    "striatum, with DLPFC, ACC, and premotor cortex also measured"
    "7T MRS with LCModel; reported GABA/Cr"
    lowerInSelectedRegion
    noSignificantClinicalSymptomCorrelation
    "Lower GABA/Cr was striatal in this cohort; the same group difference was not reported in ACC, DLPFC, or premotor cortex, and behavioral manifestations did not significantly correlate with metabolites."

harris2021ADHDSensorimotorReceipt : ADHDGABAStudyReceipt
harris2021ADHDSensorimotorReceipt =
  adhd-gaba-study-receipt
    harris2021Source
    multimodalMRSTMS
    "37 children with ADHD and 45 typically developing children aged 8-12 years across two sites"
    "left sensorimotor cortex"
    "GABA-edited MRS plus single/paired-pulse TMS during rest and GO/STOP task states"
    noGroupDifferenceInSelectedRegion
    noSignificantClinicalSymptomCorrelation
    "GABA+ did not differ overall between groups or correlate with ADHD clinical symptoms; neurophysiological relations varied with state and measure."

cheng2026ADHDSerumReceipt : ADHDGABAStudyReceipt
cheng2026ADHDSerumReceipt =
  adhd-gaba-study-receipt
    cheng2026Source
    peripheralSerum
    "145 children with ADHD and 120 healthy controls"
    "peripheral serum"
    "ultra-performance liquid chromatography-tandem mass spectrometry; serum GABA, glutamate, and GABA/Glu ratio"
    higherPeripheralLevel
    positiveSymptomCorrelation
    "Serum GABA is not a brain-MRS measurement. Higher serum GABA/GABA-Glu ratio and positive SNAP-IV correlations cannot be collapsed into a central regional GABA law; independent clinical validation was explicitly requested."

record ADHDEvidenceHeterogeneityAtlas : Set where
  constructor adhd-evidence-heterogeneity-atlas
  field
    pooledBrainMRS : ADHDGABAStudyReceipt
    selectedStriatalMRS : ADHDGABAStudyReceipt
    sensorimotorMRSTMS : ADHDGABAStudyReceipt
    serumMeasurement : ADHDGABAStudyReceipt
    regionDependenceRetained : Bool
    regionDependenceRetainedIsTrue : regionDependenceRetained ≡ true
    assayCompartmentDependenceRetained : Bool
    assayCompartmentDependenceRetainedIsTrue :
      assayCompartmentDependenceRetained ≡ true
    uniformLowGABADirectionAvailable : Bool
    uniformLowGABADirectionAvailableIsFalse :
      uniformLowGABADirectionAvailable ≡ false
    uniformInverseSeverityRelationAvailable : Bool
    uniformInverseSeverityRelationAvailableIsFalse :
      uniformInverseSeverityRelationAvailable ≡ false

canonicalADHDEvidenceHeterogeneityAtlas : ADHDEvidenceHeterogeneityAtlas
canonicalADHDEvidenceHeterogeneityAtlas =
  adhd-evidence-heterogeneity-atlas
    schur2016ADHDMetaReceipt
    puts2020ADHDStriatalReceipt
    harris2021ADHDSensorimotorReceipt
    cheng2026ADHDSerumReceipt
    true refl
    true refl
    false refl
    false refl

data ADHDGeneralLowGABAPermission : Set where
data ADHDHigherGABALowerSeverityPermission : Set where

a dhdEvidenceDoesNotPayGeneralLowGABA : ADHDGeneralLowGABAPermission → ⊥
a dhdEvidenceDoesNotPayGeneralLowGABA ()

a dhdEvidenceDoesNotPayInverseSeverityLaw :
  ADHDHigherGABALowerSeverityPermission → ⊥
a dhdEvidenceDoesNotPayInverseSeverityLaw ()

------------------------------------------------------------------------
-- Canonical boundary.
------------------------------------------------------------------------

record GABAEvidenceInstantiationBoundary : Set where
  constructor gaba-evidence-instantiation-boundary
  field
    synchronyAttachmentAssociationInstantiated : Bool
    synchronyAttachmentAssociationInstantiatedIsTrue :
      synchronyAttachmentAssociationInstantiated ≡ true
    synchronyDoesNotDefineAttachment : Bool
    synchronyDoesNotDefineAttachmentIsFalse :
      synchronyDoesNotDefineAttachment ≡ false
    neuroimmuneMechanisticBridgeInstantiated : Bool
    neuroimmuneMechanisticBridgeInstantiatedIsTrue :
      neuroimmuneMechanisticBridgeInstantiated ≡ true
    neuroimmuneReviewPaysDiagnosisCausation : Bool
    neuroimmuneReviewPaysDiagnosisCausationIsFalse :
      neuroimmuneReviewPaysDiagnosisCausation ≡ false
    adhdHeterogeneityAtlasInstantiated : Bool
    adhdHeterogeneityAtlasInstantiatedIsTrue :
      adhdHeterogeneityAtlasInstantiated ≡ true
    adhdGeneralLowGABAClaimPaid : Bool
    adhdGeneralLowGABAClaimPaidIsFalse :
      adhdGeneralLowGABAClaimPaid ≡ false
    adhdInverseSeverityLawPaid : Bool
    adhdInverseSeverityLawPaidIsFalse :
      adhdInverseSeverityLawPaid ≡ false

canonicalGABAEvidenceInstantiationBoundary : GABAEvidenceInstantiationBoundary
canonicalGABAEvidenceInstantiationBoundary =
  gaba-evidence-instantiation-boundary
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
