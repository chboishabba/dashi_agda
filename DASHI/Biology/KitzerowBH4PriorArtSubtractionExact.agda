module DASHI.Biology.KitzerowBH4PriorArtSubtractionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as Dependence
import DASHI.Biology.KitzerowPriorityAttributionExact as Attribution

record PriorArtPartition : Set where
  constructor priorArtPartition
  field
    comparisonLabel : String
    inheritedPriorBiology : String
    distinctiveKitzerowArrangement : String
    laterMeasuredEdge : String
    unresolvedCommonSourcePossibility : String
    inheritedPriorBiologyRetained : Bool
    inheritedPriorBiologyRetainedIsTrue : inheritedPriorBiologyRetained ≡ true
    structuralOverlapAloneEstablishesIndependence : Bool
    structuralOverlapAloneEstablishesIndependenceIsFalse :
      structuralOverlapAloneEstablishesIndependence ≡ false
    doubleCountsInheritedBiologyAsKitzerowPriority : Bool
    doubleCountsInheritedBiologyAsKitzerowPriorityIsFalse :
      doubleCountsInheritedBiologyAsKitzerowPriority ≡ false
    dependenceReading : Dependence.EvidenceRelation

open PriorArtPartition public

canonicalNomuraPriorArtPartition : PriorArtPartition
canonicalNomuraPriorArtPartition =
  priorArtPartition
    "Nomura translational vulnerability"
    "pre-existing CNV, translation, NMD and cellular-stress biology"
    "later Kitzerow systems synthesis connecting heterogeneous genetic inputs to an ordered stress/resource-allocation cascade"
    "cell-type-specific translational vulnerability across autism-associated CNV models"
    "bounded overlap may arise from shared prior biology, but reported 2022 preprint chronology supports independent derivation for this comparison"
    true refl
    false refl
    false refl
    Dependence.crossDatasetReplication

canonicalStanfordPriorArtPartition : PriorArtPartition
canonicalStanfordPriorArtPartition =
  priorArtPartition
    "Stanford reticular-thalamus intervention"
    "pre-existing E/I, thalamic and Cntnap2 circuit biology"
    "Kitzerow public CSTL/E-I placement inside the BH4/AAAH branch before the later paper"
    "causal contribution of reticular-thalamic hyperexcitability in the Cntnap2 model"
    "reported pre-publication contact means derivation remains a provenance question rather than an independence assumption"
    true refl
    false refl
    false refl
    Dependence.independenceUndetermined

canonicalBH4ReviewPriorArtPartition : PriorArtPartition
canonicalBH4ReviewPriorArtPartition =
  priorArtPartition
    "2025 BH4 ASD systematic review"
    "BH4 cofactor, cytoprotective, mitochondrial, oxidative-stress and inflammatory biology established before Kitzerow"
    "Kitzerow's autism/comorbidity systems architecture and BH4 allocation/shunt interpretation"
    "review-level synthesis of BH4 abnormalities/intervention literature in ASD"
    "shared pre-2024 BH4 literature is a substantial common source and must be subtracted before assessing distinctive overlap"
    true refl
    false refl
    false refl
    Dependence.independenceUndetermined

canonicalNOTSC2PriorArtPartition : PriorArtPartition
canonicalNOTSC2PriorArtPartition =
  priorArtPartition
    "NO/TSC2/mTOR 2026"
    "pre-existing NO, S-nitrosylation, TSC2 and mTOR biology"
    "Kitzerow's prior placement of NOS/redox-sensitive protein regulation and mTOR/pruning inside one BH4-centred cascade"
    "NO-mediated TSC2 S-nitrosylation/degradation causing mTOR dysregulation in Shank3/Cntnap2 models"
    "experiment pays an internal edge but not the upstream BH4 resource-allocation edge"
    true refl
    false refl
    false refl
    Dependence.crossDatasetReplication

record PriorArtSubtractionBoundary : Set where
  constructor priorArtSubtractionBoundary
  field
    unknownProvenancePromotesIndependence : Bool
    unknownProvenancePromotesIndependenceIsFalse :
      unknownProvenancePromotesIndependence ≡ false
    inheritedBiologyCountsAsDistinctivePrediction : Bool
    inheritedBiologyCountsAsDistinctivePredictionIsFalse :
      inheritedBiologyCountsAsDistinctivePrediction ≡ false

canonicalPriorArtSubtractionBoundary : PriorArtSubtractionBoundary
canonicalPriorArtSubtractionBoundary =
  priorArtSubtractionBoundary false refl false refl
