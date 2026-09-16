module DASHI.Wikimedia.IbrahimCannabisWishartPublicReviewContextParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisWishartArticleCCDDiscrepancyParetoExact as Discrepancy
import DASHI.Wikimedia.IbrahimCannabisTerpeneCommercialSampleQuantitativeAssayExact as Assay
import DASHI.Wikimedia.IbrahimCannabisTerpenePubChemCIDAuthorityExact as Registry
import DASHI.Wikimedia.IbrahimCannabisTerpeneIdentityInteractionParetoExact as Interaction
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- PUBLIC-REVIEW CONTEXT FOR THE WISHART ARTICLE <-> CCD DISCREPANCY
--
-- Public reviews and large comparative studies support a broad contextual
-- proposition: cannabis composition values can depend on matrix, sampling,
-- extraction, analytical platform, calibration, lab practice, reporting
-- convention and product identity.  They do NOT identify which such factor,
-- if any, caused the exact Wishart article/CCD THCA discrepancy.
------------------------------------------------------------------------

data ContextRole : Set where
  analyticalMethodsReview
  standardisationReview
  labelAccuracySystematicReview
  commercialDiversityEmpirical
  entourageEvidenceReview
  currentAnalyticalFrameworkReview : ContextRole

record PublicContextSource : Set where
  constructor public-context-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    directLink : String
    role : ContextRole
    boundedReading : String
    excludedPromotion : String
open PublicContextSource public

micalizzi2021 : PublicContextSource
micalizzi2021 = public-context-source
  "Giuseppe Micalizzi; Federica Vento; Filippo Alibrando; Danilo Donnarumma; Paola Dugo; Luigi Mondello"
  "Cannabis Sativa L.: a comprehensive review on the analytical methodologies for cannabinoids and terpenes characterization"
  "Journal of Chromatography A 1637:461864" 2021
  "10.1016/j.chroma.2020.461864"
  "https://doi.org/10.1016/j.chroma.2020.461864"
  analyticalMethodsReview
  "Reviews GC/HPLC and extraction choices for cannabinoid/terpene analysis, including cannabinoid decarboxylation issues in GC and extraction effects on terpene content."
  "Does not resolve the exact Wishart article/CCD value lineage or prove that one specific analytical artifact occurred there."

deidda2022 : PublicContextSource
deidda2022 = public-context-source
  "Riccardo Deidda; Amandine Dispas; Charlotte De Bleye; Philippe Hubert; Eric Ziemons"
  "Critical review on recent trends in cannabinoid determination on cannabis herbal samples: From chromatographic to vibrational spectroscopic techniques"
  "Analytica Chimica Acta 1209:339184" 2022
  "10.1016/j.aca.2021.339184"
  "https://doi.org/10.1016/j.aca.2021.339184"
  standardisationReview
  "Finds no globally accepted reference method for cannabinoid determination and argues for standardisation across analytical approaches."
  "General lack of standardisation does not establish that the Wishart paper and CCD used different methods or that method choice explains their exact numerical difference."

oldfield2021 : PublicContextSource
oldfield2021 = public-context-source
  "Karen Oldfield; John Ryan; Marjan Doppen; Stacey Kung; Irene Braithwaite; Giles Newton-Howes"
  "A systematic review of the label accuracy of cannabinoid-based products in regulated markets: is what's on the label what's in the product?"
  "Australasian Psychiatry 29(1)" 2021
  "10.1177/1039856220965334"
  "https://doi.org/10.1177/1039856220965334"
  labelAccuracySystematicReview
  "Systematic review found substantial heterogeneity in cannabinoid-product label accuracy across regulated-market studies."
  "Retail label inaccuracy is contextual evidence only; it does not identify a CCD ingestion or publication-transform defect."

smithVergaraKeeganJikomes2022 : PublicContextSource
smithVergaraKeeganJikomes2022 = public-context-source
  "Christiana J. Smith; Daniela Vergara; Brian Keegan; Nick Jikomes"
  "The phytochemical diversity of commercial Cannabis in the United States"
  "PLOS ONE 17(5):e0267498" 2022
  "10.1371/journal.pone.0267498"
  "https://doi.org/10.1371/journal.pone.0267498"
  commercialDiversityEmpirical
  "Large commercial dataset showed popular strain/category labels poorly align with phytochemical diversity and explicitly could not separate true regional variation from inter-laboratory methodological differences in some comparisons."
  "Cross-lab commercial variability does not resolve same-sample article-versus-database lineage for the Wishart study."

simei2024 : PublicContextSource
simei2024 = public-context-source
  "Joao Luis Q. Simei; Jose Diogo R. Souza; Joao Roberto Lisboa; Alline C. Campos; Francisco S. Guimaraes; Antonio Zuardi; Jose Alexandre S. Crippa"
  "Does the Entourage Effect in Cannabinoids Exist? A Narrative Scoping Review"
  "Cannabis and Cannabinoid Research 9(5):1202-1216" 2024
  "10.1089/can.2023.0052"
  "https://doi.org/10.1089/can.2023.0052"
  entourageEvidenceReview
  "Finds limited evidence that the entourage effect is stable, predictable, clinically effective or sufficiently established for premature promotion."
  "Entourage uncertainty does not resolve composition provenance and composition discrepancy does not prove or disprove entourage mechanisms."

andre2024 : PublicContextSource
andre2024 = public-context-source
  "Rebeca Andre; Ana Patricia Gomes; Catarina Pereira-Leite; Antonio Marques-da-Costa; Luis Monteiro Rodrigues; Michael Sassano; Patricia Rijo; Maria do Ceu Costa"
  "The Entourage Effect in Cannabis Medicinal Products: A Comprehensive Review"
  "Pharmaceuticals 17(11):1543" 2024
  "10.3390/ph17111543"
  "https://doi.org/10.3390/ph17111543"
  entourageEvidenceReview
  "Systematic review concludes terpene/cannabinoid synergistic or additive enhancement remains unproven and calls for further clinical trials."
  "Review-level uncertainty does not determine the source of the Wishart/CCD concentration mismatch."

shawkyEtAl2026 : PublicContextSource
shawkyEtAl2026 = public-context-source
  "Eman Shawky; Lutfun Nahar; Satyajit D. Sarker; Dina A. Selim"
  "Fit-for-purpose analytics for cannabis: identification, quantification, and standardization of cannabinoids, flavonoids and terpenes"
  "Critical Reviews in Analytical Chemistry, advance online publication" 2026
  "10.1080/10408347.2026.2714459"
  "https://doi.org/10.1080/10408347.2026.2714459"
  currentAnalyticalFrameworkReview
  "Reviews field-to-field and lab-to-lab variability, inconsistent analytical practice, matrix effects, calibration, method validation and traceability across cannabinoid and terpene measurements."
  "This broad framework supplies candidate discrepancy classes, not a same-object causal diagnosis."

------------------------------------------------------------------------
-- Candidate explanation classes supported as possibilities by the review
-- literature.  No class is promoted as the Wishart/CCD explanation without
-- exact source/version/method lineage.
------------------------------------------------------------------------

data DiscrepancyCandidate : Set where
  sourceVersionDifference
  sampleIdentityDifference
  extractionOrPreparationDifference
  analyticalPlatformDifference
  calibrationOrMatrixEffectDifference
  cannabinoidDefinitionDifference
  unitOrConversionDifference
  replicateAggregationDifference
  databaseIngestionOrTransformationDifference
  unresolvedCandidate : DiscrepancyCandidate

record CandidateContextReceipt : Set where
  constructor candidate-context-receipt
  field
    candidate : DiscrepancyCandidate
    publicContext : String
    exactWishartLineagePaid : Bool
    exactCCDTransformationPaid : Bool
    candidateExplainsObservedDifference : Bool
open CandidateContextReceipt public

methodCandidate : CandidateContextReceipt
methodCandidate = candidate-context-receipt
  analyticalPlatformDifference
  "Micalizzi 2021, Deidda 2022 and Shawky et al. 2026 document method/platform/validation variability as a real analytical concern."
  false false false

matrixCalibrationCandidate : CandidateContextReceipt
matrixCalibrationCandidate = candidate-context-receipt
  calibrationOrMatrixEffectDifference
  "Current analytical reviews identify calibration design, matrix effects, extraction and validation as important determinants of quantitative cannabis results."
  false false false

reportingCandidate : CandidateContextReceipt
reportingCandidate = candidate-context-receipt
  unitOrConversionDifference
  "Public cannabis literature contains multiple reporting surfaces such as mg/g, percent-by-weight, acid versus neutral cannabinoid species and total-cannabinoid conventions."
  false false false

ingestionCandidate : CandidateContextReceipt
ingestionCandidate = candidate-context-receipt
  databaseIngestionOrTransformationDifference
  "Wishart et al. explicitly state study data are listed in the Cannabis Compound Database, so database ingestion/transformation lineage is a live same-source candidate that still requires direct provenance."
  false false false

------------------------------------------------------------------------
-- Public reviews bound but do not explain the exact discrepancy.
------------------------------------------------------------------------

data ReviewContextCreatesExactDiagnosis : Set where
data LabelInaccuracyCreatesCCDIngestionError : Set where
data MethodVariabilityCreatesUnitConversionError : Set where
data EntourageReviewExplainsCompositionMismatch : Set where

data SameCitationCreatesSameVersion : Set where

reviewContextDoesNotCreateExactDiagnosis : ReviewContextCreatesExactDiagnosis → ⊥
reviewContextDoesNotCreateExactDiagnosis ()

labelInaccuracyDoesNotCreateCCDIngestionError : LabelInaccuracyCreatesCCDIngestionError → ⊥
labelInaccuracyDoesNotCreateCCDIngestionError ()

methodVariabilityDoesNotCreateUnitConversionError : MethodVariabilityCreatesUnitConversionError → ⊥
methodVariabilityDoesNotCreateUnitConversionError ()

entourageReviewDoesNotExplainCompositionMismatch : EntourageReviewExplainsCompositionMismatch → ⊥
entourageReviewDoesNotExplainCompositionMismatch ()

sameCitationDoesNotCreateSameVersion : SameCitationCreatesSameVersion → ⊥
sameCitationDoesNotCreateSameVersion ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data ReviewContextParetoTarget : Set where
  acquireSupportingTableS5
  inspectCCDConcentrationDetailLineage
  compareCompoundSemantics
  compareUnitsAndTransforms
  freezeSameObjectVector
  resumeExposureInteraction
  broadReviewSnowball : ReviewContextParetoTarget

record ReviewContextParetoStep : Set where
  constructor review-context-pareto-step
  field
    priority : Nat
    target : ReviewContextParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open ReviewContextParetoStep public

pareto0 : ReviewContextParetoStep
pareto0 = review-context-pareto-step
  0 acquireSupportingTableS5
  "acquire and inspect exact Table S5 cannabinoid rows from the Wishart supporting information"
  "publication-side per-sample cannabinoid vector"
  "none"

pareto1 : ReviewContextParetoStep
pareto1 = review-context-pareto-step
  1 inspectCCDConcentrationDetailLineage
  "inspect each CCD concentration-detail row, source metadata, version/update fields and any transformation/ingestion provenance"
  "database-side same-object lineage"
  "exact publication vector should be acquired in parallel"

pareto2 : ReviewContextParetoStep
pareto2 = review-context-pareto-step
  2 compareCompoundSemantics
  "check THCA versus THCA-A identity, acid/neutral species, total-THC conventions and stereochemical/registry identity"
  "semantic identity equivalence or defect"
  "requires source rows rather than prose summaries"

pareto3 : ReviewContextParetoStep
pareto3 = review-context-pareto-step
  3 compareUnitsAndTransforms
  "test mg/g, percent-weight, dilution, dry-weight, molecular-weight/decarboxylation and replicate-aggregation transforms explicitly"
  "candidate transformation discriminator"
  "must be fitted to exact source values"

pareto4 : ReviewContextParetoStep
pareto4 = review-context-pareto-step
  4 freezeSameObjectVector
  "freeze the reconciled or explicitly bifurcated cannabinoid vector with source/version provenance"
  "consumer-safe composition packet"
  "requires unresolved discrepancy to be explained or retained as bifurcation"

pareto9 : ReviewContextParetoStep
pareto9 = review-context-pareto-step
  9 resumeExposureInteraction
  "resume concentration-matched entourage/exposure reasoning only from the frozen composition packet"
  "downstream pharmacology admission"
  "dominated by source/data-lineage reconciliation"

pareto99 : ReviewContextParetoStep
pareto99 = review-context-pareto-step
  99 broadReviewSnowball
  "do not accumulate additional generic reviews unless they discriminate a live provenance hypothesis"
  "nothing by itself"
  "dominated by exact source/version acquisition"

------------------------------------------------------------------------
-- Temporal evidence: reviews published before and after Wishart remain context;
-- later review publication never rewrites the 2024 source objects.
------------------------------------------------------------------------

data ContextTime : Set where
  preWishartReviews
  wishartPublication2024
  currentCCDObservation
  currentReviewContext2026 : ContextTime

data ContextInterpretation : Set where
  variabilityKnownInField
  wishartArticleValueSurface
  ccdValueSurface
  exactDiscrepancyExplained : ContextInterpretation

data ContextSummary : Set where publicContextDoesNotResolveSameObject : ContextSummary

ContextCompatible : ContextTime → ContextInterpretation → Set
ContextCompatible preWishartReviews variabilityKnownInField = ⊤
ContextCompatible preWishartReviews wishartArticleValueSurface = ⊥
ContextCompatible preWishartReviews ccdValueSurface = ⊥
ContextCompatible preWishartReviews exactDiscrepancyExplained = ⊥
ContextCompatible wishartPublication2024 variabilityKnownInField = ⊤
ContextCompatible wishartPublication2024 wishartArticleValueSurface = ⊤
ContextCompatible wishartPublication2024 ccdValueSurface = ⊥
ContextCompatible wishartPublication2024 exactDiscrepancyExplained = ⊥
ContextCompatible currentCCDObservation variabilityKnownInField = ⊤
ContextCompatible currentCCDObservation wishartArticleValueSurface = ⊤
ContextCompatible currentCCDObservation ccdValueSurface = ⊤
ContextCompatible currentCCDObservation exactDiscrepancyExplained = ⊥
ContextCompatible currentReviewContext2026 variabilityKnownInField = ⊤
ContextCompatible currentReviewContext2026 wishartArticleValueSurface = ⊤
ContextCompatible currentReviewContext2026 ccdValueSurface = ⊤
ContextCompatible currentReviewContext2026 exactDiscrepancyExplained = ⊥

contextTemporalSystem : Temporal.TemporalEvidenceSystem
contextTemporalSystem = record
  { Time = ContextTime
  ; Interpretation = ContextInterpretation
  ; Compatible = ContextCompatible
  ; Summary = ContextSummary
  ; summarize = λ _ → publicContextDoesNotResolveSameObject
  ; timeReference = λ
      { preWishartReviews → "public analytical/label-accuracy review literature before the 2024 Wishart publication"
      ; wishartPublication2024 → "Wishart et al. 2024 DOI 10.1021/acs.jafc.3c06616"
      ; currentCCDObservation → "current Cannabis Compound Database THCA-A concentration surface attributed to Wishart et al."
      ; currentReviewContext2026 → "current public-review context through 2026"
      }
  }

currentDiscrepancyStillUnexplained : Temporal.EvidenceFibre contextTemporalSystem currentReviewContext2026
currentDiscrepancyStillUnexplained = Temporal.liveInterpretationAt ccdValueSurface tt

------------------------------------------------------------------------
-- Reused owners.
------------------------------------------------------------------------

discrepancyReference : String
discrepancyReference =
  "IbrahimCannabisWishartArticleCCDDiscrepancyParetoExact owns the exact article-versus-CCD observation; this module supplies only bounded public context."

assayReference : String
assayReference =
  "IbrahimCannabisTerpeneCommercialSampleQuantitativeAssayExact owns the six-sample terpene composition surface."

registryReference : String
registryReference =
  "IbrahimCannabisTerpenePubChemCIDAuthorityExact owns PubChem CID provenance; review context cannot replace molecule identity."

interactionReference : String
interactionReference =
  "IbrahimCannabisTerpeneIdentityInteractionParetoExact owns the composition-to-interaction frontier; review context does not pay exposure or clinical efficacy."

record PublicReviewContextBoundary : Set where
  constructor public-review-context-boundary
  field
    publicReviewsSupportVariabilityClasses : Bool
    reviewsResolveWishartCCDLineage : Bool
    sameObjectSourceAcquisitionStillRequired : Bool
    entourageClaimsRemainSeparate : Bool
    pubChemIdentityRemainsSeparate : Bool
open PublicReviewContextBoundary public

canonicalPublicReviewContextBoundary : PublicReviewContextBoundary
canonicalPublicReviewContextBoundary =
  public-review-context-boundary true false true true true
