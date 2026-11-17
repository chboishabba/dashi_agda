module DASHI.Biology.KitzerowBH4ConvergentEvidenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
import DASHI.Biology.KitzerowBH4SourceAtlasExact as Atlas

data StudyDesign : Set where
  systematicReview : StudyDesign
  observational : StudyDesign
  mechanisticIntervention : StudyDesign
  circuitIntervention : StudyDesign
  transcriptomicClassification : StudyDesign
  systemsModelReview : StudyDesign
  institutionalFramework : StudyDesign

data EvidenceRelation : Set where
  directTestsExactEdge : EvidenceRelation
  supportsBoundedEdge : EvidenceRelation
  supportsAdjacentProjection : EvidenceRelation
  structuralConvergence : EvidenceRelation
  qualifiesModel : EvidenceRelation
  underdeterminesModel : EvidenceRelation

record ConvergentEvidenceReceipt : Set where
  constructor convergentEvidenceReceipt
  field
    label : String
    source : Source.AttributedSource
    testedNode : Cascade.CascadeNode
    populationOrOrganism : String
    tissueOrRegion : String
    genotypeOrContext : String
    assay : String
    design : StudyDesign
    relation : EvidenceRelation
    exactKitzerowEdgeTested : Bool
    wholeModelConfirmed : Bool
    wholeModelConfirmedIsFalse : wholeModelConfirmed ≡ false
    reading : String

open ConvergentEvidenceReceipt public

bh4ASDReviewReceipt : ConvergentEvidenceReceipt
bh4ASDReviewReceipt =
  convergentEvidenceReceipt
    "BH4 ASD systematic review"
    Atlas.colpani2025ASDReview
    Cascade.gch1RedoxBH4Allocation
    "published ASD BH4 literature"
    "multiple peripheral/clinical biological sample contexts"
    "heterogeneous ASD cohorts and prior trials"
    "systematic review"
    systematicReview
    supportsAdjacentProjection
    false
    false refl
    "supports BH4-pathway relevance in ASD while leaving central resource-allocation causality unclosed"

noTSC2mTORReceipt : ConvergentEvidenceReceipt
noTSC2mTORReceipt =
  convergentEvidenceReceipt
    "NO S-nitrosylation -> TSC2 -> mTOR"
    Atlas.ojha2026NOTSC2MTOR
    Cascade.mTORPruning
    "Shank3 and Cntnap2 mouse models plus ASD clinical samples"
    "brain / molecular SNO-proteome context"
    "Shank3 delta4-22 and Cntnap2 knockout"
    "SNOTRAP, molecular intervention and rescue assays"
    mechanisticIntervention
    directTestsExactEdge
    true
    false refl
    "direct bounded mechanistic support for the NOS/redox-sensitive-protein/mTOR internal branch; upstream BH4 allocation remains unpaid"

reticularThalamusReceipt : ConvergentEvidenceReceipt
reticularThalamusReceipt =
  convergentEvidenceReceipt
    "reticular thalamic excitability intervention"
    Atlas.jang2025ReticularThalamus
    Cascade.eiCSTLCircuitry
    "Cntnap2 mouse model"
    "reticular thalamus / CSTL circuit"
    "Cntnap2 model"
    "electrophysiology plus targeted interventions"
    circuitIntervention
    supportsBoundedEdge
    true
    false refl
    "supports a causal circuit-level downstream E/I node; does not identify BH4 or AAAH as its upstream cause"

nomuraReceipt : ConvergentEvidenceReceipt
nomuraReceipt =
  convergentEvidenceReceipt
    "CNV translational-vulnerability convergence"
    Atlas.nomura2025CNV
    Cascade.redoxSensitiveProteinRegulation
    "ESC-derived neural models carrying autism-associated CNVs"
    "cell-type-specific neural differentiation"
    "multiple autism-associated CNVs"
    "translation / NMD and cell-state assays"
    transcriptomicClassification
    structuralConvergence
    false
    false refl
    "supports context-sensitive convergence on regulatory/translation vulnerability but not a BH4-specific causal identification"

record ExternalComparisonReceipt : Set where
  constructor externalComparisonReceipt
  field
    label : String
    sourceReference : String
    targetNode : Cascade.CascadeNode
    design : StudyDesign
    relation : EvidenceRelation
    wholeModelConfirmed : Bool
    wholeModelConfirmedIsFalse : wholeModelConfirmed ≡ false
    reading : String

open ExternalComparisonReceipt public

connectivitySubtypeReceipt : ExternalComparisonReceipt
connectivitySubtypeReceipt =
  externalComparisonReceipt
    "2026 connectivity subtype study"
    "Nature Neuroscience 2026 hypo/hyper-connectivity subtype study; full source identity retained in acquisition ledger"
    Cascade.eiCSTLCircuitry
    transcriptomicClassification
    structuralConvergence
    false refl
    "opposed connectivity states support heterogeneous state geometry; they do not uniquely identify BH4 allocation"

melilloReceipt : ExternalComparisonReceipt
melilloReceipt =
  externalComparisonReceipt
    "2026 neuroimmune cascade comparison"
    "Leisman / Melillo / Alfasi 2026 developmental neuroimmune cascade review/model"
    Cascade.autismComorbidityClustering
    systemsModelReview
    structuralConvergence
    false refl
    "ordered neuroimmune developmental-model convergence is a model-to-model comparison rather than experimental replication"

iaccReceipt : ExternalComparisonReceipt
iaccReceipt =
  externalComparisonReceipt
    "IACC developmental-systems comparison"
    "IACC July 2026 developmental systems material"
    Cascade.chronicAllostasis
    institutionalFramework
    structuralConvergence
    false refl
    "institutional conceptual convergence is not biological experimental confirmation"

canonicalEvidenceReceipts : List ConvergentEvidenceReceipt
canonicalEvidenceReceipts =
  bh4ASDReviewReceipt ∷ noTSC2mTORReceipt ∷ reticularThalamusReceipt ∷ nomuraReceipt ∷ []

allCanonicalEvidenceReceiptsRejectWholeModelConfirmation : Bool
allCanonicalEvidenceReceiptsRejectWholeModelConfirmation = true

allCanonicalEvidenceReceiptsRejectWholeModelConfirmationIsTrue :
  allCanonicalEvidenceReceiptsRejectWholeModelConfirmation ≡ true
allCanonicalEvidenceReceiptsRejectWholeModelConfirmationIsTrue = refl
