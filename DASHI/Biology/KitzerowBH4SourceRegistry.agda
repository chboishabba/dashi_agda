module DASHI.Biology.KitzerowBH4SourceRegistry where

open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- SOURCE REGISTRY
--
-- Attribution-first registry for the acquired sources.  These entries are
-- deliberately textual and versionable: they preserve who/what/when/where and
-- the bounded role each source is allowed to play in the formal atlas.
------------------------------------------------------------------------

data SourceKind : Set where
  creatorPreprint : SourceKind
  creatorTimeline : SourceKind
  peerReviewedPrimary : SourceKind
  peerReviewedReview : SourceKind
  systemsModel : SourceKind
  institutionalFramework : SourceKind
  priorArtReview : SourceKind
  biologicalDatabase : SourceKind

record SourceRecord : Set where
  constructor sourceRecord
  field
    sourceId : String
    authorOrInstitution : String
    title : String
    date : String
    locator : String
    kind : SourceKind
    acquiredRole : String
    attributionNote : String

open SourceRecord public

kitzerow2024BH4 : SourceRecord
kitzerow2024BH4 = sourceRecord
  "SRC-KIT-2024-01"
  "Kimberly Kitzerow"
  "Autism & the Comorbidities Along the BH4 Pathway"
  "2024-01"
  "DOI 10.13140/RG.2.2.23124.37761/1"
  creatorPreprint
  "formal public BH4/autism/comorbidity synthesis"
  "Credit Kitzerow for the specific synthesis actually present in this source; do not attribute older component biology to this source."

kitzerow2024Allostatic : SourceRecord
kitzerow2024Allostatic = sourceRecord
  "SRC-KIT-2024-08"
  "Kimberly Kitzerow"
  "The BH4 Pathway as an Allostatic Mechanism in the Pathology of Autism and Systemic Comorbidities"
  "2024-08"
  "ResearchGate publication 383021907; revision-specific DOI metadata should be preserved when pinning a binary"
  creatorPreprint
  "explicit BH4-shunt / stress-induced resource-reallocation architecture"
  "Credit the proposed architecture and terminology to Kitzerow while preserving prior-art subtraction for BH4, NOS, AAAH, AGMO, allostasis and E/I biology."

kitzerow2025Neurodivergent : SourceRecord
kitzerow2025Neurodivergent = sourceRecord
  "SRC-KIT-2025-07"
  "Kimberly Kitzerow"
  "Neurodivergent Biochemistry and the Autism and the Comorbidities Theory"
  "2025-07"
  "DOI 10.13140/RG.2.2.30248.89606"
  creatorPreprint
  "later systems-level formalization"
  "Use for the 2025 state of the creator's model, not to backdate concepts absent from the 2023-24 record."

kitzerowTimeline : SourceRecord
kitzerowTimeline = sourceRecord
  "SRC-KIT-TIMELINE"
  "Kimberly's Educational Resources"
  "Kitzerow Documented Timeline: Framework Development and Source Record"
  "living public record; acquired 2026-10"
  "kimberlyedu.org/kitzerow-documented-timeline"
  creatorTimeline
  "chronology and claimed institutional-contact index"
  "Creator-maintained chronology is evidence of a public claim and links; stronger priority/contact assertions require inspection of the underlying timestamped source or correspondence."

eichwald2023BH4 : SourceRecord
eichwald2023BH4 = sourceRecord
  "SRC-PA-BH4-2023"
  "Eichwald et al."
  "Tetrahydrobiopterin: Beyond Its Traditional Role as a Cofactor"
  "2023"
  "Antioxidants 12(5):1037; DOI 10.3390/antiox12051037"
  priorArtReview
  "pre-Kitzerow BH4 stress/redox/cytoprotection prior-art anchor"
  "Subtracts broad BH4 stress/redox novelty from later priority claims."

colpani2025Review : SourceRecord
colpani2025Review = sourceRecord
  "SRC-BRAZIL-BH4-2025"
  "Colpani Filho et al."
  "Tetrahydrobiopterin and Autism Spectrum Disorder: A Systematic Review of a Promising Therapeutic Pathway"
  "2025"
  "Brain Sciences 15(2):151; DOI 10.3390/brainsci15020151"
  peerReviewedReview
  "BH4/autism evidence synthesis"
  "Review date is later than Kitzerow; much of its included evidence is older. Distinguish synthesis chronology from underlying-evidence chronology."

ojha2026 : SourceRecord
ojha2026 = sourceRecord
  "SRC-NO-TSC2-MTOR-2026"
  "Ojha et al."
  "Nitric oxide-mediated S-nitrosylation of TSC2 drives mTOR dysregulation across autism models"
  "2026"
  "Molecular Psychiatry / Nature record"
  peerReviewedPrimary
  "direct mechanistic NO -> TSC2 -> mTOR edge"
  "Attribute the measured mechanism to Ojha et al.; relation to Kitzerow is a separate comparison receipt."

stanford2025 : SourceRecord
stanford2025 = sourceRecord
  "SRC-STANFORD-RT-2025"
  "Jang, Takahashi & Huguenard"
  "reticular thalamic hyperexcitability intervention in Cntnap2 autism model"
  "2025"
  "Science Advances / PMC"
  peerReviewedPrimary
  "circuit-level causal intervention evidence"
  "Attribute the experiment and circuit result to its authors; any contact/priority concern remains a separate provenance coordinate."

nomura2025 : SourceRecord
nomura2025 = sourceRecord
  "SRC-JAPAN-2025"
  "Nomura et al."
  "autism-linked CNV neural-cell translation/regulatory vulnerability study"
  "2025"
  "Cell Genomics"
  peerReviewedPrimary
  "genetic perturbation -> cell-state convergence evidence"
  "Do not paraphrase the result as a universal BH4 stress response without an explicit adapter."

italy2026 : SourceRecord
italy2026 = sourceRecord
  "SRC-ITALY-CONNECTIVITY-2026"
  "2026 Nature Neuroscience study authors"
  "autism connectivity subtypes across genetic mouse models and human data"
  "2026"
  "Nature Neuroscience"
  peerReviewedPrimary
  "hypo/hyper-connectivity state evidence"
  "The measured subtype result belongs to the study authors; Kitzerow comparison is structural only unless a source demonstrates derivation."

naviaux2025 : SourceRecord
naviaux2025 = sourceRecord
  "SRC-NAVIAUX-2025"
  "Robert K. Naviaux"
  "A 3-hit metabolic signaling model for the core symptoms of autism spectrum disorder"
  "2025"
  "Autism Research / Wiley"
  systemsModel
  "later autism systems model with stress/developmental timing structure"
  "Preserve Naviaux's pre-existing cell-danger-response lineage when evaluating overlap."

melillo2026 : SourceRecord
melillo2026 = sourceRecord
  "SRC-MELILLO-2026"
  "Leisman, Melillo & Alfasi"
  "developmental neuroimmune cascade model of autism spectrum disorder"
  "2026"
  "International Journal of Molecular Sciences / PubMed"
  systemsModel
  "later neuroimmune cascade architecture"
  "Model convergence is not equivalent to experimental replication of BH4 centrality."

iacc2026 : SourceRecord
iacc2026 = sourceRecord
  "SRC-IACC-2026"
  "Interagency Autism Coordinating Committee"
  "developmental-systems strategic-plan material"
  "2026"
  "IACC"
  institutionalFramework
  "institutional research-priority convergence"
  "Policy framing is context, not a mechanistic proof token."

uniprot2026_03 : SourceRecord
uniprot2026_03 = sourceRecord
  "SRC-UNIPROT-2026-03"
  "UniProt Consortium"
  "UniProtKB release 2026_03 / REST protein knowledgebase"
  "2026_03; acquired 2026-10-17"
  "rest.uniprot.org; concrete response digest emitted by scripts/acquire_uniprot_bio_certificate.py"
  biologicalDatabase
  "versioned protein identity, sequence, annotation, evidence and cross-reference source for bounded biochemical nodes"
  "Credit UniProt for the curated database assertion and its contributors; preserve the cited primary literature as separate evidence owners. A reviewed UniProt entry is not itself direct experimental proof or whole-model confirmation."

rheaCurrent : SourceRecord
rheaCurrent = sourceRecord
  "SRC-RHEA-CURRENT"
  "Rhea / SIB Swiss Institute of Bioinformatics"
  "Rhea expert-curated biochemical reaction knowledgebase"
  "live service; acquired 2026-10-17"
  "rhea-db.org; UniProt P09417 links RHEA:17869"
  biologicalDatabase
  "chemically precise reaction identifier and reaction-level cross-database target"
  "Credit Rhea for reaction curation; a UniProt-to-Rhea cross-reference does not collapse protein identity with a reaction or establish disease-level causality."

allSources : List SourceRecord
allSources =
  kitzerow2024BH4
  ∷ kitzerow2024Allostatic
  ∷ kitzerow2025Neurodivergent
  ∷ kitzerowTimeline
  ∷ eichwald2023BH4
  ∷ colpani2025Review
  ∷ ojha2026
  ∷ stanford2025
  ∷ nomura2025
  ∷ italy2026
  ∷ naviaux2025
  ∷ melillo2026
  ∷ iacc2026
  ∷ uniprot2026_03
  ∷ rheaCurrent
  ∷ []
