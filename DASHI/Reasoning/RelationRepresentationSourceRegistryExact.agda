module DASHI.Reasoning.RelationRepresentationSourceRegistryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED RELATION-REPRESENTATION / STEERING REGISTRY
--
-- Attribution rule:
--   * each source is credited only for the bounded empirical/mathematical role
--     stated below;
--   * none of the sources is credited with DASHI's factorisation, future-safe
--     quotient, realization-authority, capability, or governance theorems;
--   * an arXiv/DataCite DOI is recorded as such and is not silently promoted to
--     peer-reviewed publication status;
--   * the eigenslur web essay is retained as a source-facing conceptual object,
--     with no individual author asserted where the page does not provide one.
------------------------------------------------------------------------

data SourceKind : Set where
  peerReviewedConference arxivPreprint webEssay : SourceKind

data SourceRole : Set where
  relationDecoderPropertyStructure
  rotationalSemanticTransformation
  manifoldSteeringGeometry
  ordinalSimilarityMetric
  magnitudeAwareSimilarityMetric
  calibratedSimilarityMetric
  differentialEquivalenceCompression
  grokkingDynamicFailure
  eigenslurConceptualResidual
  : SourceRole

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    kind : SourceKind
    role : SourceRole
    boundedReading : String
    excludedPromotion : String

open SourceReference public

christEtAl2025 : SourceReference
christEtAl2025 =
  sourceReference
    "Miranda Anna Christ; Adrián Csiszárik; Gergely Becsó; Dániel Varga"
    "The Structure of Relation Decoding Linear Operators in Large Language Models"
    "Advances in Neural Information Processing Systems 38 (NeurIPS 2025), Spotlight"
    2025
    "DOI 10.52202/085713-1438; arXiv:2510.26543"
    peerReviewedConference
    relationDecoderPropertyStructure
    "Shows that collections of linear relation decoders can be compressed and that cross-evaluation exposes recurring coarse semantic properties with transfer mainly to semantically nearby relations."
    "Does not prove that a compressed relation decoder identifies a complete semantic relation, social meaning, ethical relation, or ontological essence."

freenorAlvarez2025 : SourceReference
freenorAlvarez2025 =
  sourceReference
    "Michael Freenor; Lauren Alvarez"
    "Steering Embedding Models with Geometric Rotation: Mapping Semantic Relationships Across Languages and Models"
    "arXiv preprint"
    2025
    "DOI 10.48550/arXiv.2510.09790"
    arxivPreprint
    rotationalSemanticTransformation
    "Introduces Rotor-Invariant Shift Estimation (RISE) and reports transferable rotational operations for discourse-level semantic transformations across languages and embedding models."
    "Does not prove that every semantic relation is rotational, that rotation is a universal ontology, or that a successful steering operator has normative authority."

wurgaftEtAl2026 : SourceReference
wurgaftEtAl2026 =
  sourceReference
    "Daniel Wurgaft; Can Rager; Matthew Kowal; Vasudev Shyam; Sheridan Feucht; Usha Bhalla; Tal Haklay; Eric Bigelow; Raphael Sarfati; Thomas McGrath; Owen Lewis; Jack Merullo; Noah Goodman; Thomas Fel; Atticus Geiger; Ekdeep Singh Lubana"
    "Manifold Steering Reveals the Shared Geometry of Neural Network Representation and Behavior"
    "arXiv preprint"
    2026
    "DOI 10.48550/arXiv.2605.05115"
    arxivPreprint
    manifoldSteeringGeometry
    "Reports that manifold-respecting activation paths produce behavior trajectories closer to the model's natural behavior geometry than flat linear steering, motivating geometry as an intervention coordinate rather than a privileged direction."
    "Does not prove that every learned representation is a smooth manifold, that a fitted activation manifold is a semantic ontology, or that geometric intervention establishes social or ethical realization."

ai2026 : SourceReference
ai2026 =
  sourceReference
    "Xinbo Ai"
    "Beyond Cosine Similarity"
    "arXiv preprint"
    2026
    "DOI 10.48550/arXiv.2602.05266"
    arxivPreprint
    ordinalSimilarityMetric
    "Derives recos, a dot-product normalization based on sorted components, and reports improved semantic textual similarity correlation across eleven embedding models relative to cosine similarity."
    "Does not establish recos as a universal semantic metric and does not turn metric agreement into consumer sufficiency, causal use, realization, or authority."

parupudi2025 : SourceReference
parupudi2025 =
  sourceReference
    "V. S. Raghu Parupudi"
    "Magnitude Matters: a Superior Class of Similarity Metrics for Holistic Semantic Understanding"
    "arXiv preprint"
    2025
    "DOI 10.48550/arXiv.2509.19323"
    arxivPreprint
    magnitudeAwareSimilarityMetric
    "Introduces Overlap Similarity (OS) and Hyperbolic Tangent Similarity (HTS), which retain magnitude as well as alignment, and reports gains on several holistic semantic tasks while the advantage is not uniform on fine compositional benchmarks."
    "Does not establish magnitude-aware similarity as universally superior, and does not turn a benchmark improvement into semantic realization, causal use, or normative authority."

tacheny2026 : SourceReference
tacheny2026 =
  sourceReference
    "Nicolas Tacheny"
    "Calibrated Similarity for Reliable Geometric Analysis of Embedding Spaces"
    "arXiv preprint"
    2026
    "DOI 10.48550/arXiv.2601.16907"
    arxivPreprint
    calibratedSimilarityMetric
    "Uses monotone isotonic calibration against human similarity judgments to improve absolute-score calibration while preserving rank-based structure, separating score interpretation from the underlying embedding geometry."
    "Does not change the underlying semantic representation by itself and does not make a calibrated similarity value an ontology, causal explanation, or authority claim."

dhimanEtAl2026 : SourceReference
dhimanEtAl2026 =
  sourceReference
    "Ravi Dhiman; Andrea Passarella; Mirco Tribastone; Lorenzo Valerio"
    "Neural Network Compression by Approximate Differential Equivalence"
    "arXiv preprint"
    2026
    "DOI 10.48550/arXiv.2606.01402"
    arxivPreprint
    differentialEquivalenceCompression
    "Compresses neural networks by aggregating neurons with approximately matching induced dynamics under approximate forward differential equivalence, rather than pruning solely by parameter magnitude."
    "Does not prove that functional-equivalence compression preserves every downstream consumer or that approximate differential equivalence is semantic identity."

prakashMartin2026 : SourceReference
prakashMartin2026 =
  sourceReference
    "Hari K Prakash; Charles H Martin"
    "Late-Stage Generalization Collapse in Grokking: Detecting anti-grokking with Weightwatcher"
    "arXiv preprint"
    2026
    "DOI 10.48550/arXiv.2602.02859"
    arxivPreprint
    grokkingDynamicFailure
    "Reports a late anti-grokking phase in which generalization collapses after previously successful generalization while training accuracy remains saturated, motivating checkpoint- and future-sensitive adequacy tests."
    "Does not prove a universal grokking phase law, does not identify spectral diagnostics with semantic mechanism, and does not make one successful checkpoint future-safe."

eigenslurDefined2026 : SourceReference
eigenslurDefined2026 =
  sourceReference
    "eigenslur.com editorial essay; individual author not asserted on the cited page"
    "Eigenslur, Defined"
    "eigenslur.com"
    2026
    "URL source; no DOI asserted"
    webEssay
    eigenslurConceptualResidual
    "Defines the eigenslur as the direction remaining after target subtraction and presents the first principal component of contempt as the more careful linear-algebra operationalization, while acknowledging that eigen- properly suggests an operator."
    "The essay's low-rank contempt / full-rank craft language is not treated as a proved theorem, and no context-free slur, ethical essence, or universal semantic operator is promoted."

relationRepresentationSources : List SourceReference
relationRepresentationSources =
  christEtAl2025
  ∷ freenorAlvarez2025
  ∷ wurgaftEtAl2026
  ∷ ai2026
  ∷ parupudi2025
  ∷ tacheny2026
  ∷ dhimanEtAl2026
  ∷ prakashMartin2026
  ∷ eigenslurDefined2026
  ∷ []

record RelationRepresentationAttributionBoundary : Set where
  constructor relationRepresentationAttributionBoundary
  field
    citedSourcesProveDASHIFactorisation : Bool
    citedSourcesProveDASHIFactorisationIsFalse :
      citedSourcesProveDASHIFactorisation ≡ false

    relationDecoderCompressionProvesRelationIdentity : Bool
    relationDecoderCompressionProvesRelationIdentityIsFalse :
      relationDecoderCompressionProvesRelationIdentity ≡ false

    rotationalTransferProvesUniversalSemanticRotation : Bool
    rotationalTransferProvesUniversalSemanticRotationIsFalse :
      rotationalTransferProvesUniversalSemanticRotation ≡ false

    manifoldSteeringProvesSemanticOntology : Bool
    manifoldSteeringProvesSemanticOntologyIsFalse :
      manifoldSteeringProvesSemanticOntology ≡ false

    similarityBenchmarkProvesConsumerSufficiency : Bool
    similarityBenchmarkProvesConsumerSufficiencyIsFalse :
      similarityBenchmarkProvesConsumerSufficiency ≡ false

    magnitudeAwareBenchmarkProvesUniversalMetric : Bool
    magnitudeAwareBenchmarkProvesUniversalMetricIsFalse :
      magnitudeAwareBenchmarkProvesUniversalMetric ≡ false

    calibratedScoreChangesUnderlyingSemanticGeometry : Bool
    calibratedScoreChangesUnderlyingSemanticGeometryIsFalse :
      calibratedScoreChangesUnderlyingSemanticGeometry ≡ false

    grokkingCheckpointSuccessProvesFutureSafety : Bool
    grokkingCheckpointSuccessProvesFutureSafetyIsFalse :
      grokkingCheckpointSuccessProvesFutureSafety ≡ false

    eigenslurEssayProvesLowRankContempt : Bool
    eigenslurEssayProvesLowRankContemptIsFalse :
      eigenslurEssayProvesLowRankContempt ≡ false

    eigenslurEssayProvesFullRankCraft : Bool
    eigenslurEssayProvesFullRankCraftIsFalse :
      eigenslurEssayProvesFullRankCraft ≡ false

    dashiRelationRepresentationFormalisationIsOriginalExtension : Bool
    dashiRelationRepresentationFormalisationIsOriginalExtensionIsTrue :
      dashiRelationRepresentationFormalisationIsOriginalExtension ≡ true

canonicalRelationRepresentationAttributionBoundary :
  RelationRepresentationAttributionBoundary
canonicalRelationRepresentationAttributionBoundary =
  relationRepresentationAttributionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
