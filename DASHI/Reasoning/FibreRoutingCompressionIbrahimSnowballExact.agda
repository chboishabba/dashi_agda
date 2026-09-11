module DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Reasoning.FibreRoutingCompressionLadderExact as Ladder

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL FOLLOW-THROUGH FOR COMPRESSION
--
-- The compression ladder is already consumer-indexed.  This owner adds the
-- external navigation/provenance layer without turning QID, Dewey or citation
-- adjacency into semantic adequacy.
--
-- data/model compression <-> machine learning <-> MDL <-> distillation /
-- pruning / quantization / low-rank <-> MoE / grokking <-> biological fibres.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim fibre-routing compression snowball"
  "verified external concept identity only"
  label
  Identity.wikidataQid
  (Identity.verified qid
    "identity checked 2026-09-11; QID does not create compression equivalence, consumer adequacy, mechanism identity, empirical result or source authority")

machineLearningQid : Identity.ExternalIdentityDemand
machineLearningQid = mkQid "machine learning" "Q2539"

dataCompressionQid : Identity.ExternalIdentityDemand
dataCompressionQid = mkQid "data compression" "Q2493"

minimumDescriptionLengthQid : Identity.ExternalIdentityDemand
minimumDescriptionLengthQid = mkQid "minimum description length" "Q1417790"

mixtureOfExpertsQid : Identity.ExternalIdentityDemand
mixtureOfExpertsQid = mkQid "mixture of experts" "Q30688561"

grokkingQid : Identity.ExternalIdentityDemand
grokkingQid = mkQid "grokking (machine learning)" "Q126362531"

quantizationQid : Identity.ExternalIdentityDemand
quantizationQid = mkQid "quantization (generic mathematical/signal concept)" "Q198099"

knowledgeDistillationQid : Identity.ExternalIdentityDemand
knowledgeDistillationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim fibre-routing compression snowball"
  "exact concept identity"
  "knowledge distillation"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact same-concept Wikidata item promoted in this pass; paper items and nearby compression concepts do not substitute")

neuralPruningQid : Identity.ExternalIdentityDemand
neuralPruningQid = Identity.mkOptionalIdentityDemand
  "Ibrahim fibre-routing compression snowball"
  "exact concept identity"
  "neural-network pruning"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact same-concept QID promoted; a specific pruning paper is not the pruning concept")

lowRankAdaptationQid : Identity.ExternalIdentityDemand
lowRankAdaptationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim fibre-routing compression snowball"
  "exact concept identity"
  "low-rank adaptation / LoRA"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact concept QID promoted; paper/work identities do not replace the method concept")

consumerAdequacyQid : Identity.ExternalIdentityDemand
consumerAdequacyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim fibre-routing compression snowball"
  "DASHI consumer-relative concept"
  "consumer-relative projection/compression adequacy"
  Identity.wikidataQid
  (Identity.notApplicable
    "repo-native typed consumer relation; no external ontology identity required")

------------------------------------------------------------------------
-- Dewey navigation.  Only explicitly inspected DDC values are admitted.
------------------------------------------------------------------------

data CompressionDeweyResolution : Set where
  deweyVerified : String → String → CompressionDeweyResolution
  deweyUnresolved : String → CompressionDeweyResolution

record CompressionDeweyCoordinate : Set where
  constructor compression-dewey-coordinate
  field
    subjectLabel : String
    resolution : CompressionDeweyResolution
    classificationCreatesSemanticParent : Bool
    classificationCreatesAdequacy : Bool
open CompressionDeweyCoordinate public

machineLearningDewey : CompressionDeweyCoordinate
machineLearningDewey = compression-dewey-coordinate
  "machine learning"
  (deweyVerified "006.31" "Wikidata Q2539 DDC statement inspected 2026-09-11")
  false false

dataCompressionDewey : CompressionDeweyCoordinate
dataCompressionDewey = compression-dewey-coordinate
  "data compression"
  (deweyVerified "005.746" "Wikidata Q2493 DDC statement inspected 2026-09-11")
  false false

minimumDescriptionLengthDewey : CompressionDeweyCoordinate
minimumDescriptionLengthDewey = compression-dewey-coordinate
  "minimum description length"
  (deweyUnresolved "no exact DDC statement promoted in this pass")
  false false

mixtureOfExpertsDewey : CompressionDeweyCoordinate
mixtureOfExpertsDewey = compression-dewey-coordinate
  "mixture of experts"
  (deweyUnresolved "no exact DDC statement promoted in this pass")
  false false

grokkingDewey : CompressionDeweyCoordinate
grokkingDewey = compression-dewey-coordinate
  "grokking"
  (deweyUnresolved "no exact DDC statement promoted in this pass")
  false false

------------------------------------------------------------------------
-- Primary/source-bounded research lineage.
------------------------------------------------------------------------

rissanenMDLSource : Attribution.AttributedSource
rissanenMDLSource = Attribution.mkDOISource
  "Jorma Rissanen"
  "Modeling by shortest data description"
  "Automatica 14(5), 465-471"
  "1978"
  "10.1016/0005-1098(78)90005-5"
  "https://doi.org/10.1016/0005-1098(78)90005-5"
  Attribution.academicArticleSource
  "primary MDL/model-selection lineage; motivates description-length ranking but does not override DASHI consumer admissibility"
  Attribution.publicAttribution

jacobsMoESource : Attribution.AttributedSource
jacobsMoESource = Attribution.mkDOISource
  "Robert A. Jacobs; Michael I. Jordan; Steven J. Nowlan; Geoffrey E. Hinton"
  "Adaptive Mixtures of Local Experts"
  "Neural Computation 3(1), 79-87"
  "1991"
  "10.1162/neco.1991.3.1.79"
  "https://doi.org/10.1162/neco.1991.3.1.79"
  Attribution.academicArticleSource
  "primary mixture-of-local-experts source; establishes a historical MoE method family, not equivalence with every modern sparse MoE"
  Attribution.publicAttribution

hintonDistillationSource : Attribution.AttributedSource
hintonDistillationSource = Attribution.mkNoDOISource
  "Geoffrey Hinton; Oriol Vinyals; Jeff Dean"
  "Distilling the Knowledge in a Neural Network"
  "arXiv:1503.02531"
  "2015"
  "https://arxiv.org/abs/1503.02531"
  Attribution.academicArticleSource
  "primary knowledge-distillation research carrier; no DOI recorded in this atlas; teacher/student behavioural transfer does not imply mechanism identity"
  Attribution.publicAttribution

hanDeepCompressionSource : Attribution.AttributedSource
hanDeepCompressionSource = Attribution.mkNoDOISource
  "Song Han; Huizi Mao; William J. Dally"
  "Deep Compression: Compressing Deep Neural Networks with Pruning, Trained Quantization and Huffman Coding"
  "arXiv:1510.00149"
  "2015"
  "https://arxiv.org/abs/1510.00149"
  Attribution.academicArticleSource
  "primary combined pruning/quantization/compression pipeline; technique bundle does not identify every compression operation"
  Attribution.publicAttribution

shazeerSparseMoESource : Attribution.AttributedSource
shazeerSparseMoESource = Attribution.mkNoDOISource
  "Noam Shazeer; Azalia Mirhoseini; Krzysztof Maziarz; Andy Davis; Quoc V. Le; Geoffrey E. Hinton; Jeff Dean"
  "Outrageously Large Neural Networks: The Sparsely-Gated Mixture-of-Experts Layer"
  "ICLR 2017 / arXiv:1701.06538"
  "2017"
  "https://arxiv.org/abs/1701.06538"
  Attribution.academicArticleSource
  "primary sparse-gated MoE source; total parameter capacity and per-example active computation remain different cost axes"
  Attribution.publicAttribution

powerGrokkingSource : Attribution.AttributedSource
powerGrokkingSource = Attribution.mkNoDOISource
  "Alethea Power; Yuri Burda; Harri Edwards; Igor Babuschkin; Vedant Misra"
  "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets"
  "arXiv:2201.02177"
  "2022"
  "https://arxiv.org/abs/2201.02177"
  Attribution.academicArticleSource
  "primary grokking report; delayed generalization is an empirical phenomenon and does not itself prove representation compression"
  Attribution.publicAttribution

huLoRASource : Attribution.AttributedSource
huLoRASource = Attribution.mkNoDOISource
  "Edward J. Hu; Yelong Shen; Phillip Wallis; Zeyuan Allen-Zhu; Yuanzhi Li; Shean Wang; Lu Wang; Weizhu Chen"
  "LoRA: Low-Rank Adaptation of Large Language Models"
  "arXiv:2106.09685"
  "2021"
  "https://arxiv.org/abs/2106.09685"
  Attribution.academicArticleSource
  "primary low-rank adaptation source; parameter-efficient adaptation is distinct from pruning, quantization and exact model compression"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Technique taxonomy.  Adjacency in the Ibrahim graph is not identity.
------------------------------------------------------------------------

data CompressionTechniqueClass : Set where
  descriptionLengthSelection : CompressionTechniqueClass
  knowledgeDistillation : CompressionTechniqueClass
  weightPruning : CompressionTechniqueClass
  quantization : CompressionTechniqueClass
  lowRankFactorizationOrAdaptation : CompressionTechniqueClass
  conditionalExpertRouting : CompressionTechniqueClass
  localFibreRepair : CompressionTechniqueClass

data TechniqueCase : Set where
  sameCompressionUmbrellaDistillation sameCompressionUmbrellaQuantization : TechniqueCase

data CompressionUmbrella : Set where sameCompressionNeighbourhood : CompressionUmbrella

data TechniqueIdentity : Set where distillationTechnique quantizationTechnique : TechniqueIdentity

compressionUmbrella : TechniqueCase → CompressionUmbrella
compressionUmbrella _ = sameCompressionNeighbourhood

techniqueIdentity : TechniqueCase → TechniqueIdentity
techniqueIdentity sameCompressionUmbrellaDistillation = distillationTechnique
techniqueIdentity sameCompressionUmbrellaQuantization = quantizationTechnique

-- Finite direct nonfactorability witness: one broad compression label cannot
-- recover the concrete operation family.
compressionTechniqueDistinct :
  techniqueIdentity sameCompressionUmbrellaDistillation ≡
  techniqueIdentity sameCompressionUmbrellaQuantization → ⊥
compressionTechniqueDistinct ()

------------------------------------------------------------------------
-- Compression adequacy inherits the repo-native consumer-relative boundary.
------------------------------------------------------------------------

compressionLadderBoundary : Ladder.FibreCompressionLadderBoundary
compressionLadderBoundary = Ladder.canonicalFibreCompressionLadderBoundary

cheapestRawStageIsNotAutomaticallyAdequate : Bool
cheapestRawStageIsNotAutomaticallyAdequate =
  Ladder.FibreCompressionLadderBoundary.rawCostMayOverrideConsumerInadequacy
    Ladder.canonicalFibreCompressionLadderBoundary

consumerRecheckRequiredAfterEveryCompression : Bool
consumerRecheckRequiredAfterEveryCompression =
  Ladder.FibreCompressionLadderBoundary.everyCompressionStepNeedsConsumerRecheck
    Ladder.canonicalFibreCompressionLadderBoundary

------------------------------------------------------------------------
-- BIDI parent constraints exposed by the compression specimen.
------------------------------------------------------------------------

record CompressionReverseConstraint : Set where
  constructor compression-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open CompressionReverseConstraint public

informationConstraint : CompressionReverseConstraint
informationConstraint = compression-reverse-constraint
  "Information / compression / MDL"
  "description length, recoverable information, declared consumer, approximation margin and mechanism identity remain separate"
  false

machineLearningConstraint : CompressionReverseConstraint
machineLearningConstraint = compression-reverse-constraint
  "Machine learning / representation"
  "distillation, pruning, quantization, low-rank factorisation, conditional routing and local repair remain distinct transformations"
  false

moeConstraint : CompressionReverseConstraint
moeConstraint = compression-reverse-constraint
  "Mixture of experts"
  "total parameter carrier, active experts, routing policy, deployment cost and held-out consumer adequacy remain separate"
  false

grokkingConstraint : CompressionReverseConstraint
grokkingConstraint = compression-reverse-constraint
  "Grokking / generalization"
  "delayed generalization, emergent compressibility, representation sparsity and mechanism explanation remain separate empirical questions"
  false

biologyConstraint : CompressionReverseConstraint
biologyConstraint = compression-reverse-constraint
  "Biological fibre reduction"
  "anatomical/source carrier, soft overlapping domains, reduced fibre carrier, held-out scientific consumer and mechanistic realization remain separate"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data QidCreatesCompressionEquivalence : Set where
data DeweyCreatesSemanticDependency : Set where
data CitationCreatesAdequacy : Set where
data DistillationMeansMechanismIdentity : Set where
data GrokkingMeansCompression : Set where
data MoETotalParametersEqualActiveCost : Set where
data ShorterMeansAdequate : Set where
data GenericQuantizationQidMeansNeuralQuantizer : Set where

qidDoesNotCreateCompressionEquivalence : QidCreatesCompressionEquivalence → ⊥
qidDoesNotCreateCompressionEquivalence ()

deweyDoesNotCreateSemanticDependency : DeweyCreatesSemanticDependency → ⊥
deweyDoesNotCreateSemanticDependency ()

citationDoesNotCreateAdequacy : CitationCreatesAdequacy → ⊥
citationDoesNotCreateAdequacy ()

distillationDoesNotCreateMechanismIdentity : DistillationMeansMechanismIdentity → ⊥
distillationDoesNotCreateMechanismIdentity ()

grokkingDoesNotCreateCompressionTheorem : GrokkingMeansCompression → ⊥
grokkingDoesNotCreateCompressionTheorem ()

moeTotalParametersDoNotEqualActiveCost : MoETotalParametersEqualActiveCost → ⊥
moeTotalParametersDoNotEqualActiveCost ()

shorterDoesNotMeanAdequate : ShorterMeansAdequate → ⊥
shorterDoesNotMeanAdequate ()

genericQuantizationIdentityDoesNotSpecifyNeuralQuantizer : GenericQuantizationQidMeansNeuralQuantizer → ⊥
genericQuantizationIdentityDoesNotSpecifyNeuralQuantizer ()

record FibreCompressionIbrahimSnowballBoundary : Set where
  constructor fibre-compression-ibrahim-snowball-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedQidsRetainedExplicitly : Bool
    deweyAttachedOnlyWhenInspected : Bool
    doiAndCanonicalPrimarySourcesRetained : Bool
    noDoiPrimarySourcesRemainExplicit : Bool
    techniqueFamiliesRemainDistinct : Bool
    consumerAdequacyPrecedesCostRanking : Bool
    grokkingCompressionRelationRemainsHypothesis : Bool
    moeTotalAndActiveCapacityRemainDistinct : Bool
    biologicalCompressionRequiresHeldOutConsumer : Bool
    qidDeweyCitationDoNotCreateAdequacy : Bool
    presentAxisVocabularyClaimedComplete : Bool
open FibreCompressionIbrahimSnowballBoundary public

canonicalFibreCompressionIbrahimSnowballBoundary : FibreCompressionIbrahimSnowballBoundary
canonicalFibreCompressionIbrahimSnowballBoundary =
  fibre-compression-ibrahim-snowball-boundary
    true true true true true true true true true true true false
