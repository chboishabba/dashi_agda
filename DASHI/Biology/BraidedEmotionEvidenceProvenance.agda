module DASHI.Biology.BraidedEmotionEvidenceProvenance where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionEvidenceRegistry as Evidence

------------------------------------------------------------------------
-- Structured source identities, claim scopes, and dialectical relations.

data ClaimScope : Set where
  populationBoundScope : ClaimScope
  taskBoundScope : ClaimScope
  crossCulturalScope : ClaimScope
  mechanisticCandidateScope : ClaimScope
  phenomenologicalScope : ClaimScope
  relationalHistoricalScope : ClaimScope
  normativeGovernanceScope : ClaimScope

data EvidenceRelation : Set where
  supports : EvidenceRelation
  qualifies : EvidenceRelation
  conflictsWith : EvidenceRelation
  underdetermines : EvidenceRelation

record EvidenceSource : Set where
  constructor mkEvidenceSource
  field
    citationKey : String
    population : String
    task : String
    year : Nat
    claimScope : ClaimScope

record EvidenceReceipt : Set where
  constructor mkEvidenceReceipt
  field
    receiptLabel : String
    source : EvidenceSource
    evidenceRow : Evidence.EmotionEvidenceRow
    relation : EvidenceRelation
    relationReading : String
    theoremAuthorityClaimed : Bool
    clinicalAuthorityClaimed : Bool

barrett2017 : EvidenceSource
barrett2017 =
  mkEvidenceSource
    "Barrett2017TheoryConstructedEmotion"
    "theoretical synthesis across human affective neuroscience and psychology"
    "constructionist synthesis and mechanistic proposal"
    2017
    mechanisticCandidateScope

elfenbeinAmbady2002 : EvidenceSource
elfenbeinAmbady2002 =
  mkEvidenceSource
    "ElfenbeinAmbady2002EmotionRecognitionMetaAnalysis"
    "cross-cultural emotion-recognition studies"
    "meta-analysis of recognition accuracy and in-group advantage"
    2002
    crossCulturalScope

gendron2015 : EvidenceSource
gendron2015 =
  mkEvidenceSource
    "Gendron2015CultureEmotionPerception"
    "culturally diverse adult populations"
    "emotion perception under varying conceptual and task constraints"
    2015
    crossCulturalScope

menonUddin2010 : EvidenceSource
menonUddin2010 =
  mkEvidenceSource
    "MenonUddin2010SalienceNetwork"
    "human neuroimaging studies"
    "network-level switching and salience synthesis"
    2010
    mechanisticCandidateScope

tugadeFredrickson2004 : EvidenceSource
tugadeFredrickson2004 =
  mkEvidenceSource
    "TugadeFredrickson2004EmotionalGranularity"
    "adult participants in affect differentiation studies"
    "emotional granularity and coping associations"
    2004
    populationBoundScope

kimmerer2013 : EvidenceSource
kimmerer2013 =
  mkEvidenceSource
    "Kimmerer2013BraidingSweetgrass"
    "authored relational and ethical knowledge context"
    "reciprocity, responsibility, and braided knowledge"
    2013
    normativeGovernanceScope

basicRegularitySupport : EvidenceReceipt
basicRegularitySupport =
  mkEvidenceReceipt
    "cross-cultural evidence supports recurrent structure"
    elfenbeinAmbady2002
    Evidence.crossCulturalRegularityRow
    supports
    "recognition above chance in many paradigms supports some recurrent affective structure"
    false
    false

basicUniversalityQualification : EvidenceReceipt
basicUniversalityQualification =
  mkEvidenceReceipt
    "cross-cultural evidence qualifies strong universal categories"
    gendron2015
    Evidence.crossCulturalRegularityRow
    qualifies
    "task, concept, language, and culture alter category boundaries and recognition"
    false
    false

constructionMechanismUnderdetermined : EvidenceReceipt
constructionMechanismUnderdetermined =
  mkEvidenceReceipt
    "constructionist synthesis does not uniquely identify mechanism"
    barrett2017
    Evidence.conceptAndLanguageRow
    underdetermines
    "the evidence supports conceptual modulation but does not uniquely select one total neural theory"
    false
    false

neuralProxyQualification : EvidenceReceipt
neuralProxyQualification =
  mkEvidenceReceipt
    "network evidence qualifies region-localised emotion decoding"
    menonUddin2010
    Evidence.neuralProxyRow
    qualifies
    "distributed network coordination undermines simple one-region one-emotion inference"
    false
    false

granularitySupport : EvidenceReceipt
granularitySupport =
  mkEvidenceReceipt
    "granularity evidence supports provisional differentiated labels"
    tugadeFredrickson2004
    Evidence.affectLabellingRow
    supports
    "differentiated affect description can associate with adaptive regulation without making labels essences"
    false
    false

reciprocityNormativeReceipt : EvidenceReceipt
reciprocityNormativeReceipt =
  mkEvidenceReceipt
    "reciprocity grounds an obligation-bearing governance commitment"
    kimmerer2013
    Evidence.reciprocalObligationRow
    supports
    "the relation between knowing, responsibility, and reciprocity informs governance rather than empirical mechanism"
    false
    false

canonicalEvidenceReceipts : List EvidenceReceipt
canonicalEvidenceReceipts =
  basicRegularitySupport
  ∷ basicUniversalityQualification
  ∷ constructionMechanismUnderdetermined
  ∷ neuralProxyQualification
  ∷ granularitySupport
  ∷ reciprocityNormativeReceipt
  ∷ []

record DialecticalEvidenceBraid : Set where
  constructor mkDialecticalEvidenceBraid
  field
    receipts : List EvidenceReceipt
    supportingAndQualifyingReceiptsCoexist : Bool
    disagreementPreserved : Bool
    noGlobalWinnerInferred : Bool
    noClinicalPromotion : Bool

canonicalDialecticalEvidenceBraid : DialecticalEvidenceBraid
canonicalDialecticalEvidenceBraid =
  mkDialecticalEvidenceBraid
    canonicalEvidenceReceipts
    true
    true
    true
    true

canonicalReceiptsAreStructured :
  DialecticalEvidenceBraid.receipts canonicalDialecticalEvidenceBraid ≡ canonicalEvidenceReceipts
canonicalReceiptsAreStructured = refl
