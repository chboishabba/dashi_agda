module DASHI.Biology.BraidedEmotionEvidenceProvenance where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionEvidenceRegistry as Evidence

data ClaimScope : Set where
  populationBoundScope taskBoundScope crossCulturalScope mechanisticCandidateScope phenomenologicalScope relationalHistoricalScope normativeGovernanceScope : ClaimScope

data EvidenceRelation : Set where
  supports qualifies conflictsWith underdetermines : EvidenceRelation

record EvidenceSource : Set where
  constructor mkEvidenceSource
  field
    citationKey population task : String
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
    theoremAuthorityClaimed clinicalAuthorityClaimed : Bool

barrett2017 : EvidenceSource
barrett2017 = mkEvidenceSource "Barrett2017TheoryConstructedEmotion" "theoretical synthesis" "constructionist synthesis and mechanistic proposal" 2017 mechanisticCandidateScope
elfenbeinAmbady2002 : EvidenceSource
elfenbeinAmbady2002 = mkEvidenceSource "ElfenbeinAmbady2002EmotionRecognitionMetaAnalysis" "cross-cultural recognition studies" "meta-analysis and in-group advantage" 2002 crossCulturalScope
gendron2015 : EvidenceSource
gendron2015 = mkEvidenceSource "Gendron2015CultureEmotionPerception" "culturally diverse adults" "emotion perception under conceptual and task constraints" 2015 crossCulturalScope
menonUddin2010 : EvidenceSource
menonUddin2010 = mkEvidenceSource "MenonUddin2010SalienceNetwork" "human neuroimaging studies" "network-level switching and salience synthesis" 2010 mechanisticCandidateScope
tugadeFredrickson2004 : EvidenceSource
tugadeFredrickson2004 = mkEvidenceSource "TugadeFredrickson2004EmotionalGranularity" "adult affect differentiation studies" "granularity and coping associations" 2004 populationBoundScope
kimmerer2013 : EvidenceSource
kimmerer2013 = mkEvidenceSource "Kimmerer2013BraidingSweetgrass" "authored relational and ethical context" "reciprocity responsibility and braided knowledge" 2013 normativeGovernanceScope

basicRegularitySupport : EvidenceReceipt
basicRegularitySupport = mkEvidenceReceipt "cross-cultural evidence supports recurrent structure" elfenbeinAmbady2002 Evidence.crossCulturalRegularityRow supports "above-chance recognition supports some recurrent structure" false false
basicUniversalityQualification : EvidenceReceipt
basicUniversalityQualification = mkEvidenceReceipt "cross-cultural evidence qualifies strong universal categories" gendron2015 Evidence.crossCulturalRegularityRow qualifies "task concept language and culture alter category boundaries" false false
constructionMechanismUnderdetermined : EvidenceReceipt
constructionMechanismUnderdetermined = mkEvidenceReceipt "construction evidence does not uniquely identify mechanism" barrett2017 Evidence.conceptAndLanguageRow underdetermines "conceptual modulation does not select one total neural theory" false false
neuralProxyQualification : EvidenceReceipt
neuralProxyQualification = mkEvidenceReceipt "network evidence qualifies region-localised decoding" menonUddin2010 Evidence.neuralProxyRow qualifies "distributed coordination blocks simple one-region inference" false false
granularitySupport : EvidenceReceipt
granularitySupport = mkEvidenceReceipt "granularity supports provisional differentiated labels" tugadeFredrickson2004 Evidence.affectLabellingRow supports "differentiated description can aid regulation without creating essences" false false
reciprocityNormativeReceipt : EvidenceReceipt
reciprocityNormativeReceipt = mkEvidenceReceipt "reciprocity grounds obligation-bearing governance" kimmerer2013 Evidence.reciprocalObligationRow supports "knowing responsibility and reciprocity inform governance rather than mechanism" false false

canonicalEvidenceReceipts : List EvidenceReceipt
canonicalEvidenceReceipts = basicRegularitySupport ∷ basicUniversalityQualification ∷ constructionMechanismUnderdetermined ∷ neuralProxyQualification ∷ granularitySupport ∷ reciprocityNormativeReceipt ∷ []

record DialecticalEvidenceBraid : Set where
  constructor mkDialecticalEvidenceBraid
  field
    receipts : List EvidenceReceipt
    supportingAndQualifyingReceiptsCoexist disagreementPreserved noGlobalWinnerInferred noClinicalPromotion : Bool

canonicalDialecticalEvidenceBraid : DialecticalEvidenceBraid
canonicalDialecticalEvidenceBraid = mkDialecticalEvidenceBraid canonicalEvidenceReceipts true true true true

canonicalReceiptsAreStructured : DialecticalEvidenceBraid.receipts canonicalDialecticalEvidenceBraid ≡ canonicalEvidenceReceipts
canonicalReceiptsAreStructured = refl
