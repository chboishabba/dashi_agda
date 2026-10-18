module DASHI.Governance.PoliticalGenealogySnowballParetoExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.RodneyUnderdevelopmentAttributedSourceExact as Rodney
import DASHI.Governance.IranMarxianIslamicTranslationExact as Iran

------------------------------------------------------------------------
-- POLITICAL GENEALOGY SNOWBALL / PARETO FRONTIER
--
-- Follows the repo-wide rule:
--   candidate discovery != corpus inclusion
--   Pareto priority != source authority
--   source mention of A + B != evidence of A x B
------------------------------------------------------------------------

data GenealogyResidual : Set where
  rodneyToIranDirectInfluenceResidual : GenealogyResidual
  shariatiToKhomeiniTransmissionResidual : GenealogyResidual
  thirdWorldismToMostazafinResidual : GenealogyResidual
  pflpIranGrammarComparisonResidual : GenealogyResidual
  irgcLetterHistoricalLineageResidual : GenealogyResidual
  zionismJudaismConflationResidual : GenealogyResidual

record ParetoCandidate : Set where
  constructor pareto-candidate
  field
    priority : Nat
    residual : GenealogyResidual
    sourceHint : String
    expectedFanOut : Nat
    exactPrimaryOrScholarlyReceiptRequired : Bool
    priorityCreatesTruth : Bool
    priorityCreatesAuthority : Bool
    discoveryCreatesGenealogy : Bool

open ParetoCandidate public

mkCandidate : Nat → GenealogyResidual → String → Nat → ParetoCandidate
mkCandidate p residual hint fanout =
  pareto-candidate p residual hint fanout true false false false

canonicalFrontier : List ParetoCandidate
canonicalFrontier =
  mkCandidate 0 shariatiToKhomeiniTransmissionResidual
    "primary Shariati/Khomeini texts plus scholarship tracing uptake rather than lexical similarity"
    5
  ∷ mkCandidate 1 thirdWorldismToMostazafinResidual
    "Iranian intellectual-history scholarship on Third Worldism, socialism and Quranic oppressed/oppressor translation"
    5
  ∷ mkCandidate 2 irgcLetterHistoricalLineageResidual
    "primary IRGC 2026 artifact + earlier Khomeini/Khamenei public texts using mostazafin/mostakberin or people-vs-rulers appeals"
    4
  ∷ mkCandidate 3 pflpIranGrammarComparisonResidual
    "PFLP primary programme/history + Iranian primary revolutionary texts; comparison only, no organisation-equivalence"
    4
  ∷ mkCandidate 4 rodneyToIranDirectInfluenceResidual
    "search only for documentary intellectual transmission; Rodney's conceptual relevance alone cannot establish influence"
    2
  ∷ mkCandidate 5 zionismJudaismConflationResidual
    "UN human-rights sources plus plural Jewish/Zionist/anti-Zionist primary positions; contextual speech analysis required"
    4
  ∷ []

data ParetoPriorityCreatesSourceAuthority : Set where
data CandidateDiscoveryCreatesCorpusAdmission : Set where
data SharedVocabularyCreatesHistoricalGenealogy : Set where

paretoPriorityDoesNotCreateSourceAuthority :
  ParetoPriorityCreatesSourceAuthority → ⊥
paretoPriorityDoesNotCreateSourceAuthority ()

candidateDiscoveryDoesNotCreateCorpusAdmission :
  CandidateDiscoveryCreatesCorpusAdmission → ⊥
candidateDiscoveryDoesNotCreateCorpusAdmission ()

sharedVocabularyDoesNotCreateHistoricalGenealogy :
  SharedVocabularyCreatesHistoricalGenealogy → ⊥
sharedVocabularyDoesNotCreateHistoricalGenealogy ()

rodneyReceipt : Snowball.SourceRoleSnowballReceipt Rodney.rodney1972
rodneyReceipt = Rodney.rodneySnowballReceipt

shariatiReceipt : Snowball.SourceRoleSnowballReceipt Iran.shariatiGlobalMarxism2026
shariatiReceipt = Iran.shariatiSnowball
