module DASHI.Governance.IRGCMostazafinInstitutionalGrammarMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.HistoricalMechanismCompilerExact as Compiler
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IRGCOpenLetter2026PrimarySpanReceiptsExact as LetterSpans
import DASHI.Governance.IranianRevolutionaryGenealogyReviewedJoinExact as GenealogyJoins

------------------------------------------------------------------------
-- MOSTAZAFIN / ANTI-IMPERIAL INSTITUTIONAL-GRAMMAR CONTINUITY
--
-- Bounded claim:
--   historical scholarship supports a continuity of relational grammar from
--   Shariati's globalised mostazafin concept through Khomeini-era
--   institutionalisation of oppressed-vs-oppressor anti-imperial ideology.
--   The 2026 IRGC letter independently contains a people/common-oppressor/
--   shared-pain structure.
--
-- This does NOT prove textual borrowing, authorial intention, personal
-- transmission, or identity between Marxian class ontology and Islamic
-- revolutionary ontology.
------------------------------------------------------------------------

glombitza2026 : Source.AttributedSource
glombitza2026 = Source.mkDOISource
  "Olivia Glombitza"
  "Continuity and Change in the Islamic Republic's Vision of Regional Order: The Palestinian Cause in Iranian Foreign Policy"
  "Iranian Studies 59(2):388-395"
  "2026"
  "10.1017/irn.2025.10134"
  "https://www.cambridge.org/core/journals/iranian-studies/article/continuity-and-change-in-the-islamic-republics-vision-of-regional-order-the-palestinian-cause-in-iranian-foreign-policy/0CBFF61998C6010732B57A803DF3D9C9"
  Source.academicArticleSource
  "open-access historical analysis supporting socialism/nationalism/Third-Worldism in the revolutionary ideological field; Shariati's global anti-colonial/anti-imperialist use of mostazafin; and Khomeini-era institutionalisation of the oppressed-versus-oppressor framework"
  Source.publicAttribution

record InstitutionalGrammarMechanism : Set where
  constructor institutional-grammar-mechanism
  field
    mechanismRef : String
    historicalSource : Source.AttributedSource
    historicalJoinRef : String
    primaryLetterSpanRef : String
    relationPreserved : String
    ontologyPreserved : Bool
    ontologyPreservedIsFalse : ontologyPreserved ≡ false
    directTextualBorrowingEstablished : Bool
    directTextualBorrowingEstablishedIsFalse :
      directTextualBorrowingEstablished ≡ false
    personalInfluenceEstablished : Bool
    personalInfluenceEstablishedIsFalse :
      personalInfluenceEstablished ≡ false
    institutionalGrammarContinuitySupported : Bool
    institutionalGrammarContinuitySupportedIsTrue :
      institutionalGrammarContinuitySupported ≡ true

open InstitutionalGrammarMechanism public

canonicalMostazafinContinuity : InstitutionalGrammarMechanism
canonicalMostazafinContinuity =
  institutional-grammar-mechanism
    "mechanism:mostazafin-institutional-grammar-continuity"
    glombitza2026
    "reviewed joins: Marxian field -> Shariati; Iranian-left anti-neocolonial field -> Khomeini"
    "IRGC primary spans: people/state distinction + common-oppressor/shared-pain frame"
    "oppressed/public subject versus ruling/oppressor elite; anti-imperial solidarity and political agency"
    false refl
    false refl
    false refl
    true refl

counterHypothesisRef : String
counterHypothesisRef =
  "counter-hypotheses: independent Quranic/theological derivation; generic anti-imperial convergence; strategic wartime messaging; generic people-versus-elite populist framing"

compilerCausalReceipt : Compiler.CausalMechanismReceipt
compilerCausalReceipt =
  Compiler.causal-mechanism-receipt
    "mechanism:mostazafin-institutional-grammar-continuity"
    "historical:Shariati-mostazafin/Khomeini-institutionalised-oppressed-oppressor-grammar"
    "2026-IRGC:people-state/common-oppressor/shared-pain/agency-argument"
    counterHypothesisRef
    "Glombitza 2026 + reviewed genealogy joins + Tasnim primary letter span receipts"
    true refl
    false refl

glombitzaSnowball :
  Snowball.SourceRoleSnowballReceipt glombitza2026
glombitzaSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt glombitza2026

data InstitutionalContinuityMeansTextualBorrowing : Set where
data SameRelationMeansSameOntology : Set where
data MechanismReceiptMeansEveryIRGCClaimExplained : Set where
data AntiImperialContinuityMeansPolicyNeverChanges : Set where

continuityDoesNotMeanTextualBorrowing :
  InstitutionalContinuityMeansTextualBorrowing → ⊥
continuityDoesNotMeanTextualBorrowing ()

sameRelationDoesNotMeanSameOntology :
  SameRelationMeansSameOntology → ⊥
sameRelationDoesNotMeanSameOntology ()

mechanismDoesNotExplainEveryIRGCClaim :
  MechanismReceiptMeansEveryIRGCClaimExplained → ⊥
mechanismDoesNotExplainEveryIRGCClaim ()

continuityDoesNotMeanPolicyNeverChanges :
  AntiImperialContinuityMeansPolicyNeverChanges → ⊥
continuityDoesNotMeanPolicyNeverChanges ()
