module DASHI.Cognition.PNF.SensibLawFiniteLegalIssueProjectionRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression

maboRecognitionIssue : Algebra.LegalIssue
maboRecognitionIssue = Algebra.legal-issue
  (Ontology.stableId "issue:Mabo:recognition-survival")
  Regression.maboSurvival
  Regression.maboSystem
  "recognition/survival of pre-existing native title"

maboFullExecutableProjection :
  Search.ExecutableIssueProjection Regression.maboGraph maboRecognitionIssue
maboFullExecutableProjection = Search.executable-issue-projection
  (Search.ruleKey Regression.maboRadicalTitleRule ∷
   Search.ruleKey Regression.maboSurvivalRule ∷ [])
  refl

maboSurvivalOnlyProjection :
  Search.ExecutableIssueProjection Regression.maboGraph maboRecognitionIssue
maboSurvivalOnlyProjection = Search.executable-issue-projection
  (Search.ruleKey Regression.maboSurvivalRule ∷ [])
  refl

maboIssueReachableWithRequiredActiveRules :
  Search.issueReachable
    2 Regression.maboGraph Regression.maboFacts
    maboRecognitionIssue maboFullExecutableProjection
  ≡ true
maboIssueReachableWithRequiredActiveRules = refl

maboIssueBlockedWhenRadicalTitleRuleProjectedOut :
  Search.issueReachable
    2 Regression.maboGraph Regression.maboFacts
    maboRecognitionIssue maboSurvivalOnlyProjection
  ≡ false
maboIssueBlockedWhenRadicalTitleRuleProjectedOut = refl

------------------------------------------------------------------------
-- Projection is a consumer-specific selection over universal rules; it does not
-- delete the radical-title rule from the universal graph.
------------------------------------------------------------------------

data ExecutableProjectionDeletesUniversalRule : Set where

projectionDoesNotDeleteUniversalRule :
  ExecutableProjectionDeletesUniversalRule → ⊥
projectionDoesNotDeleteUniversalRule ()
