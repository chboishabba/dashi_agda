module DASHI.Education.DigitalESDDatabaseTranslationSyntaxExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as Protocol
import DASHI.Education.DigitalESDStructuredSearchExact as Search

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED DATABASE TRANSLATION SYNTAX
--
-- This owner pays only what current official/help documentation supports:
-- field/query syntax for Scopus, Web of Science Core Collection and IEEE
-- Xplore. ERIC and ACM DL remain explicit translation debt until a current
-- reproducible command/UI recipe is pinned. No syntax receipt is an execution
-- receipt, result count, export, completeness claim or inclusion decision.
------------------------------------------------------------------------

scopusAdvancedSearchHelpSource : Attr.AttributedSource
scopusAdvancedSearchHelpSource = Attr.mkNoDOISource
  "Elsevier"
  "How can I best use the Advanced search?"
  "Scopus Support Center"
  "2026"
  "https://service.elsevier.com/app/answers/detail/a_id/11365/supporthub/scopus/~/how-can-i-best-use-the-advanced-search%3F/"
  Attr.institutionalSource
  "Official Scopus support documentation for Advanced Search field codes and Boolean/proximity syntax. Supports use of TITLE-ABS-KEY(...) for title, abstract and keyword searching; does not execute this review's queries or establish search completeness."
  Attr.publicAttribution

webOfScienceFieldTagsSource : Attr.AttributedSource
webOfScienceFieldTagsSource = Attr.mkNoDOISource
  "Clarivate"
  "Web of Science Core Collection Advanced Search Field Tags"
  "Web of Science Help"
  "2026"
  "https://webofscience.help.clarivate.com/Content/wos-core-collection/woscc-search-field-tags.htm"
  Attr.institutionalSource
  "Official Web of Science Core Collection help for Advanced Search field tags. Supports TS=(...) Topic searching over title, abstract, author keywords and Keywords Plus; does not execute this review's queries or establish search completeness."
  Attr.publicAttribution

ieeeCommandSearchHelpSource : Attr.AttributedSource
ieeeCommandSearchHelpSource = Attr.mkNoDOISource
  "IEEE"
  "Command Search"
  "IEEE Xplore Help"
  "2026"
  "https://ieeexplore.ieee.org/Xplorehelp/searching-ieee-xplore/command-search"
  Attr.institutionalSource
  "Official IEEE Xplore help for Command Search field-name syntax and Boolean/proximity operators. Supports quoted field-name plus colon syntax and AND/OR/NOT/NEAR/ONEAR operators; does not execute this review's queries or establish search completeness."
  Attr.publicAttribution

translationSyntaxSourceAtlas : Attr.AttributedSourceAtlas
translationSyntaxSourceAtlas = Attr.mkSourceAtlas
  "digital ESD database translation syntax sources"
  "DASHI.Education.DigitalESDDatabaseTranslationSyntaxExact"
  ( scopusAdvancedSearchHelpSource
  ∷ webOfScienceFieldTagsSource
  ∷ ieeeCommandSearchHelpSource
  ∷ [] )
  "Current official/help documentation supporting the reproducible syntax layer for three planned databases. ERIC and ACM DL translation remain explicit debt rather than being inferred from older or UI-only documentation."

record DatabaseSyntaxReceipt : Set where
  constructor database-syntax-receipt
  field
    surface : Search.SearchSurface
    source : Attr.AttributedSource
    fieldSyntax : String
    booleanSyntax : String
    exactScope : String
    translationBoundary : String

open DatabaseSyntaxReceipt public

scopusSyntaxReceipt : DatabaseSyntaxReceipt
scopusSyntaxReceipt = database-syntax-receipt
  Search.scopus
  scopusAdvancedSearchHelpSource
  "TITLE-ABS-KEY(<query>)"
  "OR / AND / AND NOT; parentheses retained; straight double quotes for phrase searching"
  "TITLE-ABS-KEY searches document title, abstract and keywords"
  "syntax receipt only; exact seven translated query strings, execution timestamp, result count and export remain separate payments"

webOfScienceSyntaxReceipt : DatabaseSyntaxReceipt
webOfScienceSyntaxReceipt = database-syntax-receipt
  Search.webOfScience
  webOfScienceFieldTagsSource
  "TS=(<query>)"
  "AND / OR / NOT / NEAR / SAME with parentheses"
  "TS Topic searches title, abstract, author keywords and Keywords Plus in Web of Science Core Collection"
  "syntax receipt only; exact seven translated query strings, execution timestamp, result count and export remain separate payments"

ieeeSyntaxReceipt : DatabaseSyntaxReceipt
ieeeSyntaxReceipt = database-syntax-receipt
  Search.ieeeXplore
  ieeeCommandSearchHelpSource
  "\"Field name\":value; Command Search supports free-form Boolean expressions"
  "AND / OR / NOT / NEAR / ONEAR; operators in capitals; parentheses may alter precedence"
  "field-restricted Command Search over IEEE Xplore metadata fields; exact field choices for each frozen query remain to be pinned with the translated query receipt"
  "syntax receipt only; exact seven translated query strings, execution timestamp, result count and export remain separate payments"

translationProtocolQueryCount : Nat
translationProtocolQueryCount = Protocol.plannedQueryCount

data ExactTranslationCreatesExecutionReceipt : Set where
data SyntaxDocumentationCreatesSearchCompleteness : Set where
data TranslationSourceCreatesEligibilityDecision : Set where

exactTranslationDoesNotCreateExecutionReceipt : ExactTranslationCreatesExecutionReceipt → ⊥
exactTranslationDoesNotCreateExecutionReceipt ()

syntaxDocumentationDoesNotCreateSearchCompleteness : SyntaxDocumentationCreatesSearchCompleteness → ⊥
syntaxDocumentationDoesNotCreateSearchCompleteness ()

translationSourceDoesNotCreateEligibilityDecision : TranslationSourceCreatesEligibilityDecision → ⊥
translationSourceDoesNotCreateEligibilityDecision ()

record DatabaseTranslationBoundary : Set where
  constructor database-translation-boundary
  field
    scopusExactTranslationSyntaxObserved : Bool
    scopusExactTranslationSyntaxObservedIsTrue :
      scopusExactTranslationSyntaxObserved ≡ true
    webOfScienceExactTranslationSyntaxObserved : Bool
    webOfScienceExactTranslationSyntaxObservedIsTrue :
      webOfScienceExactTranslationSyntaxObserved ≡ true
    ieeeExactTranslationSyntaxObserved : Bool
    ieeeExactTranslationSyntaxObservedIsTrue :
      ieeeExactTranslationSyntaxObserved ≡ true
    ericExactTranslationSyntaxObserved : Bool
    ericExactTranslationSyntaxObservedIsFalse :
      ericExactTranslationSyntaxObserved ≡ false
    acmExactTranslationSyntaxObserved : Bool
    acmExactTranslationSyntaxObservedIsFalse :
      acmExactTranslationSyntaxObserved ≡ false
    sevenExactTranslatedQuerySetsObserved : Bool
    sevenExactTranslatedQuerySetsObservedIsFalse :
      sevenExactTranslatedQuerySetsObserved ≡ false
    anyDatabaseExecutionObserved : Bool
    anyDatabaseExecutionObservedIsFalse : anyDatabaseExecutionObserved ≡ false

open DatabaseTranslationBoundary public

canonicalDatabaseTranslationBoundary : DatabaseTranslationBoundary
canonicalDatabaseTranslationBoundary = database-translation-boundary
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl

translationSyntaxReading : String
translationSyntaxReading =
  "Current official platform documentation pays reproducible search-field syntax for Scopus TITLE-ABS-KEY, Web of Science Core Collection TS Topic, and IEEE Xplore Command Search. ERIC and ACM DL remain translation debt because a current exact executable command/UI recipe has not yet been pinned. Syntax provenance does not create execution, counts, exports, completeness or eligibility."
