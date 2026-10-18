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
-- field/query syntax for Scopus, Web of Science Core Collection, IEEE Xplore
-- the public ERIC API, and ACM Digital Library Advanced Search. No syntax
-- receipt is an execution
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


ericAPISearchSource : Attr.AttributedSource
ericAPISearchSource = Attr.mkNoDOISource
  "Institute of Education Sciences / ERIC"
  "Using the ERIC API for Research Topics"
  "ERIC"
  "undated official notebook / accessed 2026"
  "https://eric.ed.gov/pdf/Using_ERIC_API_for_Research_Topics.pdf"
  Attr.institutionalSource
  "Official ERIC demonstration of the public HTTPS API. It documents the search parameter, JSON/XML/CSV output, rows/start pagination and field-qualified search examples. Supports exact API translation/execution syntax only; it does not execute this review or establish completeness."
  Attr.publicAttribution


acmDigitalLibraryUserGuideSource : Attr.AttributedSource
acmDigitalLibraryUserGuideSource = Attr.mkNoDOISource
  "Association for Computing Machinery"
  "ACM Digital Library User Guide"
  "ACM Libraries"
  "2020 official guide / accessed 2026"
  "https://libraries.acm.org/binaries/content/assets/libraries/acm-digital-library-user-guide.pdf"
  Attr.institutionalSource
  "Official ACM Digital Library guide documenting Advanced Search, the ACM Full-Text collection, the Anywhere search surface, metadata/content filtering, and Boolean AND/OR/NOT. Supports reproducible query translation only; it does not execute this review."
  Attr.publicAttribution

acmPhraseSearchSource : Attr.AttributedSource
acmPhraseSearchSource = Attr.mkNoDOISource
  "Association for Computing Machinery"
  "Using the ACM Digital Library"
  "ACM Libraries"
  "official ACM DL flyer / accessed 2026"
  "https://libraries.acm.org/binaries/content/assets/libraries/archive/dl_flyer.pdf"
  Attr.institutionalSource
  "Official ACM Digital Library search guide documenting quotation marks for exact-phrase search and Advanced Search fields. Supports phrase-syntax provenance only; it does not execute this review or establish completeness."
  Attr.publicAttribution

translationSyntaxSourceAtlas : Attr.AttributedSourceAtlas
translationSyntaxSourceAtlas = Attr.mkSourceAtlas
  "digital ESD database translation syntax sources"
  "DASHI.Education.DigitalESDDatabaseTranslationSyntaxExact"
  ( scopusAdvancedSearchHelpSource
  ∷ webOfScienceFieldTagsSource
  ∷ ieeeCommandSearchHelpSource
  ∷ ericAPISearchSource
  ∷ acmDigitalLibraryUserGuideSource
  ∷ acmPhraseSearchSource
  ∷ [] )
  "Official/help documentation supporting the reproducible syntax layer for all five declared surfaces. Syntax documentation remains distinct from execution, counts, exports, screening and evidence payment."

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


ericSyntaxReceipt : DatabaseSyntaxReceipt
ericSyntaxReceipt = database-syntax-receipt
  Search.eric
  ericAPISearchSource
  "https://api.ies.ed.gov/eric/?search=<query>&rows=<20..200>&format=json&start=<offset>"
  "AND / OR / NOT with parentheses and quoted phrases; field-qualified clauses such as title:\"...\" and subject:\"...\" are supported"
  "public ERIC API search parameter over ERIC metadata/full search surface; rows/start provide explicit pagination and JSON/CSV/XML provide retained export formats"
  "syntax receipt only; exact seven translated query strings, execution timestamp, result count, pagination/export and eligibility remain separate payments"


acmSyntaxReceipt : DatabaseSyntaxReceipt
acmSyntaxReceipt = database-syntax-receipt
  Search.acmDigitalLibrary
  acmDigitalLibraryUserGuideSource
  "ACM Digital Library Advanced Search: The ACM Full-Text collection; Search Within = Anywhere; enter the frozen Boolean expression"
  "AND / OR / NOT; quotation marks retain exact phrases per official ACM DL search guidance"
  "The ACM Full-Text collection searched in the Anywhere field; this choice is part of the frozen translation scope"
  "syntax receipt only; exact seven translated query strings, execution timestamp, result count, export, deduplication and eligibility remain separate payments"

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
    ericExactTranslationSyntaxObservedIsTrue :
      ericExactTranslationSyntaxObserved ≡ true
    acmExactTranslationSyntaxObserved : Bool
    acmExactTranslationSyntaxObservedIsTrue :
      acmExactTranslationSyntaxObserved ≡ true
    sevenExactTranslatedQuerySetsObserved : Bool
    sevenExactTranslatedQuerySetsObservedIsTrue :
      sevenExactTranslatedQuerySetsObserved ≡ true
    anyDatabaseExecutionObserved : Bool
    anyDatabaseExecutionObservedIsFalse : anyDatabaseExecutionObserved ≡ false

open DatabaseTranslationBoundary public

canonicalDatabaseTranslationBoundary : DatabaseTranslationBoundary
canonicalDatabaseTranslationBoundary = database-translation-boundary
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  false refl

translationSyntaxReading : String
translationSyntaxReading =
  "Current official platform documentation pays reproducible search syntax for all five declared surfaces: Scopus TITLE-ABS-KEY, Web of Science Core Collection TS Topic, IEEE Xplore Command Search, the public ERIC API, and ACM Digital Library Advanced Search using the ACM Full-Text collection / Anywhere field with Boolean and exact-phrase syntax. Syntax provenance does not create execution, counts, exports, completeness or eligibility."
