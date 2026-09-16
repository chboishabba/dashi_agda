module DASHI.Education.DigitalESDDatabaseTranslationSyntaxRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseTranslationSyntaxExact as Translation
import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as Protocol
import DASHI.Education.DigitalESDStructuredSearchExact as Search

scopusSurfaceRegression :
  Translation.DatabaseSyntaxReceipt.surface Translation.scopusSyntaxReceipt
  ≡ Search.scopus
scopusSurfaceRegression = refl

wosSurfaceRegression :
  Translation.DatabaseSyntaxReceipt.surface Translation.webOfScienceSyntaxReceipt
  ≡ Search.webOfScience
wosSurfaceRegression = refl

ieeeSurfaceRegression :
  Translation.DatabaseSyntaxReceipt.surface Translation.ieeeSyntaxReceipt
  ≡ Search.ieeeXplore
ieeeSurfaceRegression = refl

sevenQueryProtocolRetainedRegression :
  Translation.translationProtocolQueryCount ≡ Protocol.plannedQueryCount
sevenQueryProtocolRetainedRegression = refl

scopusTranslationObservedRegression :
  Translation.DatabaseTranslationBoundary.scopusExactTranslationSyntaxObserved
    Translation.canonicalDatabaseTranslationBoundary
  ≡ true
scopusTranslationObservedRegression = refl

wosTranslationObservedRegression :
  Translation.DatabaseTranslationBoundary.webOfScienceExactTranslationSyntaxObserved
    Translation.canonicalDatabaseTranslationBoundary
  ≡ true
wosTranslationObservedRegression = refl

ieeeTranslationObservedRegression :
  Translation.DatabaseTranslationBoundary.ieeeExactTranslationSyntaxObserved
    Translation.canonicalDatabaseTranslationBoundary
  ≡ true
ieeeTranslationObservedRegression = refl

ericTranslationStillDebtRegression :
  Translation.DatabaseTranslationBoundary.ericExactTranslationSyntaxObserved
    Translation.canonicalDatabaseTranslationBoundary
  ≡ false
ericTranslationStillDebtRegression = refl

acmTranslationStillDebtRegression :
  Translation.DatabaseTranslationBoundary.acmExactTranslationSyntaxObserved
    Translation.canonicalDatabaseTranslationBoundary
  ≡ false
acmTranslationStillDebtRegression = refl

translationDoesNotCreateExecutionReceiptRegression :
  Translation.ExactTranslationCreatesExecutionReceipt → ⊥
translationDoesNotCreateExecutionReceiptRegression =
  Translation.exactTranslationDoesNotCreateExecutionReceipt
