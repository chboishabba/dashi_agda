module DASHI.Education.DigitalESDDatabaseTranslatedQueriesRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact as T
import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as Protocol
import DASHI.Education.DigitalESDStructuredSearchExact as Search

translatedQueryCountRegression : T.translatedQueryCount ≡ 28
translatedQueryCountRegression = refl

scopusQ4FamilyRegression :
  T.TranslatedQueryReceipt.family T.scopusQ4LifecycleCircularity
  ≡ Search.lifecycleCircularity
scopusQ4FamilyRegression = refl

wosQ4FamilyRegression :
  T.TranslatedQueryReceipt.family T.wosQ4LifecycleCircularity
  ≡ Search.lifecycleCircularity
wosQ4FamilyRegression = refl

ieeeQ4FamilyRegression :
  T.TranslatedQueryReceipt.family T.ieeeQ4LifecycleCircularity
  ≡ Search.lifecycleCircularity
ieeeQ4FamilyRegression = refl

ericQ4FamilyRegression :
  T.TranslatedQueryReceipt.family T.ericQ4LifecycleCircularity
  ≡ Search.lifecycleCircularity
ericQ4FamilyRegression = refl

scopusQ1ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.scopusQ1DigitalEducationESD
  ≡ Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD
scopusQ1ProtocolRegression = refl

wosQ7ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.wosQ7OpenInteroperableRepairable
  ≡ Protocol.PlannedQuery.queryId Protocol.q7OpenInteroperableRepairable
wosQ7ProtocolRegression = refl

ieeeQ1ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.ieeeQ1DigitalEducationESD
  ≡ Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD
ieeeQ1ProtocolRegression = refl

ericQ7ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.ericQ7OpenInteroperableRepairable
  ≡ Protocol.PlannedQuery.queryId Protocol.q7OpenInteroperableRepairable
ericQ7ProtocolRegression = refl

ieeeFrozenRegression :
  T.DatabaseTranslatedQueryBoundary.ieeeSevenExactQueriesFrozen
    T.canonicalDatabaseTranslatedQueryBoundary
  ≡ true
ieeeFrozenRegression = refl

ericFrozenRegression :
  T.DatabaseTranslatedQueryBoundary.ericSevenExactQueriesFrozen
    T.canonicalDatabaseTranslatedQueryBoundary
  ≡ true
ericFrozenRegression = refl

acmStillDebtRegression :
  T.DatabaseTranslatedQueryBoundary.acmSevenExactQueriesFrozen
    T.canonicalDatabaseTranslatedQueryBoundary
  ≡ false
acmStillDebtRegression = refl

executionStillFalseRegression :
  T.DatabaseTranslatedQueryBoundary.anyTranslatedQueryExecutionObserved
    T.canonicalDatabaseTranslatedQueryBoundary
  ≡ false
executionStillFalseRegression = refl

translatedQueryDoesNotCreateResultSetRegression :
  T.TranslatedQueryCreatesResultSet → ⊥
translatedQueryDoesNotCreateResultSetRegression =
  T.translatedQueryDoesNotCreateResultSet
