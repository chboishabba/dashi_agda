module DASHI.Education.DigitalESDDatabaseTranslatedQueriesRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact as T
import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as Protocol
import DASHI.Education.DigitalESDStructuredSearchExact as Search

translatedQueryCountRegression : T.translatedQueryCount ≡ 35
translatedQueryCountRegression = refl

scopusQ4FamilyRegression :
  T.TranslatedQueryReceipt.family T.scopusQ4LifecycleCircularity
  ≡ Search.lifecycleCircularity
scopusQ4FamilyRegression = refl

wosQ4FamilyRegression :
  T.TranslatedQueryReceipt.family T.wosQ4LifecycleCircularity
  ≡ Search.lifecycleCircularity
wosQ4FamilyRegression = refl

scopusQ1ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.scopusQ1DigitalEducationESD
  ≡ Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD
scopusQ1ProtocolRegression = refl

wosQ7ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.wosQ7OpenInteroperableRepairable
  ≡ Protocol.PlannedQuery.queryId Protocol.q7OpenInteroperableRepairable
wosQ7ProtocolRegression = refl

executionStillFalseRegression :
  T.DatabaseTranslatedQueryBoundary.anyTranslatedQueryExecutionObserved
    T.canonicalDatabaseTranslatedQueryBoundary
  ≡ false
executionStillFalseRegression = refl

translatedQueryDoesNotCreateResultSetRegression :
  T.TranslatedQueryCreatesResultSet → ⊥
translatedQueryDoesNotCreateResultSetRegression =
  T.translatedQueryDoesNotCreateResultSet


ieeeQ1ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.ieeeQ1DigitalEducationESD
  ≡ Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD
ieeeQ1ProtocolRegression = refl

ericQ1ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.ericQ1DigitalEducationESD
  ≡ Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD
ericQ1ProtocolRegression = refl

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


acmQ1ProtocolRegression :
  T.TranslatedQueryReceipt.protocolQueryId T.acmQ1DigitalEducationESD
  ≡ Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD
acmQ1ProtocolRegression = refl

acmFrozenRegression :
  T.DatabaseTranslatedQueryBoundary.acmSevenExactQueriesFrozen
    T.canonicalDatabaseTranslatedQueryBoundary
  ≡ true
acmFrozenRegression = refl
