module DASHI.Education.DigitalESDDatabaseSearchProtocolRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as Protocol
import DASHI.Education.DigitalESDStructuredSearchExact as Search

queryCountRegression : Protocol.plannedQueryCount ≡ 7
queryCountRegression = refl

protocolVersionRegression : Protocol.protocolVersion ≡ "digital-esd-search-v1-2026-09-16"
protocolVersionRegression = refl

q1FamilyRegression : Protocol.PlannedQuery.family Protocol.q1DigitalEducationESD ≡ Search.digitalEducationESD
q1FamilyRegression = refl

q2FamilyRegression : Protocol.PlannedQuery.family Protocol.q2Transformation ≡ Search.digitalEducationESD
q2FamilyRegression = refl

q3FamilyRegression : Protocol.PlannedQuery.family Protocol.q3ReflexiveSustainability ≡ Search.reflexiveDigitalSustainability
q3FamilyRegression = refl

q4LifecycleFamilyRegression : Protocol.PlannedQuery.family Protocol.q4LifecycleCircularity ≡ Search.lifecycleCircularity
q4LifecycleFamilyRegression = refl

q5ParticipantFamilyRegression : Protocol.PlannedQuery.family Protocol.q5ParticipantGovernance ≡ Search.participantAgencyGovernance
q5ParticipantFamilyRegression = refl

q6LongitudinalFamilyRegression : Protocol.PlannedQuery.family Protocol.q6LongitudinalInstitutional ≡ Search.longitudinalInstitutionalImpact
q6LongitudinalFamilyRegression = refl

q7OpenFamilyRegression : Protocol.PlannedQuery.family Protocol.q7OpenInteroperableRepairable ≡ Search.openInteroperabilityRepairability
q7OpenFamilyRegression = refl

translationsRemainUnexecutedRegression :
  Protocol.SearchProtocolBoundary.databaseExecutionObserved
    Protocol.canonicalSearchProtocolBoundary
  ≡ false
translationsRemainUnexecutedRegression = refl

plannedQueryDoesNotCreateExecutionReceiptRegression :
  Protocol.PlannedQueryCreatesExecutionReceipt → ⊥
plannedQueryDoesNotCreateExecutionReceiptRegression =
  Protocol.plannedQueryDoesNotCreateExecutionReceipt

platformNeutralDoesNotEqualDatabaseSyntaxRegression :
  Protocol.PlatformNeutralQueryEqualsDatabaseSpecificSyntax → ⊥
platformNeutralDoesNotEqualDatabaseSyntaxRegression =
  Protocol.platformNeutralQueryDoesNotEqualDatabaseSpecificSyntax

sixFamiliesRetainedRegression :
  Protocol.SearchProtocolBoundary.allSixQueryFamiliesRetained
    Protocol.canonicalSearchProtocolBoundary
  ≡ true
sixFamiliesRetainedRegression = refl
