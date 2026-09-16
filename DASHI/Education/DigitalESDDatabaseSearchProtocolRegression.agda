module DASHI.Education.DigitalESDDatabaseSearchProtocolRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as Protocol

queryCountRegression : Protocol.plannedQueryCount ≡ 6
queryCountRegression = refl

protocolVersionRegression : Protocol.protocolVersion ≡ "digital-esd-search-v1-2026-09-16"
protocolVersionRegression = refl

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
