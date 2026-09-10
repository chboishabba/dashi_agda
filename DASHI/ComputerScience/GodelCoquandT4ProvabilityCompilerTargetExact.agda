module DASHI.ComputerScience.GodelCoquandT4ProvabilityCompilerTargetExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelExternalProvabilityResultCompilerExact as Results
import DASHI.ComputerScience.GodelCoquandT4AdapterCompilerTargetExact as T4

------------------------------------------------------------------------
-- T4 PROVABILITY PAYMENT -> DASHI LÖB / GÖDEL II
--
-- The arithmetic payment fixes the source carrier.  The theorem payment must
-- use that SAME carrier; this prevents a Löb theorem from one formal system
-- being attached to the syntax/provability predicate of another.
------------------------------------------------------------------------

record CoquandT4ProvabilityPayment
    (payment : T4.CoquandT4SourcePayment) : Set₁ where
  constructor coquandT4ProvabilityPayment
  field
    provability : Results.ExternalProvabilityPayment (T4.source payment)
    sourceLobModuleObserved : Bool
    sourceGodelIIModuleObserved : Bool
    theoremPaymentSamePinnedRevision : Bool

open CoquandT4ProvabilityPayment public

coquandT4ProvabilityStructure :
  (payment : T4.CoquandT4SourcePayment) →
  CoquandT4ProvabilityPayment payment →
  Godel.ProvabilityStructure (T4.coquandT4System payment)
coquandT4ProvabilityStructure payment theoremPayment =
  Results.compileExternalProvabilityStructure
    (T4.source payment)
    (provability theoremPayment)

coquandT4Lob :
  (payment : T4.CoquandT4SourcePayment) →
  (theoremPayment : CoquandT4ProvabilityPayment payment) →
  Godel.LobTheoremResult
    (T4.coquandT4System payment)
    (coquandT4ProvabilityStructure payment theoremPayment)
coquandT4Lob payment theoremPayment =
  Results.compileExternalLob
    (T4.source payment)
    (provability theoremPayment)

coquandT4GodelII :
  (payment : T4.CoquandT4SourcePayment) →
  CoquandT4ProvabilityPayment payment →
  Godel.GodelSecondIncompletenessResult (T4.coquandT4System payment)
coquandT4GodelII payment theoremPayment =
  Results.compileExternalGodelII
    (T4.source payment)
    (provability theoremPayment)

------------------------------------------------------------------------
-- Current boundary.
------------------------------------------------------------------------

record CoquandT4ProvabilityBoundary : Set where
  constructor coquandT4ProvabilityBoundary
  field
    sameCarrierLobCompilerOwned : Bool
    sameCarrierGodelIICompilerOwned : Bool
    sourceArithmeticPaymentOwned : Bool
    sourceProvabilityPaymentOwned : Bool
    localLobResultOwned : Bool
    localGodelIIResultOwned : Bool

canonicalCoquandT4ProvabilityBoundary : CoquandT4ProvabilityBoundary
canonicalCoquandT4ProvabilityBoundary =
  coquandT4ProvabilityBoundary true true false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DifferentPinnedRevisionCanPayTheorem : Set where
data T4LobObservationMeansLocalResult : Set where

differentRevisionDoesNotSilentlyPay : DifferentPinnedRevisionCanPayTheorem → ⊥
differentRevisionDoesNotSilentlyPay ()

observedLobDoesNotMeanImportedLob : T4LobObservationMeansLocalResult → ⊥
observedLobDoesNotMeanImportedLob ()
