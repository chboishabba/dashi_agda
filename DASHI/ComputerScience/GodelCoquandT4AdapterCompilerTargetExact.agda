module DASHI.ComputerScience.GodelCoquandT4AdapterCompilerTargetExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelArithmetisedFormalSystemShapeAuthorityExact as Shape
import DASHI.ComputerScience.GodelExternalArithmeticABIMinimalCompilerExact as External

------------------------------------------------------------------------
-- COQUAND T4 PAYMENT -> DASHI ABI
--
-- The external repository itself is not imported into dashi_agda.  This file
-- is the exact local target that a source-native T4 adapter has to inhabit.
-- Once inhabited, system/substitution/shape objects are compiler outputs and
-- must not be rebuilt separately.
------------------------------------------------------------------------

record CoquandT4SourcePayment : Set₁ where
  constructor coquandT4SourcePayment
  field
    pinnedRevision : String
    safeModeObserved : Bool
    source : External.ExternalArithmeticSource
    substitution : External.ExternalArithmetisedSubstitution source

    -- Source-identity coordinates: these do not prove the payload, but prevent
    -- an arbitrary external arithmetic source from being silently called T4.
    termCarrierNamedT4 : Bool
    formulaCarrierNamedT4 : Bool
    derivationCarrierNamedT4 : Bool
    freeVariableRelationNamedNotFreeF : Bool
    metaSubstitutionNamedSubstF : Bool
    formulaCodeNamedCodeFormulaNat : Bool
    numeralNamedNum : Bool
    objectSubstitutionNamedSub : Bool

open CoquandT4SourcePayment public

coquandT4System :
  CoquandT4SourcePayment → Godel.ArithmetisedFormalSystem
coquandT4System payment =
  External.compileExternalArithmeticSystem (source payment)

coquandT4Substitution :
  (payment : CoquandT4SourcePayment) →
  Godel.ArithmetisedSubstitution (coquandT4System payment)
coquandT4Substitution payment =
  External.compileExternalArithmetisedSubstitution
    (source payment)
    (substitution payment)

coquandT4Shape :
  (payment : CoquandT4SourcePayment) →
  Shape.FormulaSentenceShapeAuthority (coquandT4System payment)
coquandT4Shape payment =
  External.compileExternalShapeAuthority (source payment)

------------------------------------------------------------------------
-- The current canonical integration cut is therefore one payment object,
-- rather than a parallel list of manually reconstructed carriers.
------------------------------------------------------------------------

record CoquandT4CompiledAdapterReceipt : Set where
  constructor coquandT4CompiledAdapterReceipt
  field
    sourcePaymentObjectSpecified : Bool
    formalSystemCompilerOwned : Bool
    arithmetisedSubstitutionCompilerOwned : Bool
    shapeAuthorityCompilerOwned : Bool
    localT4PaymentInhabitantOwned : Bool
    externalSourceVendoredOrImportedHere : Bool
    localKernelReplayObserved : Bool

canonicalCoquandT4CompiledAdapterReceipt : CoquandT4CompiledAdapterReceipt
canonicalCoquandT4CompiledAdapterReceipt =
  coquandT4CompiledAdapterReceipt
    true true true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data T4SourceNameAloneInhabitsPayment : Set where
data T4PaymentImportsTheoremResultsAutomatically : Set where
data CompiledSystemMeansExternalRepositoryWasKernelReplayedLocally : Set where

sourceNameDoesNotInhabitPayment : T4SourceNameAloneInhabitsPayment → ⊥
sourceNameDoesNotInhabitPayment ()

paymentDoesNotAutoImportTheorems : T4PaymentImportsTheoremResultsAutomatically → ⊥
paymentDoesNotAutoImportTheorems ()

compilerDoesNotClaimLocalReplay :
  CompiledSystemMeansExternalRepositoryWasKernelReplayedLocally → ⊥
compilerDoesNotClaimLocalReplay ()
