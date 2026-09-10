module DASHI.ComputerScience.GodelCoquandT4DiagonalCompilerTargetExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelExternalDiagonalResultCompilerExact as Diagonal
import DASHI.ComputerScience.GodelCoquandT4AdapterCompilerTargetExact as T4

------------------------------------------------------------------------
-- T4 FINISHED DIAGONAL RESULT -> DASHI DIAGONAL-LEMMA AUTHORITY
------------------------------------------------------------------------

record CoquandT4DiagonalPayment
    (payment : T4.CoquandT4SourcePayment) : Set₁ where
  constructor coquandT4DiagonalPayment
  field
    diagonal : Diagonal.ExternalDiagonalPayment (T4.source payment)
    sourceDiagonalInfrastructureObserved : Bool
    sourcePaymentSamePinnedRevision : Bool

open CoquandT4DiagonalPayment public

coquandT4DiagonalLemma :
  (payment : T4.CoquandT4SourcePayment) →
  CoquandT4DiagonalPayment payment →
  Godel.DiagonalLemmaAuthority (T4.coquandT4System payment)
coquandT4DiagonalLemma payment theoremPayment =
  Diagonal.compileExternalDiagonalLemma
    (T4.source payment)
    (diagonal theoremPayment)

------------------------------------------------------------------------
-- This is now the shortest theorem route.  PR representability remains a
-- useful explanatory/compatibility producer but is not mandatory if the same
-- external source already supplies the finished fixed-point theorem.
------------------------------------------------------------------------

record CoquandT4DiagonalBoundary : Set where
  constructor coquandT4DiagonalBoundary
  field
    arithmeticPaymentSpecified : Bool
    finishedDiagonalPaymentSpecified : Bool
    localDiagonalCompilerOwned : Bool
    localArithmeticPaymentOwned : Bool
    localDiagonalPaymentOwned : Bool
    localDiagonalLemmaOwned : Bool
    localRepresentabilityReplayMandatory : Bool

canonicalCoquandT4DiagonalBoundary : CoquandT4DiagonalBoundary
canonicalCoquandT4DiagonalBoundary =
  coquandT4DiagonalBoundary true true true false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data T4DiagonalObservationInhabitsPayment : Set where
data T4FinishedDiagonalMakesDifferentCarrierSameObject : Set where

observationDoesNotInhabitPayment : T4DiagonalObservationInhabitsPayment → ⊥
observationDoesNotInhabitPayment ()

differentCarrierStillNeedsPayment :
  T4FinishedDiagonalMakesDifferentCarrierSameObject → ⊥
differentCarrierStillNeedsPayment ()
