module DASHI.ComputerScience.GodelCoquandT4AdapterFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- COQUAND T4 -> DASHI ADAPTER FRONTIER
--
-- After adding the generic external-arithmetic, fixed-point and provability
-- compilers, the T4-specific residual is no longer a long list of reconstructed
-- carriers.  It is the small set of proof-bearing source payments below.
------------------------------------------------------------------------

data T4ObservedCoordinate : Set where
  t4Term
  t4Formula
  t4DerivIndexedByFormula
  t4NotFreeF
  t4MetaSubstF
  t4ObjectSubstitutionSbf
  t4CodeFormula
  t4CodeFormulaNat
  t4Num
  t4Sub
  t4SubEquation
  t4ProvabilityVerifierThmT
  t4DiagonalInfrastructure
  t4LobTheorem
  t4GodelIITheorem : T4ObservedCoordinate

observedT4Coordinates : List T4ObservedCoordinate
observedT4Coordinates =
  t4Term ∷ t4Formula ∷ t4DerivIndexedByFormula ∷ t4NotFreeF ∷
  t4MetaSubstF ∷ t4ObjectSubstitutionSbf ∷ t4CodeFormula ∷
  t4CodeFormulaNat ∷ t4Num ∷ t4Sub ∷ t4SubEquation ∷
  t4ProvabilityVerifierThmT ∷ t4DiagonalInfrastructure ∷
  t4LobTheorem ∷ t4GodelIITheorem ∷ []

------------------------------------------------------------------------
-- Current canonical residuals.
------------------------------------------------------------------------

data T4AdapterResidual : Set where
  arithmeticSourcePayment
  arithmetisedSubstitutionPayment
  finishedDiagonalPayment
  provabilityResultPayment
  localKernelReplayReceipt : T4AdapterResidual

canonicalT4AdapterResiduals : List T4AdapterResidual
canonicalT4AdapterResiduals =
  arithmeticSourcePayment ∷
  arithmetisedSubstitutionPayment ∷
  finishedDiagonalPayment ∷
  provabilityResultPayment ∷
  localKernelReplayReceipt ∷ []

record CoquandT4AdapterReceipt : Set where
  constructor coquandT4AdapterReceipt
  field
    sourceRevisionPinned : Bool
    sourceSafeModeObserved : Bool
    genericExternalArithmeticCompilerOwned : Bool
    genericShapeCompilerOwned : Bool
    genericFinishedDiagonalCompilerOwned : Bool
    genericLobCompilerOwned : Bool
    genericGodelIICompilerOwned : Bool
    arithmeticSourcePaymentOwned : Bool
    substitutionPaymentOwned : Bool
    diagonalPaymentOwned : Bool
    provabilityPaymentOwned : Bool
    localKernelReplayObserved : Bool

currentCoquandT4AdapterReceipt : CoquandT4AdapterReceipt
currentCoquandT4AdapterReceipt =
  coquandT4AdapterReceipt
    false true
    true true true true true
    false false false false false

------------------------------------------------------------------------
-- Why this route is high-alpha:
--
-- T4 already owns finished diagonal, Loeb and Goedel-II machinery on one
-- source derivation/code carrier.  DASHI therefore only needs same-carrier
-- source payments; it does not need to replay a preferred representability or
-- primitive-recursion architecture before transporting those finished results.
------------------------------------------------------------------------

data T4TheoremNameImportsPayment : Set where
data FinishedT4DiagonalRequiresLocalRepresentabilityReplay : Set where
data T4DerivImpliesLocalProvableWithoutCarrierWeld : Set where

theoremNameDoesNotImportPayment : T4TheoremNameImportsPayment → ⊥
theoremNameDoesNotImportPayment ()

finishedDiagonalDoesNotForceLocalReplay :
  FinishedT4DiagonalRequiresLocalRepresentabilityReplay → ⊥
finishedDiagonalDoesNotForceLocalReplay ()

t4DerivNeedsCarrierWeld : T4DerivImpliesLocalProvableWithoutCarrierWeld → ⊥
t4DerivNeedsCarrierWeld ()

record CoquandT4AdapterBoundary : Set where
  constructor coquandT4AdapterBoundary
  field
    externalSourceContainsDiagonalInfrastructure : Bool
    externalSourceContainsLob : Bool
    externalSourceContainsGodelII : Bool
    externalSourceSafeFlagObserved : Bool
    localCompilerArchitectureComplete : Bool
    localSourcePaymentComplete : Bool
    localKernelReplayComplete : Bool

canonicalCoquandT4AdapterBoundary : CoquandT4AdapterBoundary
canonicalCoquandT4AdapterBoundary =
  coquandT4AdapterBoundary true true true true true false false
