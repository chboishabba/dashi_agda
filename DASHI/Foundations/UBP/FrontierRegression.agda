module DASHI.Foundations.UBP.FrontierRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.BishopAbsMigrationReceipt as BishopMigration
import DASHI.Foundations.UBP.ExactRealBackendBoundary as Backend
import DASHI.Foundations.UBP.ExactRealSourceAtlas as Sources
import DASHI.Foundations.UBP.ObserverConstantProvenance as Observer
import DASHI.Foundations.UBP.RationalCertificateTransport as RationalTransport
import DASHI.Foundations.UBP.TaxFiniteDynamicsBoundary as Dynamics

exactRealSourceCountRegression :
  Sources.sourceCount Sources.exactRealSources ≡ 3
exactRealSourceCountRegression = Sources.exactRealSourceCountIsThree

observerDeltaRegression :
  Observer.observerVersionDelta
  ≡ Observer.observerVersionDeltaNormalForm
observerDeltaRegression = Observer.observerVersionDeltaExact

silentReplacementClosed :
  Observer.silentUpstreamReplacementPermitted
    Observer.canonicalObserverProvenanceFork
  ≡ false
silentReplacementClosed =
  Observer.silentUpstreamReplacementPermittedIsFalse
    Observer.canonicalObserverProvenanceFork

finiteExceptionalBishopDependencyClosed :
  Backend.finiteExceptionalLayerDependsOnBishop
    Backend.canonicalExactRealArchitectureStatus
  ≡ false
finiteExceptionalBishopDependencyClosed =
  Backend.finiteExceptionalLayerDependsOnBishopIsFalse
    Backend.canonicalExactRealArchitectureStatus

constructivePiStillOpen :
  Backend.constructivePiIntervalInstantiated
    Backend.canonicalExactRealArchitectureStatus
  ≡ false
constructivePiStillOpen =
  Backend.constructivePiIntervalInstantiatedIsFalse
    Backend.canonicalExactRealArchitectureStatus

kAbsRouteSucceeded :
  BishopMigration.kAbsProved
    BishopMigration.canonicalBishopAbsMigrationStatus
  ≡ true
kAbsRouteSucceeded =
  BishopMigration.kAbsProvedIsTrue
    BishopMigration.canonicalBishopAbsMigrationStatus

commonIndexNotRequiredHere :
  BishopMigration.commonIndexTransportRequiredHere
    BishopMigration.canonicalBishopAbsMigrationStatus
  ≡ false
commonIndexNotRequiredHere =
  BishopMigration.commonIndexTransportRequiredHereIsFalse
    BishopMigration.canonicalBishopAbsMigrationStatus

bishopSequenceValidated :
  BishopMigration.sequenceValidated
    BishopMigration.canonicalBishopAbsMigrationStatus
  ≡ true
bishopSequenceValidated =
  BishopMigration.sequenceValidatedIsTrue
    BishopMigration.canonicalBishopAbsMigrationStatus

observerFactorisationRegression :
  (x y : Data.Rational.ℚ) →
  RationalTransport.observerCrossDifference x y
  ≡ RationalTransport.observerFactorDifference x y
observerFactorisationRegression =
  RationalTransport.observerCrossDifferenceIdentity

constructivePiContainmentStillOpen :
  RationalTransport.constructivePiContainmentInstantiated
    RationalTransport.canonicalRationalFirstArchitectureStatus
  ≡ false
constructivePiContainmentStillOpen =
  RationalTransport.constructivePiContainmentInstantiatedIsFalse
    RationalTransport.canonicalRationalFirstArchitectureStatus

concreteLeechGraphStillOpen :
  Dynamics.concreteLeechGraphInstantiated
    Dynamics.canonicalTaxDynamicsStatus
  ≡ false
concreteLeechGraphStillOpen =
  Dynamics.concreteLeechGraphInstantiatedIsFalse
    Dynamics.canonicalTaxDynamicsStatus

focusedReceipts : List GenericReceipt.GenericReceipt
focusedReceipts =
  Sources.exactRealSourceAtlasReceipt
  ∷ Observer.observerConstantProvenanceReceipt
  ∷ Backend.exactRealBackendBoundaryReceipt
  ∷ BishopMigration.bishopAbsMigrationReceipt
  ∷ RationalTransport.rationalCertificateTransportReceipt
  ∷ Dynamics.taxFiniteDynamicsReceipt
  ∷ []

allFocusedReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
