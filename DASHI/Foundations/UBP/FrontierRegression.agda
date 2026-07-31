module DASHI.Foundations.UBP.FrontierRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExactRealBackendBoundary as Backend
import DASHI.Foundations.UBP.ExactRealSourceAtlas as Sources
import DASHI.Foundations.UBP.ObserverConstantProvenance as Observer
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
  ∷ Dynamics.taxFiniteDynamicsReceipt
  ∷ []

allFocusedReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
