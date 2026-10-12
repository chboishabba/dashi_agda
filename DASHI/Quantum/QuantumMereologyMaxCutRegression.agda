{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyMaxCutRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Quantum.QuantumMereologyMaxCutExact as MaxCut
import DASHI.Quantum.QuantumMereologyFiniteQuantumProducerAuthorityExact as Finite

source-written-producer-does-not-create-selection :
  MaxCut.sourceWrittenProducerCreatesSelection
    MaxCut.canonicalQuantumMereologyMaxCutBoundary ≡ false
source-written-producer-does-not-create-selection =
  MaxCut.sourceWrittenProducerCreatesSelectionIsFalse
    MaxCut.canonicalQuantumMereologyMaxCutBoundary

selected-tps-does-not-create-geometry-without-relation :
  MaxCut.selectedTPSCreatesGeometryWithoutPairRelation
    MaxCut.canonicalQuantumMereologyMaxCutBoundary ≡ false
selected-tps-does-not-create-geometry-without-relation =
  MaxCut.selectedTPSCreatesGeometryWithoutPairRelationIsFalse
    MaxCut.canonicalQuantumMereologyMaxCutBoundary

spatial-geometry-does-not-create-spacetime :
  MaxCut.spatialGeometryCreatesSpacetime
    MaxCut.canonicalQuantumMereologyMaxCutBoundary ≡ false
spatial-geometry-does-not-create-spacetime =
  MaxCut.spatialGeometryCreatesSpacetimeIsFalse
    MaxCut.canonicalQuantumMereologyMaxCutBoundary

geometry-collision-forces-refinement :
  MaxCut.geometryCriterionCollisionCreatesRefinementObligation
    MaxCut.canonicalQuantumMereologyMaxCutBoundary ≡ true
geometry-collision-forces-refinement =
  MaxCut.geometryCriterionCollisionCreatesRefinementObligationIsTrue
    MaxCut.canonicalQuantumMereologyMaxCutBoundary

geometry-consumer-is-least-sufficient-observer :
  MaxCut.geometryConsumerObserverIsLeastSufficient
    MaxCut.canonicalQuantumMereologyMaxCutBoundary ≡ true
geometry-consumer-is-least-sufficient-observer =
  MaxCut.geometryConsumerObserverIsLeastSufficientIsTrue
    MaxCut.canonicalQuantumMereologyMaxCutBoundary

boundary-adequacy-is-consumer-relative :
  MaxCut.holographicBoundaryAdequacyIsConsumerRelative
    MaxCut.canonicalQuantumMereologyMaxCutBoundary ≡ true
boundary-adequacy-is-consumer-relative =
  MaxCut.holographicBoundaryAdequacyIsConsumerRelativeIsTrue
    MaxCut.canonicalQuantumMereologyMaxCutBoundary

standard-basis-projector-family-source-written :
  Finite.StandardBasisProjectorFamilySourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
standard-basis-projector-family-source-written =
  Finite.StandardBasisProjectorFamilySourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

finite-hermitian-spectral-basis-source-written :
  Finite.FiniteHermitianSpectralBasisSourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
finite-hermitian-spectral-basis-source-written =
  Finite.FiniteHermitianSpectralBasisSourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

arbitrary-selected-cpo-eigenbasis-remains-open :
  Finite.ArbitrarySelectedCPOEigenbasisPaid
    Finite.canonicalFiniteQuantumProducerStatus ≡ false
arbitrary-selected-cpo-eigenbasis-remains-open =
  Finite.ArbitrarySelectedCPOEigenbasisPaidIsFalse
    Finite.canonicalFiniteQuantumProducerStatus
