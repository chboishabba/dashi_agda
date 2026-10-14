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

typed-selected-cpo-refinement-source-written :
  Finite.TypedSelectedCPOFiniteHermitianRefinementSourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
typed-selected-cpo-refinement-source-written =
  Finite.TypedSelectedCPOFiniteHermitianRefinementSourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

typed-selected-product-cpo-eigenbasis-source-written :
  Finite.TypedSelectedCPOProductEigenbasisSourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
typed-selected-product-cpo-eigenbasis-source-written =
  Finite.TypedSelectedCPOProductEigenbasisSourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

generic-admissibility-does-not-create-typed-symmetry :
  Finite.GenericCPOAdmissibilityCreatesTypedSymmetry
    Finite.canonicalFiniteQuantumProducerStatus ≡ false
generic-admissibility-does-not-create-typed-symmetry =
  Finite.GenericCPOAdmissibilityCreatesTypedSymmetryIsFalse
    Finite.canonicalFiniteQuantumProducerStatus

coordinate-born-nonnegative-source-written :
  Finite.CoordinateBornProbabilityNonnegativeSourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
coordinate-born-nonnegative-source-written =
  Finite.CoordinateBornProbabilityNonnegativeSourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

coordinate-born-normalized-source-written :
  Finite.CoordinateBornProbabilityNormalizedSourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
coordinate-born-normalized-source-written =
  Finite.CoordinateBornProbabilityNormalizedSourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

finite-von-neumann-entropy-source-written :
  Finite.FiniteVonNeumannEntropySourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
finite-von-neumann-entropy-source-written =
  Finite.FiniteVonNeumannEntropySourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

bipartite-mutual-information-source-written :
  Finite.BipartiteMutualInformationSourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
bipartite-mutual-information-source-written =
  Finite.BipartiteMutualInformationSourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

ccm-distance-ansatz-does-not-create-metric :
  Finite.CCMDistanceAnsatzCreatesMetric
    Finite.canonicalFiniteQuantumProducerStatus ≡ false
ccm-distance-ansatz-does-not-create-metric =
  Finite.CCMDistanceAnsatzCreatesMetricIsFalse
    Finite.canonicalFiniteQuantumProducerStatus

finite-schwinger-minimizer-source-written :
  Finite.FiniteNonemptySchwingerMinimizerSourceWritten
    Finite.canonicalFiniteQuantumProducerStatus ≡ true
finite-schwinger-minimizer-source-written =
  Finite.FiniteNonemptySchwingerMinimizerSourceWrittenIsTrue
    Finite.canonicalFiniteQuantumProducerStatus

finite-minimizer-does-not-create-uniqueness :
  Finite.FiniteSchwingerMinimizerCreatesUniqueness
    Finite.canonicalFiniteQuantumProducerStatus ≡ false
finite-minimizer-does-not-create-uniqueness =
  Finite.FiniteSchwingerMinimizerCreatesUniquenessIsFalse
    Finite.canonicalFiniteQuantumProducerStatus

arbitrary-selected-cpo-eigenbasis-remains-open :
  Finite.ArbitrarySelectedCPOEigenbasisPaid
    Finite.canonicalFiniteQuantumProducerStatus ≡ false
arbitrary-selected-cpo-eigenbasis-remains-open =
  Finite.ArbitrarySelectedCPOEigenbasisPaidIsFalse
    Finite.canonicalFiniteQuantumProducerStatus
