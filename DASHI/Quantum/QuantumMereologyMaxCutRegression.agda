{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyMaxCutRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Quantum.QuantumMereologyMaxCutExact as MaxCut

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
