module DASHI.Crypto.IncrementalResidualTraversalExact where

------------------------------------------------------------------------
-- INCREMENTAL RESIDUAL TRAVERSAL
--
-- A candidate ordering can matter even when candidate count and code rate are
-- identical.  If the residual state can be updated proportionally to the number
-- of changed secret coordinates, Gray-like traversal can reduce verifier work.
-- The cost constants below are explicit architecture parameters, not FIPS-203
-- implementation measurements.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab
import DASHI.Crypto.FiniteMLWETransitionGeometryExact as LabGeometry

record IncrementalResidualCostModel : Set where
  constructor incrementalResidualCostModel
  field
    costPerChangedSecretCoordinate : Nat
    fixedPerCandidateCost : Nat

open IncrementalResidualCostModel public

stepCost : IncrementalResidualCostModel → Nat → Nat
stepCost model changedCoordinates =
  fixedPerCandidateCost model +
  changedCoordinates * costPerChangedSecretCoordinate model

labIncrementalModel : IncrementalResidualCostModel
labIncrementalModel = incrementalResidualCostModel 3 1

binaryStepWork : Nat
binaryStepWork =
  stepCost labIncrementalModel 1 +
  stepCost labIncrementalModel 2 +
  stepCost labIncrementalModel 1

grayStepWork : Nat
grayStepWork =
  stepCost labIncrementalModel 1 +
  stepCost labIncrementalModel 1 +
  stepCost labIncrementalModel 1

binaryStepWorkIs15 : binaryStepWork ≡ 15
binaryStepWorkIs15 = refl

grayStepWorkIs12 : grayStepWork ≡ 12
grayStepWorkIs12 = refl

grayTraversalSavesThreeWorkUnits : binaryStepWork ≡ grayStepWork + 3
grayTraversalSavesThreeWorkUnits = refl

------------------------------------------------------------------------
-- Same-object finite residual checkpoints from the existing lab.
------------------------------------------------------------------------

grayResidual0 : Lab.Error2
grayResidual0 = Lab.candidateResidual Lab.public22 Lab.s00

grayResidual1 : Lab.Error2
grayResidual1 = Lab.candidateResidual Lab.public22 Lab.s01

grayResidual2 : Lab.Error2
grayResidual2 = Lab.candidateResidual Lab.public22 Lab.s11

grayResidual3 : Lab.Error2
grayResidual3 = Lab.candidateResidual Lab.public22 Lab.s10

firstGrayResidualIsKnown : grayResidual1 ≡ Lab.e01
firstGrayResidualIsKnown = refl

lastGrayResidualIsKnown : grayResidual3 ≡ Lab.e10
lastGrayResidualIsKnown = refl

------------------------------------------------------------------------
-- The candidate set is unchanged; only traversal/update geometry changes.
------------------------------------------------------------------------

sameCandidateCarrierDifferentTraversalCost :
  LabGeometry.binaryTraversalCost ≡ 4
  × LabGeometry.grayTraversalCost ≡ 3
sameCandidateCarrierDifferentTraversalCost = refl , refl
  where
  open import Data.Product using (_×_; _,_)
