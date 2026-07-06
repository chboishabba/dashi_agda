module DASHI.Physics.Closure.NSTriadKNResidualPrimitiveEstimates where

open import Agda.Builtin.Bool using (Bool; false)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Residual primitive-estimate surface.
--
-- The residual lane should close by one of two honest routes:
--
--   Route A: domination by already-closed / soon-to-close profiles
--   Route B: its own row/column exponent theorem
--
-- This file records both options explicitly and leaves the lane fail-closed
-- until one of them is actually inhabited.

data ResidualClosureRoute : Set where
  residualDominationRoute : ResidualClosureRoute
  residualIndependentExponentRoute : ResidualClosureRoute

data ResidualClass : Set where
  dominatedLeftover : ResidualClass
  balancedResidual : ResidualClass
  boundaryResidual : ResidualClass

residualRowCountExp : ResidualClass -> ℕ
residualRowCountExp dominatedLeftover = 0
residualRowCountExp balancedResidual = 1
residualRowCountExp boundaryResidual = 0

residualColumnCountExp : ResidualClass -> ℕ
residualColumnCountExp dominatedLeftover = 0
residualColumnCountExp balancedResidual = 1
residualColumnCountExp boundaryResidual = 0

residualMagnitudeExp : ResidualClass -> ℕ
residualMagnitudeExp dominatedLeftover = 2
residualMagnitudeExp balancedResidual = 2
residualMagnitudeExp boundaryResidual = 1

postulate
  ResidualIncidence : Set

  residualClassification :
    ResidualIncidence -> ResidualClass

  residualDominatedByClosedProfiles :
    (N : ℕ) -> Set

  residualRowIncidenceCountBound :
    (N : ℕ) -> (c : ResidualClass) -> Set

  residualColumnIncidenceCountBound :
    (N : ℕ) -> (c : ResidualClass) -> Set

  residualMagnitudeEnvelopeBound :
    (N : ℕ) -> (c : ResidualClass) -> Set

  residualRowAlphaProductBound :
    (N : ℕ) -> (c : ResidualClass) -> Set

  residualColumnBetaProductBound :
    (N : ℕ) -> (c : ResidualClass) -> Set

record ResidualPrimitiveEstimatesStatus : Set where
  constructor mkResidualPrimitiveEstimatesStatus
  field
    dominationRouteInstalled : Bool
    rowCountBoundProved : Bool
    columnCountBoundProved : Bool
    magnitudeEnvelopeProved : Bool
    rowAlphaProductProved : Bool
    columnBetaProductProved : Bool

open ResidualPrimitiveEstimatesStatus public

currentResidualPrimitiveEstimatesStatus :
  ResidualPrimitiveEstimatesStatus
currentResidualPrimitiveEstimatesStatus =
  mkResidualPrimitiveEstimatesStatus
    true
    false
    false
    false
    false
    false
