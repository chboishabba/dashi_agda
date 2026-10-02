{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSParetoFrontierExact where

------------------------------------------------------------------------
-- PARETO FRONTIER AFTER E1/E2/E4 COMPILER REDUCTIONS.
--
-- The previous marked-OS max-cut counted E1/E2/E4 as three opaque analytic
-- conditions.  That is now too coarse:
--
-- E1:
--   base O(4) Schwinger covariance is already available;
--   residual = equivariance/naturality of the SAME stress source derivative.
--
-- E2:
--   continuum OS2 Gram positivity is already available;
--   residual = embed the Local-C stress mark into the SAME positive-time
--              reflected cylinder observable algebra, commuting with reflection.
--
-- E4:
--   two-source geometric connected clustering is already available;
--   residual = select the Local-C stress as one literal source observable and
--              identify quantitative connected decay with marked OS4 clustering.
--
-- Plus the two semantic bridges already isolated:
-- B0 nuclear continuity -> OS E0 topology;
-- B3 Local-C symmetry/locality -> marked E3.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE1DifferentiatedCovarianceExact as E1
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2CylinderEmbeddingExact as E2
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE4ClusteringExact as E4

data MarkedOSResidual : Set where
  b0-nuclear-to-os-topology :
    MarkedOSResidual

  e1-stress-derivative-equivariance :
    MarkedOSResidual

  e2-stress-cylinder-embedding :
    MarkedOSResidual

  b3-local-symmetry-to-os-e3 :
    MarkedOSResidual

  e4-stress-source-selection-and-os4-semantics :
    MarkedOSResidual

record MarkedOSParetoStatus : Set where
  field
    baseO4SchwingerCovarianceAlreadyAvailable :
      Bool

    baseContinuumOS2AlreadyAvailable :
      Bool

    baseTwoSourceClusteringAlreadyAvailable :
      Bool

    round109NuclearStressAlreadyAvailable :
      Bool

    localCStressSymmetryLocalityAlreadyAvailable :
      Bool

    e1NeedsNewIndependentCovarianceEstimate :
      Bool

    e2NeedsNewIndependentPositivityEstimate :
      Bool

    e4NeedsNewIndependentDecayEstimate :
      Bool

    remainingResiduals :
      Nat

open MarkedOSParetoStatus public

canonicalMarkedOSParetoStatus : MarkedOSParetoStatus
canonicalMarkedOSParetoStatus = record
  { baseO4SchwingerCovarianceAlreadyAvailable = true
  ; baseContinuumOS2AlreadyAvailable = true
  ; baseTwoSourceClusteringAlreadyAvailable = true
  ; round109NuclearStressAlreadyAvailable = true
  ; localCStressSymmetryLocalityAlreadyAvailable = true
  ; e1NeedsNewIndependentCovarianceEstimate = false
  ; e2NeedsNewIndependentPositivityEstimate = false
  ; e4NeedsNewIndependentDecayEstimate = false
  ; remainingResiduals = 5
  }

remainingResidual0 : MarkedOSResidual
remainingResidual0 = b0-nuclear-to-os-topology

remainingResidual1 : MarkedOSResidual
remainingResidual1 = e1-stress-derivative-equivariance

remainingResidual2 : MarkedOSResidual
remainingResidual2 = e2-stress-cylinder-embedding

remainingResidual3 : MarkedOSResidual
remainingResidual3 = b3-local-symmetry-to-os-e3

remainingResidual4 : MarkedOSResidual
remainingResidual4 = e4-stress-source-selection-and-os4-semantics

opaqueE1AnalyticEstimateStillNeeded : Bool
opaqueE1AnalyticEstimateStillNeeded = false

opaqueE2PositivityEstimateStillNeeded : Bool
opaqueE2PositivityEstimateStillNeeded = false

opaqueE4ClusteringEstimateStillNeeded : Bool
opaqueE4ClusteringEstimateStillNeeded = false

allRemainingWorkIsSameObjectOrSemanticTransport : Bool
allRemainingWorkIsSameObjectOrSemanticTransport = true
