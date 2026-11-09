module DASHI.Biology.Molecular.BH4OriginalCHNOPFiveAxisSimplexBridgeExact where

-- Exact five-axis CHNOP invariant for the original 27-site / 29-species /
-- 12-finite-reaction spatial source.  This reuses the existing source
-- certificate and RATE-WEIGHTED original stoichiometry proof, not a new
-- simplex or stoichiometric implementation.
--
-- Five nonnegative mass coordinates form an invariant finite accounting
-- chart.  They are NOT yet the compact real weighted simplex required
-- by Brouwer: positivity of the aggregate weight of all 29 species,
-- topology/compactness and an actual fixed-point theorem remain unpaid.
--
-- Original chemistry: Rhea/ChEBI, source-authenticated by separate owner.
-- DASHI's 369 material geometry and source matrix are pre-existing.
-- This is assistant-authored theorem composition, not measured kinetics.

open import DASHI.Core.Prelude
import Data.Vec.Base as V

import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Panel
import DASHI.Biology.Molecular.BH4PanelRateWeightedConservationExact as Rate

-- All five original CHNOP invariants for ONE SAME 27-site vector of
-- source-indexed reaction multiplicities.
record OriginalFiveAxisSpatialReactionBalance
    (certificate : Panel.SourceCertifiedOriginal29x12)
    (siteMultiplicities : V.Vec (V.Vec Nat 12) 27) : Set where
  field
    carbonConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.carbonElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.carbonElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    hydrogenConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.hydrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.hydrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    nitrogenConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    oxygenConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.oxygenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.oxygenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    phosphorusConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.phosphorusElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.phosphorusElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

open OriginalFiveAxisSpatialReactionBalance public

original369x29x12FiveAxisSpatialBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (siteMultiplicities : V.Vec (V.Vec Nat 12) 27) →
  OriginalFiveAxisSpatialReactionBalance certificate siteMultiplicities
original369x29x12FiveAxisSpatialBalance certificate multiplicities = record
  { carbonConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.carbonElement multiplicities
  ; hydrogenConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.hydrogenElement multiplicities
  ; nitrogenConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.nitrogenElement multiplicities
  ; oxygenConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.oxygenElement multiplicities
  ; phosphorusConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.phosphorusElement multiplicities
  }

-- The original owner already yields EVERY source CHNOP coordinate,
-- rather than merely the selected carbon one. The five-coordinate
-- package is an application-specific consumer convenience.
original369x29x12EveryCHNOPBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (multiplicities : V.Vec (V.Vec Nat 12) 27)
  (element : Panel.OriginalCHNOPElement) →
  Rate.spatialRateWeightedReactants
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) multiplicities
  ≡
  Rate.spatialRateWeightedProducts
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) multiplicities
original369x29x12EveryCHNOPBalance =
  Rate.original369x29x12SpatialRateCHNOPBalance
