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
import Data.Fin.Base as F

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

------------------------------------------------------------------------
-- The original Brouwer positive-weight simplex uses ONE aggregate mass
-- coordinate. Build it from the five source CHNOP coordinates; do not
-- invent a sixth chemical invariant or infer positivity from atom counts.
------------------------------------------------------------------------

panelWeightedAddWeights :
  ∀ {n} (left right counts : V.Vec Nat n) →
  Panel.panelWeighted (Panel.panelAdd left right) counts
    ≡ Panel.panelWeighted left counts + Panel.panelWeighted right counts
panelWeightedAddWeights V.[] V.[] V.[] = refl
panelWeightedAddWeights
  (V._∷_ a left) (V._∷_ b right) (V._∷_ count counts) =
  trans
    (cong (λ t → (a + b) * count + t)
      (panelWeightedAddWeights left right counts))
    (trans
      (cong (λ t → t +
        (Panel.panelWeighted left counts +
         Panel.panelWeighted right counts))
        (*-distribʳ-+ count a b))
      (Panel.panelShuffle
        (a * count) (b * count)
        (Panel.panelWeighted left counts)
        (Panel.panelWeighted right counts)))

combineOriginalLeftKernel :
  ∀ {n}
  (left right : V.Vec Nat n)
  (reaction : Panel.OriginalFiniteReaction n) →
  Panel.panelWeighted left (Panel.originalReactants reaction)
    ≡ Panel.panelWeighted left (Panel.originalProducts reaction) →
  Panel.panelWeighted right (Panel.originalReactants reaction)
    ≡ Panel.panelWeighted right (Panel.originalProducts reaction) →
  Panel.panelWeighted (Panel.panelAdd left right)
    (Panel.originalReactants reaction)
    ≡ Panel.panelWeighted (Panel.panelAdd left right)
      (Panel.originalProducts reaction)
combineOriginalLeftKernel left right reaction leftBalance rightBalance =
  trans
    (panelWeightedAddWeights left right
      (Panel.originalReactants reaction))
    (trans
      (cong₂ _+_ leftBalance rightBalance)
      (sym (panelWeightedAddWeights left right
        (Panel.originalProducts reaction))))

-- Build the original 29-component aggregate without assigning any
-- measured rates, source concentrations, or independent physiology.
totalCHNOPSourceWeights :
  (certificate : Panel.SourceCertifiedOriginal29x12) →
  V.Vec Nat 29
totalCHNOPSourceWeights certificate =
  Panel.panelAdd
    (Panel.sourceElementWeights certificate Panel.carbonElement)
    (Panel.panelAdd
      (Panel.sourceElementWeights certificate Panel.hydrogenElement)
      (Panel.panelAdd
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement))))

sourceTotalCHNOPLeftKernel :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (column : F.Fin 12) →
  Panel.panelWeighted (totalCHNOPSourceWeights certificate)
    (Panel.originalReactants
      (V.lookup (Panel.sourceFiniteColumns certificate) column))
    ≡
  Panel.panelWeighted (totalCHNOPSourceWeights certificate)
    (Panel.originalProducts
      (V.lookup (Panel.sourceFiniteColumns certificate) column))
sourceTotalCHNOPLeftKernel certificate column =
  combineOriginalLeftKernel
    (Panel.sourceElementWeights certificate Panel.carbonElement)
    (Panel.panelAdd
      (Panel.sourceElementWeights certificate Panel.hydrogenElement)
      (Panel.panelAdd
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement))))
    (V.lookup (Panel.sourceFiniteColumns certificate) column)
    (Panel.sourceColumnLeftKernel certificate Panel.carbonElement column)
    (combineOriginalLeftKernel
      (Panel.sourceElementWeights certificate Panel.hydrogenElement)
      (Panel.panelAdd
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement)))
      (V.lookup (Panel.sourceFiniteColumns certificate) column)
      (Panel.sourceColumnLeftKernel certificate Panel.hydrogenElement column)
      (combineOriginalLeftKernel
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement))
        (V.lookup (Panel.sourceFiniteColumns certificate) column)
        (Panel.sourceColumnLeftKernel certificate Panel.nitrogenElement column)
        (combineOriginalLeftKernel
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement)
          (V.lookup (Panel.sourceFiniteColumns certificate) column)
          (Panel.sourceColumnLeftKernel certificate Panel.oxygenElement column)
          (Panel.sourceColumnLeftKernel certificate Panel.phosphorusElement column))))

-- This is the exact original 27-site x 12-column aggregate CHNOP
-- conservation used by a weighted-mass simplex, for arbitrary natural
-- reaction multiplicity at each site. The actual positive-species
-- hypothesis is deliberately NOT produced here.
original369x29x12AggregateCHNOPBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (multiplicities : V.Vec (V.Vec Nat 12) 27) →
  Rate.spatialRateWeightedReactants
    (totalCHNOPSourceWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
    ≡
  Rate.spatialRateWeightedProducts
    (totalCHNOPSourceWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
original369x29x12AggregateCHNOPBalance certificate multiplicities =
  Rate.allSitesRateWeightedConserve
    (totalCHNOPSourceWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
    (sourceTotalCHNOPLeftKernel certificate)
