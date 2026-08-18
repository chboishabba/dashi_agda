module Ontology.Hecke.CurrentSaturatedObserverRefinementBridgeExact where

------------------------------------------------------------------------
-- Generic observer-refinement interpretation of the already-landed saturated
-- Hecke separator lane.  No new arithmetic is assumed here:
--
-- * the full current DefectOrbitSummary collision is proved in-repo;
-- * sector/triad/correlation separation remains an explicit theorem target;
-- * any future separator witness automatically upgrades to StrictRefinement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedBalancedCycle
    ; saturatedSupportCascade
    ; saturatedOrbitSummaryP2At
    )
open import Ontology.Hecke.CurrentSaturatedOrbitSummaryCollapse
  using
    ( canonicalSaturatedOrbitSummary
    ; saturatedOrbitSummary≡canonical
    )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries
  using (DefectOrbitSummary)
open import Ontology.Hecke.CurrentSaturatedSectorHistogramComputations
  using
    ( CurrentSaturatedSectorHistograms
    ; sectorHistogramsAt
    )
open import Ontology.Hecke.TriadSectorCorrelationRefinement
  using
    ( SectorCorrelation
    ; currentSaturatedSectorCorrelationAt
    )

coarseSaturatedObserver :
  Observer.Observer CurrentSaturatedGenerator DefectOrbitSummary
coarseSaturatedObserver = saturatedOrbitSummaryP2At

sectorHistogramObserver :
  Observer.Observer CurrentSaturatedGenerator CurrentSaturatedSectorHistograms
sectorHistogramObserver = sectorHistogramsAt

sectorCorrelationObserver :
  Observer.Observer CurrentSaturatedGenerator SectorCorrelation
sectorCorrelationObserver = currentSaturatedSectorCorrelationAt

firstLeft : CurrentSaturatedGenerator
firstLeft = saturatedBalancedCycle

firstRight : CurrentSaturatedGenerator
firstRight = saturatedSupportCascade

coarseFirstPairCollides :
  coarseSaturatedObserver firstLeft ≡ coarseSaturatedObserver firstRight
coarseFirstPairCollides =
  trans
    (saturatedOrbitSummary≡canonical firstLeft)
    (sym (saturatedOrbitSummary≡canonical firstRight))

firstPairDistinct : firstLeft ≡ firstRight → ⊥
firstPairDistinct ()

coarseSaturatedObserverCollision :
  Observer.ObserverCollision coarseSaturatedObserver
coarseSaturatedObserverCollision =
  Observer.observerCollision
    firstLeft
    firstRight
    coarseFirstPairCollides
    firstPairDistinct

coarseSaturatedObserverNotSeparating :
  Observer.Separating coarseSaturatedObserver → ⊥
coarseSaturatedObserverNotSeparating =
  Observer.collisionBlocksSeparation coarseSaturatedObserverCollision

------------------------------------------------------------------------
-- Exact theorem transformers for the existing next-separator targets.
------------------------------------------------------------------------

histogramWitnessGivesStrictRefinement :
  (sectorHistogramObserver firstLeft ≡ sectorHistogramObserver firstRight → ⊥) →
  Observer.StrictRefinement
    coarseSaturatedObserver
    (Observer.pairObserver coarseSaturatedObserver sectorHistogramObserver)
histogramWitnessGivesStrictRefinement histogramSeparates =
  Observer.strictPairRefinement
    coarseSaturatedObserver
    sectorHistogramObserver
    firstLeft
    firstRight
    coarseFirstPairCollides
    histogramSeparates

correlationWitnessGivesStrictRefinement :
  (sectorCorrelationObserver firstLeft ≡ sectorCorrelationObserver firstRight → ⊥) →
  Observer.StrictRefinement
    coarseSaturatedObserver
    (Observer.pairObserver coarseSaturatedObserver sectorCorrelationObserver)
correlationWitnessGivesStrictRefinement correlationSeparates =
  Observer.strictPairRefinement
    coarseSaturatedObserver
    sectorCorrelationObserver
    firstLeft
    firstRight
    coarseFirstPairCollides
    correlationSeparates

------------------------------------------------------------------------
-- The refinement ladder is a theorem-producing interface rather than a claim
-- that either currently packaged richer observer has already separated.
------------------------------------------------------------------------

record CurrentSaturatedObserverFrontier : Set₁ where
  constructor currentSaturatedObserverFrontier
  field
    coarseObserverCollisionProved : Bool
    coarseObserverCollisionProvedIsTrue : coarseObserverCollisionProved ≡ true
    histogramStrictnessStillRequiresWitness :
      Set
    correlationStrictnessStillRequiresWitness :
      Set

open CurrentSaturatedObserverFrontier public

canonicalCurrentSaturatedObserverFrontier : CurrentSaturatedObserverFrontier
canonicalCurrentSaturatedObserverFrontier =
  currentSaturatedObserverFrontier
    true refl
    (sectorHistogramObserver firstLeft ≡ sectorHistogramObserver firstRight → ⊥)
    (sectorCorrelationObserver firstLeft ≡ sectorCorrelationObserver firstRight → ⊥)
