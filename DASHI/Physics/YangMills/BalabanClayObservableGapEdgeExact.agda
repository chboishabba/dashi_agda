module DASHI.Physics.YangMills.BalabanClayObservableGapEdgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- DASHI CONTRIBUTION
--
-- A dense-core clustering theorem proves absence of spectrum below a positive
-- threshold.  Identifying the exact spectral edge with the decay of one
-- particular local observable is stronger: that observable must have nonzero
-- spectral mass arbitrarily close to the edge.  This optional physical
-- identification is kept out of the Clay-critical exclusion theorem.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ObservableGapEdgeData
    (Observable Energy Window : Set) : Set₁ where
  field
    gapEdge : Energy
    windowsAboveEdge : Window → Set
    observableForWindow : Window → Observable
    HasPositiveSpectralMass : Observable → Window → Set
    detectsEveryEdgeWindow : ∀ window →
      windowsAboveEdge window →
      HasPositiveSpectralMass (observableForWindow window) window

open ObservableGapEdgeData public

record ObservableDetectsGapEdge
    {Observable Energy Window : Set}
    (dataSet : ObservableGapEdgeData Observable Energy Window) : Set₁ where
  field
    edgeDetection : ∀ window →
      windowsAboveEdge dataSet window →
      HasPositiveSpectralMass dataSet
        (observableForWindow dataSet window) window

open ObservableDetectsGapEdge public

observableGapEdgeDetection :
  ∀ {Observable Energy Window}
    (dataSet : ObservableGapEdgeData Observable Energy Window) →
  ObservableDetectsGapEdge dataSet
observableGapEdgeDetection dataSet = record
  { edgeDetection = detectsEveryEdgeWindow dataSet }

observableGapEdgeAssemblyLevel : ProofLevel
observableGapEdgeAssemblyLevel = machineChecked

physicalEdgeOverlapInputsLevel : ProofLevel
physicalEdgeOverlapInputsLevel = conditional
