{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE4ClusteringExact where

------------------------------------------------------------------------
-- MARKED E4 FROM THE EXISTING TWO-SOURCE CONNECTED-CLUSTERING ROUTE.
--
-- Round274 already proves the quantitative geometric decay
--
--   |Cov(A,B)| <= (1/4) (1/2)^dist(A,B)
--
-- once the literal pair of physical observables is realized as the two
-- CMP116/CMP119 source directions on the SAME state.
--
-- Therefore marked stress clustering does not require a fresh decay theorem.
-- The stress-specific residual is:
--
--   * select the Local-C stress insertion as one observable in that route;
--   * transport the resulting quantitative decay statement into the OS4
--     marked-clustering predicate used by reconstruction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

record MarkedStressE4ClusteringAdapter
    {Scale Volume Root State Observable : Set}
    (twoSource :
      R274.TwoSourceConnectedRootedShellData
        Scale Volume Root State Observable)
    : Set₁ where
  field
    selectedStressObservable :
      Observable

    MarkedE4ClusterCompatibility :
      Set

    quantitativeStressClusteringImpliesMarkedE4 :
      (∀ state other →
        R274.connectedCovarianceMagnitude twoSource
          state selectedStressObservable other
        ≤
        Shell.quarter
        *
        Power.rationalPower Geo.half
          (R274.physicalDistance twoSource
            selectedStressObservable other))
      →
      MarkedE4ClusterCompatibility

open MarkedStressE4ClusteringAdapter public

selectedStressConnectedDecay :
  ∀ {Scale Volume Root State Observable}
    {twoSource :
      R274.TwoSourceConnectedRootedShellData
        Scale Volume Root State Observable}
    (adapter :
      MarkedStressE4ClusteringAdapter twoSource)
    state other →
  R274.connectedCovarianceMagnitude twoSource
    state (selectedStressObservable adapter) other
  ≤
  Shell.quarter
  *
  Power.rationalPower Geo.half
    (R274.physicalDistance twoSource
      (selectedStressObservable adapter) other)
selectedStressConnectedDecay {twoSource = twoSource} adapter =
  R274.connectedCovarianceGeometricBound twoSource

compileMarkedE4 :
  ∀ {Scale Volume Root State Observable}
    {twoSource :
      R274.TwoSourceConnectedRootedShellData
        Scale Volume Root State Observable}
    (adapter :
      MarkedStressE4ClusteringAdapter twoSource) →
  MarkedE4ClusterCompatibility adapter
compileMarkedE4 adapter =
  quantitativeStressClusteringImpliesMarkedE4 adapter
    (selectedStressConnectedDecay adapter)

markedE4NeedsNoNewDecayEstimate : Bool
markedE4NeedsNoNewDecayEstimate = true

markedE4ResidualIsStressSourceSelectionPlusOS4Semantics : Bool
markedE4ResidualIsStressSourceSelectionPlusOS4Semantics = true
