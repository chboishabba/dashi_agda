module DASHI.Physics.YangMills.YangMillsStrongCouplingAlternativeGateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", official Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Refine the highest-alpha dependency graph from a single line into two honest
-- branches.  The selected-background/RG branch targets weak-coupling control
-- and changing lattice spacing.  The stochastic functional-inequality branch
-- reaches a unique infinite-volume fixed-lattice measure and exponential
-- covariance decay in a strong-coupling window without first constructing the
-- Balaban finite propagator or Schur RG step.
--
-- The branches do not merge automatically: fixed-lattice strong-coupling mass
-- gap is a genuine theorem but is not the cutoff-removal continuum theory in
-- the Clay statement.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data LatticeGapMethod : Set where
  balabanSelectedBackgroundRG : LatticeGapMethod
  shenZhuZhuStochasticFunctional : LatticeGapMethod

data LatticeResultStage : Set where
  localFiniteCoercivity : LatticeResultStage
  finiteVolumePropagator : LatticeResultStage
  scaleUniformRGControl : LatticeResultStage
  uniqueInfiniteVolumeFixedLatticeMeasure : LatticeResultStage
  fixedLatticeExponentialClustering : LatticeResultStage
  changingSpacingContinuumMeasure : LatticeResultStage
  reconstructedContinuumHamiltonianGap : LatticeResultStage

stochasticRouteEntry : LatticeResultStage
stochasticRouteEntry = uniqueInfiniteVolumeFixedLatticeMeasure

stochasticRouteGapEndpoint : LatticeResultStage
stochasticRouteGapEndpoint = fixedLatticeExponentialClustering

rgRouteEntry : LatticeResultStage
rgRouteEntry = localFiniteCoercivity

rgRouteNext : LatticeResultStage → LatticeResultStage
rgRouteNext localFiniteCoercivity = finiteVolumePropagator
rgRouteNext finiteVolumePropagator = scaleUniformRGControl
rgRouteNext scaleUniformRGControl = changingSpacingContinuumMeasure
rgRouteNext uniqueInfiniteVolumeFixedLatticeMeasure =
  fixedLatticeExponentialClustering
rgRouteNext fixedLatticeExponentialClustering =
  fixedLatticeExponentialClustering
rgRouteNext changingSpacingContinuumMeasure =
  reconstructedContinuumHamiltonianGap
rgRouteNext reconstructedContinuumHamiltonianGap =
  reconstructedContinuumHamiltonianGap

strongCouplingGapIsNotContinuumMeasure :
  fixedLatticeExponentialClustering
  ≡ changingSpacingContinuumMeasure → ⊥
strongCouplingGapIsNotContinuumMeasure ()

strongCouplingGapIsNotHamiltonianGap :
  fixedLatticeExponentialClustering
  ≡ reconstructedContinuumHamiltonianGap → ⊥
strongCouplingGapIsNotHamiltonianGap ()

finitePropagatorNotRequiredByStochasticEntry :
  stochasticRouteEntry ≡ finiteVolumePropagator → ⊥
finitePropagatorNotRequiredByStochasticEntry ()

record PublishedStrongCouplingLatticeResult : Set₁ where
  field
    strongCouplingCondition : Set
    finiteVolumeBakryEmeryLowerBound : Set
    volumeUniformLogSobolev : Set
    volumeUniformPoincare : Set
    uniqueInfiniteVolumeInvariantMeasure : Set
    derivativeCommutatorPropagation : Set
    exponentialCylinderCovarianceDecay : Set

record ContinuumBridgeFromStrongCoupling : Set₁ where
  field
    latticeSpacingFamily : Set
    betaRunningLaw : Set
    measuresCompatibleAcrossSpacings : Set
    reflectionPositivityUniformInSpacing : Set
    ultravioletTightness : Set
    asymptoticFreedomMatching : Set
    nontrivialContinuumLimit : Set

-- The first record describes the published fixed-spacing theorem surface.  The
-- second names the genuinely missing bridge; no constructor turns the first
-- into the second.
