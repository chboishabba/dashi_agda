module DASHI.Physics.YangMills.YangMillsHodgeCoercivityFrontierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- Jozef Dodziuk,
-- "Finite-Difference Approach to the Hodge Theory of Harmonic Forms".
-- DOI: 10.2307/2373615.
--
-- DASHI CONTRIBUTION
--
-- Attach the new finite gauge/Hodge theorem to the repository's established
-- strong-coupling and selected-background dependency graph.  The exact
-- abelian model now inhabits the local-finite-coercivity entry stage.  Every
-- subsequent step--nonabelian weighted adjointness, finite propagator,
-- spacing-uniform OS2/OS4/KP control, continuum measure and reconstructed
-- Hamiltonian gap--remains a separately typed obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.FiniteAbelianGaugeHodgeExact as Gauge
import DASHI.Physics.Closure.FiniteHodgePhysicsCrossPollinationExact as HodgeBridge
import DASHI.Physics.YangMills.YangMillsStrongCouplingAlternativeGateExact as Existing
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound30StrongCouplingFunctionalValidation as Round30

localCoercivityStageNowInhabited : Existing.LatticeResultStage
localCoercivityStageNowInhabited = Existing.localFiniteCoercivity

localCoercivityMatchesRGEntry :
  localCoercivityStageNowInhabited ≡ Existing.rgRouteEntry
localCoercivityMatchesRGEntry = refl

localCoercivityCertificate : Gauge.FiniteAbelianGaugeCertificate
localCoercivityCertificate = Gauge.canonicalFiniteAbelianGaugeCertificate

finiteHodgePhysicsBridge : HodgeBridge.FiniteHodgePhysicsBridge
finiteHodgePhysicsBridge = HodgeBridge.canonicalFiniteHodgePhysicsBridge

localCoercivityIsNotContinuumHamiltonianGap :
  Existing.localFiniteCoercivity
  ≡ Existing.reconstructedContinuumHamiltonianGap → ⊥
localCoercivityIsNotContinuumHamiltonianGap ()

localCoercivityIsNotFixedLatticeClustering :
  Existing.localFiniteCoercivity
  ≡ Existing.fixedLatticeExponentialClustering → ⊥
localCoercivityIsNotFixedLatticeClustering ()

data YangMillsFrontierObligation : Set where
  nonabelianCovariantHodgeAdjoint
  finiteVolumeGaugeQuotientCoercivity
  finiteVolumePropagatorConstruction
  os2ReflectionPositivity
  os4ClusterDecomposition
  kpSpatialLargeFieldControl
  spacingUniformGapLowerBound
  ultravioletTightness
  nontrivialContinuumMeasure
  reconstructedHamiltonianMassGap

record YangMillsHodgeCoercivityFrontier : Set₁ where
  field
    localAbelianCoercivity : Gauge.FiniteAbelianGaugeCertificate
    existingRound30Validation : Set
    nonabelianAdjointBoundary : Set
    finitePropagatorBoundary : Set
    os2Boundary : Set
    os4Boundary : Set
    kpBoundary : Set
    volumeUniformBoundary : Set
    continuumMeasureBoundary : Set
    hamiltonianGapBoundary : Set

canonicalYangMillsHodgeCoercivityFrontier :
  YangMillsHodgeCoercivityFrontier
canonicalYangMillsHodgeCoercivityFrontier = record
  { localAbelianCoercivity = localCoercivityCertificate
  ; existingRound30Validation =
      Round30.BalabanClayHighestAlphaRound30StrongCouplingFunctionalValidation
  ; nonabelianAdjointBoundary = Set
  ; finitePropagatorBoundary = Set
  ; os2Boundary = Set
  ; os4Boundary = Set
  ; kpBoundary = Set
  ; volumeUniformBoundary = Set
  ; continuumMeasureBoundary = Set
  ; hamiltonianGapBoundary = Set
  }

record PublishedStrongCouplingToContinuumLadder : Set₁ where
  field
    publishedFixedLatticeResult : Existing.PublishedStrongCouplingLatticeResult
    continuumBridge : Existing.ContinuumBridgeFromStrongCoupling
    connectsFixedSpacingToChangingSpacing : Set
    preservesReflectionPositivity : Set
    preservesExponentialClustering : Set
    reconstructsPositiveHamiltonian : Set
    transfersUniformGap : Set
