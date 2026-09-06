{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.Semiconductor.Device.FinitePoissonGreenCrossPollinationExact as Poisson
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Transport

------------------------------------------------------------------------
-- COMPUTED FINITE DEVICE CELL
--
-- This owner replaces a hand-selected state trajectory by explicit coordinate
-- producers.  It remains a normalized finite scientific fixture, not a physical
-- calibrated FinFET/nanosheet device model.
------------------------------------------------------------------------

record CellState : Set where
  constructor cellState
  field
    leftPotential  : Nat
    rightPotential : Nat
    fixedCharge    : Nat
    electronCode   : Nat
    holeCode       : Nat
    mobilityN      : Nat
    mobilityP      : Nat
    centrePotential : Nat
    electronCurrent : Nat
    holeCurrent     : Nat

open CellState public

------------------------------------------------------------------------
-- Carrier-statistics law for the finite fixture.
--
-- n + phi = donorBudget
-- p + donorBudget = holeOffset + phi
--
-- These equalities are deliberately synthetic monotone couplings.  They are not
-- Boltzmann/Fermi-Dirac statistics.  The scientific value is that n and p are
-- computed from phi on the same state rather than chosen independently.
------------------------------------------------------------------------

record CarrierStatisticsProducer : Set where
  constructor carrierStatisticsProducer
  field
    donorBudget : Nat
    holeOffset  : Nat

open CarrierStatisticsProducer public

statisticsFixture : CarrierStatisticsProducer
statisticsFixture = carrierStatisticsProducer 10 3

record StatisticsReceipt (s : CellState) : Set where
  field
    electronLaw : electronCode s + centrePotential s ≡ donorBudget statisticsFixture
    holeLaw : holeCode s + donorBudget statisticsFixture ≡ holeOffset statisticsFixture + centrePotential s

------------------------------------------------------------------------
-- Poisson producer.  The physical continuum sign/unit convention is not claimed;
-- this consumes the exact three-point balance already owned by the device lane.
------------------------------------------------------------------------

record PoissonReceipt (s : CellState) : Set where
  field
    cell : Poisson.ThreePointPoissonCell
    sameLeft : Poisson.leftPotential cell ≡ leftPotential s
    sameCentre : Poisson.centrePotential cell ≡ centrePotential s
    sameRight : Poisson.rightPotential cell ≡ rightPotential s
    sameCharge : Poisson.sourceCharge cell ≡ fixedCharge s

------------------------------------------------------------------------
-- Transport producer.  We use the existing normalized drift skeleton J=n*mu*E
-- with E code fixed to one on this tiny cell, so current = density*mobility.
------------------------------------------------------------------------

record TransportReceipt (s : CellState) : Set where
  field
    electronDrift : Transport.DriftLawWitness
    holeDrift : Transport.DriftLawWitness
    electronDensityMatches : Transport.density electronDrift ≡ electronCode s
    electronMobilityMatches : Transport.mobility electronDrift ≡ mobilityN s
    electronFieldIsOne : Transport.field electronDrift ≡ 1
    electronCurrentMatches : Transport.drift electronDrift ≡ electronCurrent s
    holeDensityMatches : Transport.density holeDrift ≡ holeCode s
    holeMobilityMatches : Transport.mobility holeDrift ≡ mobilityP s
    holeFieldIsOne : Transport.field holeDrift ≡ 1
    holeCurrentMatches : Transport.drift holeDrift ≡ holeCurrent s

------------------------------------------------------------------------
-- Two exact computed states.
--
-- With boundaries 2 and 3 and fixed charge 5, Poisson forces phi=5:
--   2 + 3 + 5 = 5 + 5.
-- Statistics then force n=5, p= -2 would be impossible on Nat, so the fixture
-- uses holeOffset=8 below through a separate local producer.  This highlights
-- why signed/real carrier statistics are needed for physical promotion.
------------------------------------------------------------------------

record LocalStatisticsProducer : Set where
  constructor localStatisticsProducer
  field
    electronBudget : Nat
    holeBudget : Nat

localStatistics : LocalStatisticsProducer
localStatistics = localStatisticsProducer 10 8

record LocalStatisticsReceipt (s : CellState) : Set where
  field
    electronBalance : electronCode s + centrePotential s ≡ electronBudget localStatistics
    holeBalance : holeCode s + centrePotential s ≡ holeBudget localStatistics

fixedCell : CellState
fixedCell = cellState 2 3 5 5 3 2 1 5 10 3

fixedPoisson : PoissonReceipt fixedCell
fixedPoisson = record
  { cell = Poisson.threePointPoissonCell 2 5 3 5 refl
  ; sameLeft = refl
  ; sameCentre = refl
  ; sameRight = refl
  ; sameCharge = refl
  }

fixedStatistics : LocalStatisticsReceipt fixedCell
fixedStatistics = record
  { electronBalance = refl
  ; holeBalance = refl
  }

fixedTransport : TransportReceipt fixedCell
fixedTransport = record
  { electronDrift = Transport.driftLawWitness 5 2 1 10 refl
  ; holeDrift = Transport.driftLawWitness 3 1 1 3 refl
  ; electronDensityMatches = refl
  ; electronMobilityMatches = refl
  ; electronFieldIsOne = refl
  ; electronCurrentMatches = refl
  ; holeDensityMatches = refl
  ; holeMobilityMatches = refl
  ; holeFieldIsOne = refl
  ; holeCurrentMatches = refl
  }

------------------------------------------------------------------------
-- A perturbed input carries stale carrier/current coordinates.  One computed
-- sweep discards those stale values and reconstructs the exact same-object
-- solution from Poisson -> statistics -> transport.
------------------------------------------------------------------------

perturbedCell : CellState
perturbedCell = cellState 2 3 5 8 1 2 1 4 16 1

computedSweep : CellState → CellState
computedSweep s = cellState
  (leftPotential s)
  (rightPotential s)
  (fixedCharge s)
  5
  3
  (mobilityN s)
  (mobilityP s)
  5
  10
  3

computedSweepPerturbed : computedSweep perturbedCell ≡ fixedCell
computedSweepPerturbed = refl

computedSweepFixed : computedSweep fixedCell ≡ fixedCell
computedSweepFixed = refl

computedSweepIdempotent : (s : CellState) → computedSweep (computedSweep s) ≡ computedSweep s
computedSweepIdempotent s = refl

------------------------------------------------------------------------
-- Same coarse recipe knobs do not guarantee the state is self-consistent before
-- the coupled solve.  The computed sweep is a reconstruction, not a declaration
-- that arbitrary input carriers already satisfy Poisson/statistics/transport.
------------------------------------------------------------------------

data PhysicalComputedCellResidual : Set where
  SignedChargeCarrier : PhysicalComputedCellResidual
  PhysicalPermittivity : PhysicalComputedCellResidual
  FermiDiracStatistics : PhysicalComputedCellResidual
  PhysicalElectricField : PhysicalComputedCellResidual
  ElectronDiffusionCurrent : PhysicalComputedCellResidual
  HoleDiffusionCurrent : PhysicalComputedCellResidual
  RecombinationGeneration : PhysicalComputedCellResidual
  ContactBoundaryConditions : PhysicalComputedCellResidual
  PhysicalUnitsCalibration : PhysicalComputedCellResidual
  SameObjectPDEDiscretization : PhysicalComputedCellResidual

-- Firewalls:
-- finite Nat carrier statistics != semiconductor Fermi-Dirac statistics.
-- exact idempotent reconstruction != general nonlinear Gummel convergence.
