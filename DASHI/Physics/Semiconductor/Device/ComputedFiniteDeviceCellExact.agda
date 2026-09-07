{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Analysis.StrictContractionUniqueness as SCU
import DASHI.Physics.Semiconductor.Device.FinitePoissonGreenCrossPollinationExact as Poisson
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Transport

------------------------------------------------------------------------
-- COMPUTED FINITE DEVICE CELL
--
-- The earlier three-state Gummel fixture chose the coupled coordinates directly.
-- Here the state carrier is only a finite source-charge coordinate.  Potential,
-- electron/hole populations and drift currents are then computed functions of
-- that source coordinate and supplied with exact Poisson/statistics/transport
-- receipts.
--
-- All numbers are normalized finite codes.  This is not a calibrated transistor
-- model and does not claim Boltzmann/Fermi-Dirac statistics, physical field units,
-- or a real-device Gummel convergence theorem.
------------------------------------------------------------------------

data SourceCharge : Set where
  q1 : SourceCharge
  q3 : SourceCharge
  q5 : SourceCharge

chargeCode : SourceCharge → Nat
chargeCode q1 = 1
chargeCode q3 = 3
chargeCode q5 = 5

-- Fixed boundary potentials for the tiny one-cell problem.
leftBoundary : Nat
leftBoundary = 2

rightBoundary : Nat
rightBoundary = 3

------------------------------------------------------------------------
-- Poisson producer.
--
-- Existing finite device convention:
--   phi_l + phi_r + rho = phi_c + phi_c.
-- For rho in {1,3,5}, the exact centre solutions are {3,4,5}.
------------------------------------------------------------------------

centrePotential : SourceCharge → Nat
centrePotential q1 = 3
centrePotential q3 = 4
centrePotential q5 = 5

poissonCell : SourceCharge → Poisson.ThreePointPoissonCell
poissonCell q1 = Poisson.threePointPoissonCell 2 3 3 1 refl
poissonCell q3 = Poisson.threePointPoissonCell 2 4 3 3 refl
poissonCell q5 = Poisson.threePointPoissonCell 2 5 3 5 refl

poissonLeftMatches : (q : SourceCharge) → Poisson.leftPotential (poissonCell q) ≡ leftBoundary
poissonLeftMatches q1 = refl
poissonLeftMatches q3 = refl
poissonLeftMatches q5 = refl

poissonRightMatches : (q : SourceCharge) → Poisson.rightPotential (poissonCell q) ≡ rightBoundary
poissonRightMatches q1 = refl
poissonRightMatches q3 = refl
poissonRightMatches q5 = refl

poissonCentreMatches : (q : SourceCharge) → Poisson.centrePotential (poissonCell q) ≡ centrePotential q
poissonCentreMatches q1 = refl
poissonCentreMatches q3 = refl
poissonCentreMatches q5 = refl

poissonChargeMatches : (q : SourceCharge) → Poisson.sourceCharge (poissonCell q) ≡ chargeCode q
poissonChargeMatches q1 = refl
poissonChargeMatches q3 = refl
poissonChargeMatches q5 = refl

------------------------------------------------------------------------
-- Finite carrier-statistics producer.
--
-- Synthetic exact laws on this admitted family:
--   n + phi = 10
--   p + 2 = phi
-- encoded by exhaustive finite receipts.  They are intentionally not promoted
-- to semiconductor equilibrium statistics.
------------------------------------------------------------------------

electronPopulation : SourceCharge → Nat
electronPopulation q1 = 7
electronPopulation q3 = 6
electronPopulation q5 = 5

holePopulation : SourceCharge → Nat
holePopulation q1 = 1
holePopulation q3 = 2
holePopulation q5 = 3

record CarrierStatisticsReceipt (q : SourceCharge) : Set where
  field
    electronLaw :
      electronPopulation q + centrePotential q ≡ 10
    holeLaw :
      holePopulation q + 2 ≡ centrePotential q

open CarrierStatisticsReceipt public

carrierStatisticsReceipt : (q : SourceCharge) → CarrierStatisticsReceipt q
carrierStatisticsReceipt q1 = record { electronLaw = refl ; holeLaw = refl }
carrierStatisticsReceipt q3 = record { electronLaw = refl ; holeLaw = refl }
carrierStatisticsReceipt q5 = record { electronLaw = refl ; holeLaw = refl }

------------------------------------------------------------------------
-- Transport producer using the already-existing normalized drift skeleton.
-- Electron mobility code is 2, hole mobility code is 1, and field code is 1.
------------------------------------------------------------------------

electronCurrent : SourceCharge → Nat
electronCurrent q1 = 14
electronCurrent q3 = 12
electronCurrent q5 = 10

holeCurrent : SourceCharge → Nat
holeCurrent q1 = 1
holeCurrent q3 = 2
holeCurrent q5 = 3

electronDrift : (q : SourceCharge) → Transport.DriftLawWitness
electronDrift q1 = Transport.driftLawWitness 7 2 1 14 refl
electronDrift q3 = Transport.driftLawWitness 6 2 1 12 refl
electronDrift q5 = Transport.driftLawWitness 5 2 1 10 refl

holeDrift : (q : SourceCharge) → Transport.DriftLawWitness
holeDrift q1 = Transport.driftLawWitness 1 1 1 1 refl
holeDrift q3 = Transport.driftLawWitness 2 1 1 2 refl
holeDrift q5 = Transport.driftLawWitness 3 1 1 3 refl

------------------------------------------------------------------------
-- Same-object computed state.  No independent choices remain for phi,n,p,Jn,Jp
-- once q is selected inside this finite fixture.
------------------------------------------------------------------------

record ComputedCell : Set where
  constructor computedCell
  field
    sourceChargeCode : Nat
    phi : Nat
    n : Nat
    p : Nat
    Jn : Nat
    Jp : Nat

open ComputedCell public

solveCell : SourceCharge → ComputedCell
solveCell q = computedCell
  (chargeCode q)
  (centrePotential q)
  (electronPopulation q)
  (holePopulation q)
  (electronCurrent q)
  (holeCurrent q)

q1Solution : solveCell q1 ≡ computedCell 1 3 7 1 14 1
q1Solution = refl

q3Solution : solveCell q3 ≡ computedCell 3 4 6 2 12 2
q3Solution = refl

q5Solution : solveCell q5 ≡ computedCell 5 5 5 3 10 3
q5Solution = refl

------------------------------------------------------------------------
-- Finite residual update.
--
-- This is an explicit normalized correction law on the admitted charge family:
-- q1 -> q3 -> q5 -> q5.  Unlike the older hand-selected coordinate trajectory,
-- every full device coordinate after each correction is recomputed by solveCell.
-- The correction law itself remains synthetic and is NOT a physical charge-
-- neutrality/Newton/Gummel update.
------------------------------------------------------------------------

chargeCorrection : SourceCharge → SourceCharge
chargeCorrection q1 = q3
chargeCorrection q3 = q5
chargeCorrection q5 = q5

computedSweep : ComputedCell → ComputedCell
computedSweep (computedCell 1 3 7 1 14 1) = solveCell q3
computedSweep (computedCell 3 4 6 2 12 2) = solveCell q5
computedSweep (computedCell 5 5 5 3 10 3) = solveCell q5
computedSweep other = other

sourceSweep : SourceCharge → ComputedCell
sourceSweep q = solveCell (chargeCorrection q)

q1SweepComputed : sourceSweep q1 ≡ solveCell q3
q1SweepComputed = refl

q3SweepComputed : sourceSweep q3 ≡ solveCell q5
q3SweepComputed = refl

q5SweepFixed : sourceSweep q5 ≡ solveCell q5
q5SweepFixed = refl

q1ReachesFixedInTwo : sourceSweep (chargeCorrection q1) ≡ solveCell q5
q1ReachesFixedInTwo = refl

------------------------------------------------------------------------
-- Exhaustive convergence certificate on the source family, using the corrected
-- generic distinct-pair contraction theory discovered in the previous pass.
------------------------------------------------------------------------

data CellDistance : Set where
  d0 : CellDistance
  d1 : CellDistance
  d2 : CellDistance

sourceDistance : SourceCharge → SourceCharge → CellDistance
sourceDistance q1 q1 = d0
sourceDistance q3 q3 = d0
sourceDistance q5 q5 = d0
sourceDistance q1 q3 = d2
sourceDistance q3 q1 = d2
sourceDistance q1 q5 = d2
sourceDistance q5 q1 = d2
sourceDistance q3 q5 = d1
sourceDistance q5 q3 = d1

data StrictlySmaller : CellDistance → CellDistance → Set where
  d0<d1 : StrictlySmaller d0 d1
  d1<d2 : StrictlySmaller d1 d2
  d0<d2 : StrictlySmaller d0 d2

sourceEquality :
  (left right : SourceCharge) →
  (left ≡ right) ⊎ SCU.Distinct left right
sourceEquality q1 q1 = inj₁ refl
sourceEquality q1 q3 = inj₂ (λ ())
sourceEquality q1 q5 = inj₂ (λ ())
sourceEquality q3 q1 = inj₂ (λ ())
sourceEquality q3 q3 = inj₁ refl
sourceEquality q3 q5 = inj₂ (λ ())
sourceEquality q5 q1 = inj₂ (λ ())
sourceEquality q5 q3 = inj₂ (λ ())
sourceEquality q5 q5 = inj₁ refl

strictDistanceIrreflexive :
  SCU.IrreflexiveStrictDistance CellDistance StrictlySmaller
strictDistanceIrreflexive = record
  { irreflexive = λ where
      d0 ()
      d1 ()
      d2 ()
  }

correctionContractsDistinct :
  (left right : SourceCharge) →
  SCU.Distinct left right →
  StrictlySmaller
    (sourceDistance (chargeCorrection left) (chargeCorrection right))
    (sourceDistance left right)
correctionContractsDistinct q1 q1 different = ⊥-elim (different refl)
correctionContractsDistinct q1 q3 different = d1<d2
correctionContractsDistinct q1 q5 different = d1<d2
correctionContractsDistinct q3 q1 different = d1<d2
correctionContractsDistinct q3 q3 different = ⊥-elim (different refl)
correctionContractsDistinct q3 q5 different = d0<d1
correctionContractsDistinct q5 q1 different = d1<d2
correctionContractsDistinct q5 q3 different = d0<d1
correctionContractsDistinct q5 q5 different = ⊥-elim (different refl)

computedSourceContraction :
  SCU.SeparatedFiniteContractionCertificate SourceCharge CellDistance
computedSourceContraction = record
  { step = chargeCorrection
  ; distance = sourceDistance
  ; StrictlySmaller = StrictlySmaller
  ; fixedPoint = q5
  ; fixed = refl
  ; decideEquality = sourceEquality
  ; contractiveDistinct = correctionContractsDistinct
  }

computedSourceUniqueFixedPoint :
  SCU.SeparatedUniqueFixedPointCertificate computedSourceContraction
computedSourceUniqueFixedPoint =
  SCU.certifySeparatedUniqueFixedPoint
    computedSourceContraction strictDistanceIrreflexive

anyComputedSourceFixedPointIsQ5 :
  (q : SourceCharge) →
  chargeCorrection q ≡ q →
  q ≡ q5
anyComputedSourceFixedPointIsQ5 =
  SCU.SeparatedUniqueFixedPointCertificate.unique computedSourceUniqueFixedPoint

------------------------------------------------------------------------
-- Promotion boundary.
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
  PhysicalChargeCorrectionLaw : PhysicalComputedCellResidual
  SameObjectPDEDiscretization : PhysicalComputedCellResidual

-- Firewalls:
-- exhaustive finite source family != physical continuum/device state space.
-- finite population tables != Boltzmann/Fermi-Dirac carrier statistics.
-- synthetic chargeCorrection != physical Gummel/Newton residual update.
-- exact finite contraction here != general physical solver convergence.
