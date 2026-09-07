{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopSGPopulationJacobianExact where

------------------------------------------------------------------------
-- EXACT POPULATION JACOBIAN FOR A FIXED-DROP BISHOP SG FACE
--
-- On the current semiconductor chart the normalized potential drop is fixed at
-- psi = 1/2.  Therefore the Bernoulli weights are fixed while the carrier
-- populations vary.  The SG face map is exactly affine-linear in those two
-- population coordinates:
--
--   J(uL,uR) = uL B(psi) - uR B(-psi).
--
-- Hence its population Jacobian is not an approximation or a postulated
-- derivative.  It is the exact finite-difference operator
--
--   dJ = B(psi) duL - B(-psi) duR.
--
-- The nonlinear potential/drop derivative is intentionally kept separate.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as Unit
import DASHI.Physics.Semiconductor.Device.BishopConcreteBernoulliPairExact as Bernoulli
import DASHI.Physics.Semiconductor.Device.BishopConcreteScharfetterGummelFaceFluxExact as SG

------------------------------------------------------------------------
-- Fixed-drop face constructor.
------------------------------------------------------------------------

faceAt :
  (drop : BishopReal.ℝ) →
  Unit.PositiveUnitIntervalPoint drop →
  BishopReal.ℝ → BishopReal.ℝ →
  SG.ConcreteBishopFaceState
faceAt drop chart left right = record
  { SG.leftPopulation = left
  ; SG.rightPopulation = right
  ; SG.drop = drop
  ; SG.dropInPositiveUnitInterval = chart
  }

forwardCoefficient :
  ∀ {drop} → Unit.PositiveUnitIntervalPoint drop → BishopReal.ℝ
forwardCoefficient = Bernoulli.forwardWeight

backwardCoefficient :
  ∀ {drop} → Unit.PositiveUnitIntervalPoint drop → BishopReal.ℝ
backwardCoefficient = Bernoulli.backwardWeight

rightJacobianCoefficient :
  ∀ {drop} → Unit.PositiveUnitIntervalPoint drop → BishopReal.ℝ
rightJacobianCoefficient chart = BishopReal.- (backwardCoefficient chart)

------------------------------------------------------------------------
-- Population perturbation at fixed drop.
------------------------------------------------------------------------

record FixedDropPopulationPerturbation
    (drop : BishopReal.ℝ)
    (chart : Unit.PositiveUnitIntervalPoint drop) : Set where
  constructor fixedDropPopulationPerturbation
  field
    leftBase : BishopReal.ℝ
    rightBase : BishopReal.ℝ
    leftDelta : BishopReal.ℝ
    rightDelta : BishopReal.ℝ

open FixedDropPopulationPerturbation public

baseFace :
  ∀ {drop chart} →
  FixedDropPopulationPerturbation drop chart →
  SG.ConcreteBishopFaceState
baseFace {drop} {chart} perturbation =
  faceAt drop chart
    (leftBase perturbation)
    (rightBase perturbation)

perturbedFace :
  ∀ {drop chart} →
  FixedDropPopulationPerturbation drop chart →
  SG.ConcreteBishopFaceState
perturbedFace {drop} {chart} perturbation =
  faceAt drop chart
    (BishopReal._+_ (leftBase perturbation) (leftDelta perturbation))
    (BishopReal._+_ (rightBase perturbation) (rightDelta perturbation))

populationJacobianAction :
  ∀ {drop chart} →
  FixedDropPopulationPerturbation drop chart →
  BishopReal.ℝ
populationJacobianAction {chart = chart} perturbation =
  BishopReal._+_
    (BishopReal._*_
      (leftDelta perturbation)
      (forwardCoefficient chart))
    (BishopReal._*_
      (rightDelta perturbation)
      (rightJacobianCoefficient chart))

------------------------------------------------------------------------
-- Exact finite-difference theorem.
------------------------------------------------------------------------

populationFiniteDifferenceIsJacobianAction :
  ∀ {drop chart} →
  (perturbation : FixedDropPopulationPerturbation drop chart) →
  BishopReal._≃_
    (BishopReal._-_
      (SG.concreteBishopSGFaceFlux (perturbedFace perturbation))
      (SG.concreteBishopSGFaceFlux (baseFace perturbation)))
    (populationJacobianAction perturbation)
populationFiniteDifferenceIsJacobianAction {chart = chart} perturbation =
  let
    l = leftBase perturbation
    r = rightBase perturbation
    dl = leftDelta perturbation
    dr = rightDelta perturbation
    wf = forwardCoefficient chart
    wb = backwardCoefficient chart
    open BishopP.ℝ-Solver
  in
  solve 6
    (λ l′ r′ dl′ dr′ wf′ wb′ →
      ((((l′ ⊕ dl′) ⊗ wf′) ⊖ ((r′ ⊕ dr′) ⊗ wb′))
        ⊖ ((l′ ⊗ wf′) ⊖ (r′ ⊗ wb′)))
      ⊜ ((dl′ ⊗ wf′) ⊕ (dr′ ⊗ (⊝ wb′))))
    BishopP.≃-refl l r dl dr wf wb

------------------------------------------------------------------------
-- Sparse row certificate.  Only the two population coordinates of the face
-- participate in this block.
------------------------------------------------------------------------

record PopulationJacobianRow
    (drop : BishopReal.ℝ)
    (chart : Unit.PositiveUnitIntervalPoint drop) : Set where
  constructor populationJacobianRow
  field
    dJdLeftPopulation : BishopReal.ℝ
    dJdRightPopulation : BishopReal.ℝ
    leftCoefficientExact :
      BishopReal._≃_ dJdLeftPopulation (forwardCoefficient chart)
    rightCoefficientExact :
      BishopReal._≃_ dJdRightPopulation (rightJacobianCoefficient chart)

open PopulationJacobianRow public

exactPopulationJacobianRow :
  ∀ {drop} (chart : Unit.PositiveUnitIntervalPoint drop) →
  PopulationJacobianRow drop chart
exactPopulationJacobianRow chart = record
  { dJdLeftPopulation = forwardCoefficient chart
  ; dJdRightPopulation = rightJacobianCoefficient chart
  ; leftCoefficientExact = BishopP.≃-refl
  ; rightCoefficientExact = BishopP.≃-refl
  }

------------------------------------------------------------------------
-- Firewalls / remaining nonlinear block.
------------------------------------------------------------------------

data SGJacobianResidualLeaf : Set where
  PotentialDropDerivative : SGJacobianResidualLeaf
  ThermalVoltageDerivative : SGJacobianResidualLeaf
  PhysicalPopulationScaling : SGJacobianResidualLeaf
  DimensionalPrefactorDerivative : SGJacobianResidualLeaf

-- Exact population linearity at fixed drop != the full semiconductor Jacobian.
-- In particular this theorem does not differentiate B(psi) with respect to psi
-- or the Poisson/statistics maps with respect to the device source state.
