{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.FinitePoissonGreenCrossPollinationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as YM
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using
  (side4)

------------------------------------------------------------------------
-- ACTUAL REPO PHYSICS REUSE
--
-- The Yang--Mills/Balaban lane already owns an exact rational side-4 periodic
-- scalar Green operator and proves that it is a right inverse for the configured
-- finite operator (local Laplacian + global-average mode).
--
-- Semiconductor electrostatics can reuse that theorem as an exact finite
-- calibration of the pattern "source -> Green solve -> operator recovers source".
-- It is NOT yet the physical semiconductor Poisson boundary-value problem:
-- device geometry, dielectric coefficients, contacts and boundary conditions are
-- different objects and remain explicit residuals below.
------------------------------------------------------------------------

ymConfiguredGreenRightInverse :
  (source : SiteField side4) →
  (row : PhysicalBlockL side4) →
  YM.configuredSiteOperator (YM.scalarGreen source) row ≡ source row
ymConfiguredGreenRightInverse = YM.configuredSiteGreenRightInverse

------------------------------------------------------------------------
-- A tiny semiconductor-specific Poisson stencil, kept division/subtraction-free.
--
--     2 phi_c - phi_l - phi_r = rho
--
-- is represented as
--
--     phi_l + phi_r + rho = phi_c + phi_c.
------------------------------------------------------------------------

record ThreePointPoissonCell : Set where
  constructor threePointPoissonCell
  field
    leftPotential   : Nat
    centrePotential : Nat
    rightPotential  : Nat
    sourceCharge    : Nat
    poissonBalance  :
      leftPotential + (rightPotential + sourceCharge)
      ≡ centrePotential + centrePotential

open ThreePointPoissonCell public

syntheticPoissonCell : ThreePointPoissonCell
syntheticPoissonCell = threePointPoissonCell 2 5 3 5 refl

------------------------------------------------------------------------
-- Same charge coordinate does not determine the potential solution without
-- boundary/geometry data.
------------------------------------------------------------------------

poissonA : ThreePointPoissonCell
poissonA = threePointPoissonCell 2 5 3 5 refl

poissonB : ThreePointPoissonCell
poissonB = threePointPoissonCell 4 6 3 5 refl

sameSourceCharge : sourceCharge poissonA ≡ sourceCharge poissonB
sameSourceCharge = refl

data ⊥ : Set where

sameChargeDoesNotDeterminePotential :
  centrePotential poissonA ≡ centrePotential poissonB → ⊥
sameChargeDoesNotDeterminePotential ()

------------------------------------------------------------------------
-- Boundary between reused operator mathematics and physical device authority.
------------------------------------------------------------------------

data PoissonResidual : Set where
  DeviceGeometry             : PoissonResidual
  PermittivityField          : PoissonResidual
  FixedChargeDistribution    : PoissonResidual
  MobileChargeStatistics     : PoissonResidual
  GateBoundaryCondition      : PoissonResidual
  SourceDrainBoundary        : PoissonResidual
  QuantumConfinementCharge   : PoissonResidual
  NonuniformMeshOperator     : PoissonResidual
  PhysicalDeviceGreenFunction : PoissonResidual

-- Firewall:
-- exact periodic YM scalar Green inverse != semiconductor device Poisson solve.
