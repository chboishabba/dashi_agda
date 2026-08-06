module DASHI.Physics.Closure.NSTriadKNLuoGalerkinScaledFiltrationCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John G. Heywood,
-- "An Error Estimate Uniform in Time for Spectral Galerkin Approximations of
-- the Navier--Stokes Problem", Pacific Journal of Mathematics 98 (1982).
-- DOI: 10.2140/pjm.1982.98.333.
--
-- Roger Temam,
-- "Navier--Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
-- View the checked shell-dependent diagonal Galerkin selection as a filtered
-- object carrying an explicit defect.  This connects the NS limit architecture
-- to the shared scale/defect schema without replacing the physical Sobolev
-- projection-error producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.Common.ScaledFilteredEstimateExact as Scaled
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinDiagonalSelectionExact as Galerkin
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record GalerkinFilteredView : Set where
  constructor galerkinFilteredView
  field
    errorData : Galerkin.PointwiseGalerkinErrorData
    rawShellQuantity : Nat → ℚ
    shellSpacing : Nat → ℚ
    physicalShellQuantity : Nat → ℚ
    shellRepresentsPhysical :
      (shell : Nat) →
      rawShellQuantity shell
      ≡ shellSpacing shell * physicalShellQuantity shell

open GalerkinFilteredView public

shellScaleRepresentation :
  GalerkinFilteredView → Nat → Scaled.ScaleRepresentation
shellScaleRepresentation view shell =
  Scaled.scaleRepresentation
    (rawShellQuantity view shell)
    (shellSpacing view shell)
    (physicalShellQuantity view shell)
    (shellRepresentsPhysical view shell)

shellFilteredLevel :
  GalerkinFilteredView → Nat → Scaled.ScaledFilteredLevel
shellFilteredLevel view shell =
  Scaled.scaledFilteredLevel
    (shellSpacing view shell)
    (shellScaleRepresentation view shell)
    (Galerkin.diagonalError (errorData view) shell)

selectedGalerkinDefectTendsToZero :
  (view : GalerkinFilteredView) →
  Limit.TendsToZero
    (λ shell → Scaled.levelDefect (shellFilteredLevel view shell))
selectedGalerkinDefectTendsToZero view =
  Galerkin.diagonalErrorTendsToZero (errorData view)

record GalerkinScaledBoundary : Set where
  constructor galerkinScaledBoundary
  field
    diagonalSelectionSuppliesPhysicalSobolevError : Set
    diagonalSelectionDoesNotSupplyPhysicalSobolevError :
      diagonalSelectionSuppliesPhysicalSobolevError → Set
    filteredViewProvesGlobalRegularity : Set
    filteredViewDoesNotProveGlobalRegularity :
      filteredViewProvesGlobalRegularity → Set

canonicalGalerkinScaledBoundary : GalerkinScaledBoundary
canonicalGalerkinScaledBoundary =
  galerkinScaledBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
