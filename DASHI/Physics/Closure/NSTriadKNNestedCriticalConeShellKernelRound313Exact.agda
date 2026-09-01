module DASHI.Physics.Closure.NSTriadKNNestedCriticalConeShellKernelRound313Exact where

------------------------------------------------------------------------
-- ROUND313 / NESTED CRITICAL-CONE SHELL KERNEL COORDINATES
--
-- R309--312 show that the hard R301 object has TWO resonant layers:
--
--   a+b=p        inner projected NS forcing
--   p+q=k        outer R307 helicity-slot interaction.
--
-- Collapsing this to one Bony gap would erase exactly the geometry we have
-- just recovered.  This file therefore fixes the shell-coordinate language
-- used by the next row/column estimate.  It keeps independently:
--
--   inner input shells a,b
--   inner output / outer input shell p
--   outer partner shell q
--   final output shell k
--   inner helicity route
--   inner radial multiplier defect
--   inner HH output-null defect
--   outer slot/null defect.
--
-- No estimate is asserted here.  The purpose is to prevent a future Schur
-- bound from silently substituting one generic gap for these different gains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311

data OuterCriticalSubcone : Set where
  outerFLShoulder : OuterCriticalSubcone
  outerHHShoulder : OuterCriticalSubcone
  outerComparable : OuterCriticalSubcone

record NestedCriticalShellCoordinate : Set where
  constructor nested-critical-shell-coordinate
  field
    innerLeftShell innerRightShell : ℚ
    innerOutputShell : ℚ
    outerPartnerShell outerOutputShell : ℚ

    innerRoute : R311.InnerNestedRoute
    outerSubcone : OuterCriticalSubcone

    -- These are independent scalar coordinates.  Their physical formulas and
    -- inequalities are supplied by R120/R232/R307 adapters, not guessed here.
    innerMultiplierDefect : ℚ
    innerOutputNullDefect : ℚ
    outerSlotDefect : ℚ

open NestedCriticalShellCoordinate public

record NestedHeatSchurCell : Set where
  constructor nested-heat-schur-cell
  field
    coordinate : NestedCriticalShellCoordinate
    heatWeight : ℚ
    kernelMagnitudeSquared : ℚ

open NestedHeatSchurCell public

data NestedDiagnosticOutcome : Set where
  integrableAtDeclaredInputs : NestedDiagnosticOutcome
  borderlineNeedsSignedGain : NestedDiagnosticOutcome
  divergentNeedsNewGeometry : NestedDiagnosticOutcome

record NestedShellDiagnostic : Set where
  constructor nested-shell-diagnostic
  field
    coordinate : NestedCriticalShellCoordinate
    rowExponent columnExponent : ℚ
    outcome : NestedDiagnosticOutcome

open NestedShellDiagnostic public

-- Proof-search policy: a failing child may be refined independently; success
-- on another child cannot be used as authority for it.
subconeRoute : OuterCriticalSubcone → Admission.RouteDisposition
subconeRoute outerFLShoulder = Admission.admitted
subconeRoute outerHHShoulder = Admission.admitted
subconeRoute outerComparable = Admission.admitted

round313NestedShellCoordinatesSeparated : Bool
round313NestedShellCoordinatesSeparated = true

round313InnerAndOuterDefectsKeptIndependent : Bool
round313InnerAndOuterDefectsKeptIndependent = true

round313SingleGenericGapUsed : Bool
round313SingleGenericGapUsed = false

round313RowExponentComputed : Bool
round313RowExponentComputed = false

round313ColumnExponentComputed : Bool
round313ColumnExponentComputed = false

round313HeatSchurClosed : Bool
round313HeatSchurClosed = false

round313PackageAClosed : Bool
round313PackageAClosed = false

round313ClayPromotion : Bool
round313ClayPromotion = false
