module DASHI.Physics.QuantumVacuum.CasimirGRNullFocusingBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact as CasimirEC
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Kernel
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.Gravity.NullRaychaudhuriSachsFocusingExact as Focusing

------------------------------------------------------------------------
-- CASIMIR LOCAL NEC -> SEMICLASSICAL GR / NULL-FOCUSING BOUNDARY
--
-- The preceding Casimir owner proves a local QFT statement on the ideal plate
-- system.  The existing GR focusing owner already contains the exact firewall
-- that NEC is not itself the null-convergence condition unless an Einstein-
-- equation translation is supplied.  This module makes that composition
-- explicit for the Casimir object rather than inventing another GR calculus.
------------------------------------------------------------------------

existingNECNullConvergenceFirewall :
  Focusing.nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquation
    Focusing.canonicalNullFocusingCompositionBoundary
  ≡ true
existingNECNullConvergenceFirewall =
  Focusing.nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquationIsTrue
    Focusing.canonicalNullFocusingCompositionBoundary

casimirLocalNECIsViolated :
  CasimirEC.casimirNEC ≡ CasimirEC.conditionViolated
casimirLocalNECIsViolated = refl

data CasimirNECViolationAutomaticallyProducesNegativeNullRicci : Set where
data CasimirNECViolationAutomaticallyProducesNullDefocusing : Set where
data CasimirNegativeActiveStressAutomaticallyProducesRepulsiveGeometry : Set where

casimirNECNeedsSemiclassicalEinsteinWeld :
  CasimirNECViolationAutomaticallyProducesNegativeNullRicci → ⊥
casimirNECNeedsSemiclassicalEinsteinWeld ()

casimirNECNeedsCurvatureAndOpticalWeld :
  CasimirNECViolationAutomaticallyProducesNullDefocusing → ⊥
casimirNECNeedsCurvatureAndOpticalWeld ()

negativeActiveStressNeedsMetricSolution :
  CasimirNegativeActiveStressAutomaticallyProducesRepulsiveGeometry → ⊥
negativeActiveStressNeedsMetricSolution ()

------------------------------------------------------------------------
-- Proof-relevant same-object semiclassical weld.
--
-- A future physical/semiclassical instance must carry the exact renormalized
-- stress object all the way into the gravitational source equation.  None of
-- these fields is supplied merely by the local energy-condition violation.
------------------------------------------------------------------------

record CasimirSemiclassicalGravityWeld
    (kernel : Kernel.CasimirScalarModel)
    (d : Q.Length) : Set₁ where
  field
    pressureWeld : CasimirEC.BrownMaclayKernelPressureWeld kernel d

    RenormalizedStressExpectation : Set
    renormalizedStressExpectation : RenormalizedStressExpectation

    SameStressObjectAcrossQFTAndGravity : Set
    sameStressObjectAcrossQFTAndGravity : SameStressObjectAcrossQFTAndGravity

    SemiclassicalEinsteinEquationReceipt : Set
    semiclassicalEinsteinEquationReceipt : SemiclassicalEinsteinEquationReceipt

    CovariantConservationReceipt : Set
    covariantConservationReceipt : CovariantConservationReceipt

    NullRicciContractionReceipt : Set
    nullRicciContractionReceipt : NullRicciContractionReceipt

    OpticalCongruenceReceipt : Set
    opticalCongruenceReceipt : OpticalCongruenceReceipt

    BackreactionMeasuredOrCalibrated : Set
    backreactionMeasuredOrCalibrated : BackreactionMeasuredOrCalibrated

    reading : String

open CasimirSemiclassicalGravityWeld public

------------------------------------------------------------------------
-- Machine-readable max-cut boundary.
------------------------------------------------------------------------

record CasimirGRNullFocusingBoundary : Set where
  constructor casimir-gr-null-focusing-boundary
  field
    localCasimirNECViolationOwned : Bool
    arbitraryNullDirectionFormulaOwned : Bool
    existingGRNECNullConvergenceFirewallReused : Bool

    semiclassicalEinsteinEquationPaid : Bool
    sameStressObjectAcrossQFTAndGravityPaid : Bool
    covariantConservationPaid : Bool
    nullRicciContractionPaid : Bool
    opticalDefocusingPaid : Bool
    measuredBackreactionPaid : Bool

open CasimirGRNullFocusingBoundary public

canonicalCasimirGRNullFocusingBoundary : CasimirGRNullFocusingBoundary
canonicalCasimirGRNullFocusingBoundary =
  casimir-gr-null-focusing-boundary
    true true true
    false false false false false false

casimirGRNullFocusingReading : String
casimirGRNullFocusingReading =
  "Casimir supplies a local renormalized QFT stress with pointwise NEC violation, including T(k,k)=-4 C n_perp^2 on the ideal plate system. The existing GR firewall is reused exactly: NEC is not null convergence without an Einstein-equation translation. A physical GR promotion still requires a same-object renormalized stress expectation, semiclassical Einstein equation, conservation, null-Ricci contraction, optical congruence, and measured/calibrated backreaction."
