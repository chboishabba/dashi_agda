module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverLocalRepairValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverLocalRepairExact as R

------------------------------------------------------------------------
-- RED/GREEN validation root: the third-axis counterexample must drive a
-- concrete local refinement repair before ranking resumes.
------------------------------------------------------------------------

repairRegression :
  R.AdKObserverLocalRepairBoundary.thirdAxisCounterexampleDrivesLocalRepair
    R.canonicalAdKObserverLocalRepairBoundary
  ≡ true
  × R.AdKObserverLocalRepairBoundary.repairProvidesEligibleThreeAxisObserver
    R.canonicalAdKObserverLocalRepairBoundary
  ≡ true
repairRegression = refl , refl

localityRegression :
  R.AdKObserverLocalRepairBoundary.repairStaysInsideDeclaredObserverFamily
    R.canonicalAdKObserverLocalRepairBoundary
  ≡ true
  × R.AdKObserverLocalRepairBoundary.repairInventsExperimentalMeasurement
    R.canonicalAdKObserverLocalRepairBoundary
  ≡ false
localityRegression = refl , refl

selectionRegression :
  R.AdKObserverLocalRepairBoundary.repairedObserverAgreesWithThirdAxisMinimalEligibleSelection
    R.canonicalAdKObserverLocalRepairBoundary
  ≡ true
  × R.AdKObserverLocalRepairBoundary.localRepairMeansCompleteProteinRecovery
    R.canonicalAdKObserverLocalRepairBoundary
  ≡ false
selectionRegression = refl , refl
