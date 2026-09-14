module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverLocalRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoExact as Pareto

------------------------------------------------------------------------
-- ADENYLATE-KINASE OBSERVER LOCAL REPAIR
--
-- The parent Pareto owner already proves that joinedTwo is too coarse for the
-- declared third-coordinate consumer and that threeAxis is the minimum eligible
-- member of the finite observer family.  This owner closes the missing dynamic
-- proof step in the selection loop:
--
--   consumer counterexample
--     -> declared local refinement joinedTwo -> threeAxis
--     -> repaired admissibility
--     -> repaired consumer adequacy
--     -> eligible repaired observer.
--
-- The construction reuses LocalRefinementRepair directly.  It does not create
-- a new observer-selection calculus, experimental datum, or protein-state claim.
------------------------------------------------------------------------

joinedTwoToThreeAxisRepair :
  MDL.LocalRefinementRepair
    Pareto.thirdAxisProblem
    Pareto.joinedTwo
    Pareto.threeAxis
joinedTwoToThreeAxisRepair =
  MDL.localRefinementRepair
    Pareto.twoAxisThirdConsumerCounterexample
    Pareto.joinedToThree
    tt
    tt
    "reopen the retained NMP-CORE third coordinate over the existing two-axis AdK observer"

repairProvidesThreeAxisEligibility :
  MDL.Eligible Pareto.thirdAxisProblem Pareto.threeAxis
repairProvidesThreeAxisEligibility =
  MDL.repairProvidesEligibleRefinement joinedTwoToThreeAxisRepair

------------------------------------------------------------------------
-- Locality: the refinement stays inside the declared AdK observer family.
------------------------------------------------------------------------

data ObserverFamilyAddress : Set where
  adkObserverFamily : ObserverFamilyAddress

observerFamilyNeighbourhood :
  MDL.RefinementNeighbourhood Pareto.thirdAxisProblem
observerFamilyNeighbourhood =
  MDL.refinementNeighbourhood
    ObserverFamilyAddress
    (λ model → adkObserverFamily)
    (λ left right → ⊤)
    (λ coarse fine refinement → tt)
    "finite AdK observer family: axis-erased / single-axis / joined-two / three-axis"

repairStaysInObserverFamily :
  MDL.sameNeighbourhood observerFamilyNeighbourhood
    (MDL.address observerFamilyNeighbourhood Pareto.joinedTwo)
    (MDL.address observerFamilyNeighbourhood Pareto.threeAxis)
repairStaysInObserverFamily =
  MDL.repairStaysInDeclaredNeighbourhood
    observerFamilyNeighbourhood
    joinedTwoToThreeAxisRepair

------------------------------------------------------------------------
-- Agreement with the already-proved finite selection result.
--
-- The repair yields the same concrete model selected by the parent minimum-
-- eligible proof.  This is agreement of repository objects, not a claim that
-- a physical experiment was automatically optimized.
------------------------------------------------------------------------

repairedObserver : Pareto.ObserverModel
repairedObserver = Pareto.threeAxis

minimalSelectedObserver : Pareto.ObserverModel
minimalSelectedObserver = Pareto.threeAxis

repairSelectionAgreement : repairedObserver ≡ minimalSelectedObserver
repairSelectionAgreement = refl

parentMinimalEligibility :
  MDL.Eligible Pareto.thirdAxisProblem minimalSelectedObserver
parentMinimalEligibility = Pareto.thirdAxisSelectedIsEligible

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKObserverLocalRepairBoundary : Set where
  constructor adk-observer-local-repair-boundary
  field
    thirdAxisCounterexampleDrivesLocalRepair : Bool
    thirdAxisCounterexampleDrivesLocalRepairIsTrue :
      thirdAxisCounterexampleDrivesLocalRepair ≡ true

    repairProvidesEligibleThreeAxisObserver : Bool
    repairProvidesEligibleThreeAxisObserverIsTrue :
      repairProvidesEligibleThreeAxisObserver ≡ true

    repairStaysInsideDeclaredObserverFamily : Bool
    repairStaysInsideDeclaredObserverFamilyIsTrue :
      repairStaysInsideDeclaredObserverFamily ≡ true

    repairedObserverAgreesWithThirdAxisMinimalEligibleSelection : Bool
    repairedObserverAgreesWithThirdAxisMinimalEligibleSelectionIsTrue :
      repairedObserverAgreesWithThirdAxisMinimalEligibleSelection ≡ true

    repairInventsExperimentalMeasurement : Bool
    repairInventsExperimentalMeasurementIsFalse :
      repairInventsExperimentalMeasurement ≡ false

    localRepairMeansCompleteProteinRecovery : Bool
    localRepairMeansCompleteProteinRecoveryIsFalse :
      localRepairMeansCompleteProteinRecovery ≡ false

    repairMakesEveryRicherObserverPreferable : Bool
    repairMakesEveryRicherObserverPreferableIsFalse :
      repairMakesEveryRicherObserverPreferable ≡ false

canonicalAdKObserverLocalRepairBoundary : AdKObserverLocalRepairBoundary
canonicalAdKObserverLocalRepairBoundary =
  adk-observer-local-repair-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
