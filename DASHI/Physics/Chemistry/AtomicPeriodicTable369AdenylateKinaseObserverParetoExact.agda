module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact as JoinFRET
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact as Third

------------------------------------------------------------------------
-- ADENYLATE-KINASE OBSERVER PARETO SELECTION
--
-- The AdK observer ladder now contains several increasingly rich observation
-- surfaces.  Richer is not intrinsically better: the smallest admissible
-- observer depends on the consumer query.  This owner reuses the repo-native
-- admissible-consumer MDL / NDim Pareto machinery rather than creating a new
-- ranking calculus.
--
--   two-axis consumer:  joinedTwo is the minimum eligible observer;
--   third-axis consumer: joinedTwo is ineligible, threeAxis is minimum eligible.
--
-- Description length is therefore applied only *after* consumer adequacy.  It
-- is not physical truth and cannot promote an inadequate projection.
------------------------------------------------------------------------

data ObserverModel : Set where
  axisErased : ObserverModel
  lidNmpOnly : ObserverModel
  lidCoreOnly : ObserverModel
  joinedTwo : ObserverModel
  threeAxis : ObserverModel

observerReference : ObserverModel → String
observerReference axisErased = "axis-erased AdK observation"
observerReference lidNmpOnly = "single LID-NMP coordinate"
observerReference lidCoreOnly = "single LID-CORE coordinate"
observerReference joinedTwo = "joined LID-NMP x LID-CORE observer"
observerReference threeAxis = "joined two-axis observer plus NMP-CORE angle coordinate"

observerDescriptionLength : ObserverModel → Nat
observerDescriptionLength axisErased = 0
observerDescriptionLength lidNmpOnly = 1
observerDescriptionLength lidCoreOnly = 1
observerDescriptionLength joinedTwo = 2
observerDescriptionLength threeAxis = 3

allObserversAdmissible : ObserverModel → Set
allObserversAdmissible model = ⊤

-- Adequacy for a consumer that explicitly requires both historical FRET axes.
twoAxisAdequate : ObserverModel → Set
twoAxisAdequate axisErased = ⊥
twoAxisAdequate lidNmpOnly = ⊥
twoAxisAdequate lidCoreOnly = ⊥
twoAxisAdequate joinedTwo = ⊤
twoAxisAdequate threeAxis = ⊤

-- Adequacy for the declared third-coordinate query from the parent owner.
thirdAxisAdequate : ObserverModel → Set
thirdAxisAdequate axisErased = ⊥
thirdAxisAdequate lidNmpOnly = ⊥
thirdAxisAdequate lidCoreOnly = ⊥
thirdAxisAdequate joinedTwo = ⊥
thirdAxisAdequate threeAxis = ⊤

data ObserverRefines : ObserverModel → ObserverModel → Set where
  erasedToLidNmp : ObserverRefines axisErased lidNmpOnly
  erasedToLidCore : ObserverRefines axisErased lidCoreOnly
  lidNmpToJoined : ObserverRefines lidNmpOnly joinedTwo
  lidCoreToJoined : ObserverRefines lidCoreOnly joinedTwo
  joinedToThree : ObserverRefines joinedTwo threeAxis

------------------------------------------------------------------------
-- Two consumer-indexed MDL problems over the same observer family.
------------------------------------------------------------------------

twoAxisProblem : MDL.ConsumerMDLProblem
twoAxisProblem =
  MDL.consumerMDLProblem
    ObserverModel
    allObserversAdmissible
    twoAxisAdequate
    observerDescriptionLength
    ObserverRefines
    observerReference
    "one code unit per retained declared observer coordinate"
    "consumer requires both LID-NMP and LID-CORE observation axes"

thirdAxisProblem : MDL.ConsumerMDLProblem
thirdAxisProblem =
  MDL.consumerMDLProblem
    ObserverModel
    allObserversAdmissible
    thirdAxisAdequate
    observerDescriptionLength
    ObserverRefines
    observerReference
    "one code unit per retained declared observer coordinate"
    "consumer asks the NMP-CORE third-coordinate query"

------------------------------------------------------------------------
-- Exact minimum eligible descriptions.
------------------------------------------------------------------------

twoAxisNoLongerThanAnyEligible :
  (candidate : ObserverModel) →
  allObserversAdmissible candidate →
  twoAxisAdequate candidate →
  observerDescriptionLength joinedTwo ≤ observerDescriptionLength candidate
twoAxisNoLongerThanAnyEligible axisErased admissible ()
twoAxisNoLongerThanAnyEligible lidNmpOnly admissible ()
twoAxisNoLongerThanAnyEligible lidCoreOnly admissible ()
twoAxisNoLongerThanAnyEligible joinedTwo admissible adequate = ≤-refl
twoAxisNoLongerThanAnyEligible threeAxis admissible adequate =
  s≤s (s≤s z≤n)

twoAxisMinimalEligible :
  MDL.MinimalEligibleDescription twoAxisProblem joinedTwo
twoAxisMinimalEligible =
  MDL.minimalEligibleDescription
    tt
    tt
    twoAxisNoLongerThanAnyEligible
    "joined two-axis observer is shortest among observers eligible for the declared two-axis consumer"

thirdAxisNoLongerThanAnyEligible :
  (candidate : ObserverModel) →
  allObserversAdmissible candidate →
  thirdAxisAdequate candidate →
  observerDescriptionLength threeAxis ≤ observerDescriptionLength candidate
thirdAxisNoLongerThanAnyEligible axisErased admissible ()
thirdAxisNoLongerThanAnyEligible lidNmpOnly admissible ()
thirdAxisNoLongerThanAnyEligible lidCoreOnly admissible ()
thirdAxisNoLongerThanAnyEligible joinedTwo admissible ()
thirdAxisNoLongerThanAnyEligible threeAxis admissible adequate = ≤-refl

thirdAxisMinimalEligible :
  MDL.MinimalEligibleDescription thirdAxisProblem threeAxis
thirdAxisMinimalEligible =
  MDL.minimalEligibleDescription
    tt
    tt
    thirdAxisNoLongerThanAnyEligible
    "three-axis observer is the only eligible member of this finite family for the declared third-coordinate consumer"

twoAxisSelectedIsEligible : MDL.Eligible twoAxisProblem joinedTwo
twoAxisSelectedIsEligible =
  MDL.minimalDescriptionIsEligible twoAxisMinimalEligible

thirdAxisSelectedIsEligible : MDL.Eligible thirdAxisProblem threeAxis
thirdAxisSelectedIsEligible =
  MDL.minimalDescriptionIsEligible thirdAxisMinimalEligible

------------------------------------------------------------------------
-- Explicit inadequacy receipt: compactness cannot rescue the two-axis observer
-- for the third-coordinate consumer.
------------------------------------------------------------------------

twoAxisThirdConsumerCounterexample :
  MDL.ConsumerCounterexample thirdAxisProblem joinedTwo
twoAxisThirdConsumerCounterexample =
  MDL.consumerCounterexample
    ⊤
    tt
    (λ impossible → impossible)
    "joinedTwo erases the declared NMP-CORE third coordinate"
    "AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact.twoFretAxesThirdCoordinateDefect"

joinedTwoExcludedFromThirdAxisEligibility :
  MDL.Eligible thirdAxisProblem joinedTwo → ⊥
joinedTwoExcludedFromThirdAxisEligibility =
  MDL.counterexampleExcludesEligibility twoAxisThirdConsumerCounterexample

------------------------------------------------------------------------
-- NDim cost view.  These costs are repository-local design coordinates, not
-- experimental measurements.  They make the Pareto semantics explicit while
-- keeping consumer eligibility logically prior to ranking.
------------------------------------------------------------------------

data ObserverCostAxis : Set where
  retainedCoordinateCount : ObserverCostAxis
  acquisitionBurden : ObserverCostAxis

observerCost : ObserverCostAxis → ObserverModel → Nat
observerCost retainedCoordinateCount model = observerDescriptionLength model
observerCost acquisitionBurden axisErased = 0
observerCost acquisitionBurden lidNmpOnly = 1
observerCost acquisitionBurden lidCoreOnly = 1
observerCost acquisitionBurden joinedTwo = 3
observerCost acquisitionBurden threeAxis = 5

observerCostReference : ObserverCostAxis → String
observerCostReference retainedCoordinateCount =
  "repository-local retained-coordinate count"
observerCostReference acquisitionBurden =
  "repository-local relative acquisition/design burden; not an empirical cost"

twoAxisCostHyperfabric : MDL.CostHyperfabric twoAxisProblem
twoAxisCostHyperfabric =
  MDL.costHyperfabric ObserverCostAxis observerCost observerCostReference

twoAxisNDimParetoView : NDim.NDimParetoView twoAxisCostHyperfabric
twoAxisNDimParetoView =
  NDim.ndimParetoView
    2
    "two declared design-cost axes: retained coordinates and acquisition burden"
    observerCostReference
    true
    "no scalarized score required"

------------------------------------------------------------------------
-- Donors and promotion boundary.
------------------------------------------------------------------------

fretJoinDonor : JoinFRET.AdKFRETObserverJoinBoundary
fretJoinDonor = JoinFRET.canonicalAdKFRETObserverJoinBoundary

thirdAxisDonor : Third.AdKFRETThirdAxisBoundary
thirdAxisDonor = Third.canonicalAdKFRETThirdAxisBoundary

mdlBoundaryDonor : MDL.AdmissibleConsumerMDLBoundary
mdlBoundaryDonor = MDL.canonicalAdmissibleConsumerMDLBoundary

ndimParetoBoundaryDonor : NDim.NDimParetoHyperfabricBoundary
ndimParetoBoundaryDonor = NDim.canonicalNDimParetoHyperfabricBoundary

record AdKObserverParetoBoundary : Set where
  constructor adk-observer-pareto-boundary
  field
    joinedTwoIsMinimalEligibleForTwoAxisConsumer : Bool
    joinedTwoIsMinimalEligibleForTwoAxisConsumerIsTrue :
      joinedTwoIsMinimalEligibleForTwoAxisConsumer ≡ true

    threeAxisAutomaticallyPreferredForTwoAxisConsumer : Bool
    threeAxisAutomaticallyPreferredForTwoAxisConsumerIsFalse :
      threeAxisAutomaticallyPreferredForTwoAxisConsumer ≡ false

    twoAxisJoinEligibleForThirdAxisConsumer : Bool
    twoAxisJoinEligibleForThirdAxisConsumerIsFalse :
      twoAxisJoinEligibleForThirdAxisConsumer ≡ false

    threeAxisIsMinimalEligibleForThirdAxisConsumer : Bool
    threeAxisIsMinimalEligibleForThirdAxisConsumerIsTrue :
      threeAxisIsMinimalEligibleForThirdAxisConsumer ≡ true

    eligibilityPrecedesDescriptionLengthRanking : Bool
    eligibilityPrecedesDescriptionLengthRankingIsTrue :
      eligibilityPrecedesDescriptionLengthRanking ≡ true

    shorterObserverMeansPhysicalTruth : Bool
    shorterObserverMeansPhysicalTruthIsFalse :
      shorterObserverMeansPhysicalTruth ≡ false

    moreAxesImproveEveryConsumer : Bool
    moreAxesImproveEveryConsumerIsFalse :
      moreAxesImproveEveryConsumer ≡ false

    paretoCostAxesAreExperimentalMeasurements : Bool
    paretoCostAxesAreExperimentalMeasurementsIsFalse :
      paretoCostAxesAreExperimentalMeasurements ≡ false

    minimumEligibleObserverEqualsCompleteProteinState : Bool
    minimumEligibleObserverEqualsCompleteProteinStateIsFalse :
      minimumEligibleObserverEqualsCompleteProteinState ≡ false

canonicalAdKObserverParetoBoundary : AdKObserverParetoBoundary
canonicalAdKObserverParetoBoundary =
  adk-observer-pareto-boundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
