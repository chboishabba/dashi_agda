module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact as JoinFRET
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as NDim

------------------------------------------------------------------------
-- ADENYLATE-KINASE FRET THIRD-AXIS ADEQUACY DEFECT
--
-- The two historical FRET axes form a strictly richer observer when joined,
-- but that does not make the pair a complete N-dimensional conformation chart.
-- Li, Liu & Ji 2015 explicitly characterize AdK states with three collective
-- variables: LID--CORE angle theta1, NMP--CORE angle theta2, and LID--NMP
-- distance dLN.  This owner uses that source fact only to motivate a third-axis
-- query.  The finite collision below is repository-local and is NOT asserted to
-- be a historical simultaneous same-molecule measurement.
------------------------------------------------------------------------

data ThirdAxisWorld : Set where
  lowThetaTwoWorld : ThirdAxisWorld
  highThetaTwoWorld : ThirdAxisWorld

data NmpCoreAngleCoordinate : Set where
  lowThetaTwo : NmpCoreAngleCoordinate
  highThetaTwo : NmpCoreAngleCoordinate

data ThirdAxisQuery : Set where
  askThirdCoordinate : ThirdAxisQuery

data ThirdAxisAnswer : Set where
  lowThetaTwoAnswer : ThirdAxisAnswer
  highThetaTwoAnswer : ThirdAxisAnswer

-- Same two FRET coordinates in the finite witness.
twoFretAxisProjection :
  ThirdAxisWorld →
  JoinFRET.LidNmpCoordinate × JoinFRET.LidCoreCoordinate
twoFretAxisProjection lowThetaTwoWorld =
  JoinFRET.lidNmpOpen , JoinFRET.lidCoreOpen
twoFretAxisProjection highThetaTwoWorld =
  JoinFRET.lidNmpOpen , JoinFRET.lidCoreOpen

thirdCoordinate : ThirdAxisWorld → NmpCoreAngleCoordinate
thirdCoordinate lowThetaTwoWorld = lowThetaTwo
thirdCoordinate highThetaTwoWorld = highThetaTwo

thirdAxisAnswer : ThirdAxisQuery → ThirdAxisWorld → ThirdAxisAnswer
thirdAxisAnswer askThirdCoordinate lowThetaTwoWorld = lowThetaTwoAnswer
thirdAxisAnswer askThirdCoordinate highThetaTwoWorld = highThetaTwoAnswer

thirdAxisSemantics :
  Query.QuerySemantics ThirdAxisWorld ThirdAxisQuery ThirdAxisAnswer
thirdAxisSemantics = Query.querySemantics thirdAxisAnswer

twoFretAxesThirdCoordinateDefect :
  Query.QueryAdequacyDefect
    twoFretAxisProjection
    thirdAxisSemantics
    askThirdCoordinate
twoFretAxesThirdCoordinateDefect =
  Query.queryAdequacyDefect
    lowThetaTwoWorld
    highThetaTwoWorld
    refl
    (λ ())

twoFretAxesNotAdequateForThirdCoordinate :
  Query.AdequateFor
    twoFretAxisProjection
    thirdAxisSemantics
    askThirdCoordinate
  → ⊥
twoFretAxesNotAdequateForThirdCoordinate =
  Query.queryAdequacyDefectBlocksFactorisation
    twoFretAxesThirdCoordinateDefect

------------------------------------------------------------------------
-- Constructive three-axis repair for the declared third-coordinate query.
------------------------------------------------------------------------

record ThreeAxisObservation : Set where
  constructor three-axis-observation
  field
    twoFretAxes : JoinFRET.LidNmpCoordinate × JoinFRET.LidCoreCoordinate
    nmpCoreAngle : NmpCoreAngleCoordinate
open ThreeAxisObservation public

threeAxisProjection : ThirdAxisWorld → ThreeAxisObservation
threeAxisProjection lowThetaTwoWorld =
  three-axis-observation
    (JoinFRET.lidNmpOpen , JoinFRET.lidCoreOpen)
    lowThetaTwo
threeAxisProjection highThetaTwoWorld =
  three-axis-observation
    (JoinFRET.lidNmpOpen , JoinFRET.lidCoreOpen)
    highThetaTwo

threeAxisAnswer : ThreeAxisObservation → ThirdAxisAnswer
threeAxisAnswer (three-axis-observation fretPair lowThetaTwo) = lowThetaTwoAnswer
threeAxisAnswer (three-axis-observation fretPair highThetaTwo) = highThetaTwoAnswer

threeAxisAdequateForThirdCoordinate :
  Query.AdequateFor
    threeAxisProjection
    thirdAxisSemantics
    askThirdCoordinate
threeAxisAdequateForThirdCoordinate =
  Query.factorsForQuery
    threeAxisAnswer
    (λ { lowThetaTwoWorld → refl ; highThetaTwoWorld → refl })

------------------------------------------------------------------------
-- Existing observer-join and NDim donors.
------------------------------------------------------------------------

fretJoinDonor : JoinFRET.AdKFRETObserverJoinBoundary
fretJoinDonor = JoinFRET.canonicalAdKFRETObserverJoinBoundary

ndimGraphDonor : NDim.AdKWeightedGraphBoundary
ndimGraphDonor = NDim.canonicalAdKWeightedGraphBoundary

------------------------------------------------------------------------
-- Source coordinate: three-CV state description, not the finite collision.
------------------------------------------------------------------------

record ThirdAxisSourceCoordinate : Set where
  constructor third-axis-source-coordinate
  field
    label : String
    doi : String
    pmid : String
    pmcid : String
    qid : String
    uniprot : String
    collectiveVariables : String
    directLink : String
    dewey : String
    oeis : String
    sourceRole : String

liLiuJi2015ThreeCvSource : ThirdAxisSourceCoordinate
liLiuJi2015ThreeCvSource =
  third-axis-source-coordinate
    "Li, Liu and Ji 2015 three-CV AdK conformational-state description"
    "10.1016/j.bpj.2015.06.059"
    "26244746"
    "PMC4572606"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "P69441"
    "theta1 LID-CORE angle; theta2 NMP-CORE angle; dLN LID-NMP distance"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    "exact article-level Dewey unresolved"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "pays use of three collective variables to characterize simulated AdK states; does not pay the repository-local same-two-FRET/different-third-coordinate collision"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdKFRETThirdAxisBoundary : Set where
  constructor adk-fret-third-axis-boundary
  field
    twoFretAxisJoinRetainsDeclaredTwoAxes : Bool
    twoFretAxisJoinRetainsDeclaredTwoAxesIsTrue :
      twoFretAxisJoinRetainsDeclaredTwoAxes ≡ true

    twoFretAxisJoinAdequateForThirdCoordinate : Bool
    twoFretAxisJoinAdequateForThirdCoordinateIsFalse :
      twoFretAxisJoinAdequateForThirdCoordinate ≡ false

    threeAxisObserverAdequateForThirdCoordinate : Bool
    threeAxisObserverAdequateForThirdCoordinateIsTrue :
      threeAxisObserverAdequateForThirdCoordinate ≡ true

    sourcePaysThreeCvStateDescription : Bool
    sourcePaysThreeCvStateDescriptionIsTrue :
      sourcePaysThreeCvStateDescription ≡ true

    historicalFretAxesAreIdenticalToThetaOneThetaTwo : Bool
    historicalFretAxesAreIdenticalToThetaOneThetaTwoIsFalse :
      historicalFretAxesAreIdenticalToThetaOneThetaTwo ≡ false

    finiteThirdAxisCollisionIsHistoricalSameMoleculeMeasurement : Bool
    finiteThirdAxisCollisionIsHistoricalSameMoleculeMeasurementIsFalse :
      finiteThirdAxisCollisionIsHistoricalSameMoleculeMeasurement ≡ false

    threeCoordinatesEqualCompleteProteinState : Bool
    threeCoordinatesEqualCompleteProteinStateIsFalse :
      threeCoordinatesEqualCompleteProteinState ≡ false

    addingAxisAutomaticallyImprovesEveryConsumer : Bool
    addingAxisAutomaticallyImprovesEveryConsumerIsFalse :
      addingAxisAutomaticallyImprovesEveryConsumer ≡ false

canonicalAdKFRETThirdAxisBoundary : AdKFRETThirdAxisBoundary
canonicalAdKFRETThirdAxisBoundary =
  adk-fret-third-axis-boundary
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
