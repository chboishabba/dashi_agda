module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverAxisExact as FRET

------------------------------------------------------------------------
-- ADENYLATE-KINASE FRET OBSERVER-AXIS JOIN
--
-- The historical AdK FRET experiments retained by the parent owner observe
-- different one-dimensional geometric coordinates: LID--NMP and LID--CORE.
-- RequiredObserverAxisJoinAdequacyExact already owns the generic product law:
-- an observer retaining both required axes retains their joint pair, while a
-- collision on either missing axis blocks a claim to retain both.
--
-- This owner specializes that theorem to a finite AdK-shaped observer-design
-- fixture.  It does NOT claim that the two historical experiments made
-- simultaneous measurements on one molecule, nor that two distances recover a
-- complete protein conformation.
------------------------------------------------------------------------

data AdKJointState : Set where
  openOpen : AdKJointState
  openClosed : AdKJointState
  closedOpen : AdKJointState
  closedClosed : AdKJointState

data LidNmpCoordinate : Set where
  lidNmpOpen : LidNmpCoordinate
  lidNmpClosed : LidNmpCoordinate

data LidCoreCoordinate : Set where
  lidCoreOpen : LidCoreCoordinate
  lidCoreClosed : LidCoreCoordinate

lidNmpProjection : AdKJointState → LidNmpCoordinate
lidNmpProjection openOpen = lidNmpOpen
lidNmpProjection openClosed = lidNmpOpen
lidNmpProjection closedOpen = lidNmpClosed
lidNmpProjection closedClosed = lidNmpClosed

lidCoreProjection : AdKJointState → LidCoreCoordinate
lidCoreProjection openOpen = lidCoreOpen
lidCoreProjection openClosed = lidCoreClosed
lidCoreProjection closedOpen = lidCoreOpen
lidCoreProjection closedClosed = lidCoreClosed

joinedProjection : AdKJointState → LidNmpCoordinate × LidCoreCoordinate
joinedProjection = Join.jointAxis lidNmpProjection lidCoreProjection

------------------------------------------------------------------------
-- Each single axis can collide while the other axis changes.
------------------------------------------------------------------------

lidNmpMissesLidCore :
  NF.NonFactorabilityWitness lidNmpProjection lidCoreProjection
lidNmpMissesLidCore =
  NF.nonFactorabilityWitness
    openOpen
    openClosed
    refl
    (λ ())

lidCoreMissesLidNmp :
  NF.NonFactorabilityWitness lidCoreProjection lidNmpProjection
lidCoreMissesLidNmp =
  NF.nonFactorabilityWitness
    openOpen
    closedOpen
    refl
    (λ ())

lidNmpAloneCannotRetainBoth :
  Join.RetainsBothRequiredAxes
    lidNmpProjection
    lidNmpProjection
    lidCoreProjection
  → ⊥
lidNmpAloneCannotRetainBoth =
  Join.rightAxisDefectBlocksRetainingBoth lidNmpMissesLidCore

lidCoreAloneCannotRetainBoth :
  Join.RetainsBothRequiredAxes
    lidCoreProjection
    lidNmpProjection
    lidCoreProjection
  → ⊥
lidCoreAloneCannotRetainBoth =
  Join.leftAxisDefectBlocksRetainingBoth lidCoreMissesLidNmp

------------------------------------------------------------------------
-- The joint observer constructively retains both declared axes.
------------------------------------------------------------------------

joinedObserverRetainsBoth :
  Join.RetainsBothRequiredAxes
    joinedProjection
    lidNmpProjection
    lidCoreProjection
joinedObserverRetainsBoth =
  Join.retainsBothRequiredAxes
    (Join.jointRetainsLeft lidNmpProjection lidCoreProjection)
    (Join.jointRetainsRight lidNmpProjection lidCoreProjection)

joinedObserverRetainsJoint :
  Join.RetainsAxis
    joinedProjection
    (Join.jointAxis lidNmpProjection lidCoreProjection)
joinedObserverRetainsJoint =
  Join.retainsBothGivesJointFactorisation joinedObserverRetainsBoth

------------------------------------------------------------------------
-- Parent donor: this specializes the already source-bounded FRET-axis owner.
------------------------------------------------------------------------

fretAxisDonor : FRET.AdKFRETObserverBoundary
fretAxisDonor = FRET.canonicalAdKFRETObserverBoundary

genericJoinDonor : Join.RequiredObserverAxisJoinBoundary
genericJoinDonor = Join.canonicalRequiredObserverAxisJoinBoundary

------------------------------------------------------------------------
-- Attribution / role boundary.
------------------------------------------------------------------------

record FRETJoinSourceCoordinate : Set where
  constructor fret-join-source-coordinate
  field
    label : String
    doi : String
    sourceRole : String
    directLink : String
    dewey : String
    oeis : String

henzlerWildmanJoinAxisSource : FRETJoinSourceCoordinate
henzlerWildmanJoinAxisSource =
  fret-join-source-coordinate
    "Henzler-Wildman et al. 2007 LID/NMP-labelled AdK FRET axis"
    "10.1038/nature06410"
    "pays the historical LID/NMP-labelled observer axis through the parent source-bounded owner; does not pay the repository-local joint-observer theorem"
    "https://doi.org/10.1038/nature06410"
    "exact article-level Dewey unresolved"
    "not an integer-sequence object; no same-object OEIS coordinate"

hansonJoinAxisSource : FRETJoinSourceCoordinate
hansonJoinAxisSource =
  fret-join-source-coordinate
    "Hanson et al. 2007 LID/CORE-labelled AdK FRET axis"
    "10.1073/pnas.0708600104"
    "pays the historical LID/CORE-labelled observer axis through the parent source-bounded owner; does not pay the repository-local joint-observer theorem"
    "https://doi.org/10.1073/pnas.0708600104"
    "exact article-level Dewey unresolved"
    "not an integer-sequence object; no same-object OEIS coordinate"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdKFRETObserverJoinBoundary : Set where
  constructor adk-fret-observer-join-boundary
  field
    singleLidNmpAxisRetainsBothDeclaredAxes : Bool
    singleLidNmpAxisRetainsBothDeclaredAxesIsFalse :
      singleLidNmpAxisRetainsBothDeclaredAxes ≡ false

    singleLidCoreAxisRetainsBothDeclaredAxes : Bool
    singleLidCoreAxisRetainsBothDeclaredAxesIsFalse :
      singleLidCoreAxisRetainsBothDeclaredAxes ≡ false

    joinedObserverRetainsBothDeclaredAxes : Bool
    joinedObserverRetainsBothDeclaredAxesIsTrue :
      joinedObserverRetainsBothDeclaredAxes ≡ true

    joinStrictlyRicherThanEitherAxisInFiniteWitness : Bool
    joinStrictlyRicherThanEitherAxisInFiniteWitnessIsTrue :
      joinStrictlyRicherThanEitherAxisInFiniteWitness ≡ true

    joinedDeclaredAxisAdequacyMeansCompleteProteinState : Bool
    joinedDeclaredAxisAdequacyMeansCompleteProteinStateIsFalse :
      joinedDeclaredAxisAdequacyMeansCompleteProteinState ≡ false

    historicalExperimentsWereSimultaneousSameMoleculeReadouts : Bool
    historicalExperimentsWereSimultaneousSameMoleculeReadoutsIsFalse :
      historicalExperimentsWereSimultaneousSameMoleculeReadouts ≡ false

    joinConstructionCreatesNewExperimentalData : Bool
    joinConstructionCreatesNewExperimentalDataIsFalse :
      joinConstructionCreatesNewExperimentalData ≡ false

    twoDistancesUniquelyDetermineThreeDimensionalConformation : Bool
    twoDistancesUniquelyDetermineThreeDimensionalConformationIsFalse :
      twoDistancesUniquelyDetermineThreeDimensionalConformation ≡ false

canonicalAdKFRETObserverJoinBoundary : AdKFRETObserverJoinBoundary
canonicalAdKFRETObserverJoinBoundary =
  adk-fret-observer-join-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
