module DASHI.Physics.Chemistry.AmmoniaGroundStateC3ActionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaGroundStateC3ActionExact as A
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as E

groundDeterminantPhaseIsInvariant : A.groundDeterminantPhase ≡ E.invariant
groundDeterminantPhaseIsInvariant = A.groundDeterminantPhaseInvariant

phaseComputedFromOccupiedCarrier :
  A.GroundStateC3Boundary.determinantPhaseComputedFromOccupiedCarrier
    A.canonicalGroundStateC3Boundary ≡ true
phaseComputedFromOccupiedCarrier = refl

trivialGroundRepresentationPaid :
  A.GroundStateC3Boundary.trivialGroundConfigurationC3RepresentationPaid
    A.canonicalGroundStateC3Boundary ≡ true
trivialGroundRepresentationPaid = refl

closedShellInvariantPaid :
  A.GroundStateC3Boundary.closedShellDeterminantInvariantPaid
    A.canonicalGroundStateC3Boundary ≡ true
closedShellInvariantPaid = refl

realSpaceWavefunctionActionStillUnpaid :
  A.GroundStateC3Boundary.nontrivialRealSpaceWavefunctionC3ActionPaid
    A.canonicalGroundStateC3Boundary ≡ false
realSpaceWavefunctionActionStillUnpaid = refl

monsterActionStillUnpaid :
  A.GroundStateC3Boundary.c3GroundStateActionCreatesMonsterAction
    A.canonicalGroundStateC3Boundary ≡ false
monsterActionStillUnpaid = refl
