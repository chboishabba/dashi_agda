module DASHI.Physics.Chemistry.AmmoniaGroundStateC3ActionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaGroundStateC3ActionExact as A
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as E

occupiedEPhaseProductIsInvariant :
  A.occupiedEManifoldPhase ≡ E.invariant
occupiedEPhaseProductIsInvariant = refl

closedShellDeterminantIsC3Invariant :
  A.groundDeterminantPhase ≡ E.invariant
closedShellDeterminantIsC3Invariant = refl

groundStateActionPaid :
  A.GroundStateC3Boundary.literalGroundConfigurationC3ActionPaid
    A.canonicalGroundStateC3Boundary ≡ true
groundStateActionPaid = refl

fullSpatialWavefunctionStillOpen :
  A.GroundStateC3Boundary.realSpaceWavefunctionActionPaid
    A.canonicalGroundStateC3Boundary ≡ false
fullSpatialWavefunctionStillOpen = refl
