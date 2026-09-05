module DASHI.Physics.Astrophysics.GrillmairDistanceScanMatchedFilterCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record DistanceScanCoordinate : Set where
  constructor distance-scan-coordinate
  field
    modulusOffsetTenthsMag : Nat
    templateLabel : String
    signalProbability : String
    foregroundProbability : String
    combinedWeight : String
    sourceReference : String

open DistanceScanCoordinate public

record StreamCandidateReceipt : Set where
  constructor stream-candidate-receipt
  field
    skyTrack : String
    bestDistanceModulus : String
    scanStep : String
    projection : String
    reddeningControl : String
    matchedFilterExcess : String
    requiresKinematicConfirmation : Bool
    requiresKinematicConfirmationIsTrue : requiresKinematicConfirmation ≡ true

open StreamCandidateReceipt public

record OrbitFitReceipt : Set where
  constructor orbit-fit-receipt
  field
    candidate : StreamCandidateReceipt
    assumedGalacticPotential : String
    fittedOrbit : String
    radialVelocityConstraint : String
    properMotionConstraint : String
    progenitorAssociation : String
    progenitorAssociationConfirmed : Bool

open OrbitFitReceipt public

record GrillmairCompilerBoundary : Set where
  constructor grillmair-compiler-boundary
  field
    matchedFilterExcessEqualsConfirmedStream : Bool
    matchedFilterExcessEqualsConfirmedStreamIsFalse : matchedFilterExcessEqualsConfirmedStream ≡ false
    bestDistanceBinIsExactPhysicalDistance : Bool
    bestDistanceBinIsExactPhysicalDistanceIsFalse : bestDistanceBinIsExactPhysicalDistance ≡ false
    orbitFitUniquelyDeterminesProgenitor : Bool
    orbitFitUniquelyDeterminesProgenitorIsFalse : orbitFitUniquelyDeterminesProgenitor ≡ false
    projectionAndReddeningMustRemainExplicit : Bool
    projectionAndReddeningMustRemainExplicitIsTrue : projectionAndReddeningMustRemainExplicit ≡ true

canonicalGrillmairCompilerBoundary : GrillmairCompilerBoundary
canonicalGrillmairCompilerBoundary = grillmair-compiler-boundary false refl false refl false refl true refl
