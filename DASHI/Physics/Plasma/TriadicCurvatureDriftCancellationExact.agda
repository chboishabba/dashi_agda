module DASHI.Physics.Plasma.TriadicCurvatureDriftCancellationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDThreeOutputCyclicElsasserTriadExact as Cyclic

------------------------------------------------------------------------
-- TRIADIC CURVATURE-DRIFT CANCELLATION
--
-- The new zero-bounce frontier is not mirror cancellation but radial curvature
-- closure.  We therefore require three same-orbit / same-surface drift legs,
-- cyclically related, whose vector sum vanishes.  The existing three-output
-- cyclic-triad owner is reused only as a structural donor for the need to carry
-- all three legs and their same-object cyclic identification.
------------------------------------------------------------------------

record DriftVectorSpace : Set₁ where
  constructor drift-vector-space
  field
    Vector : Set
    zero : Vector
    _⊕_ : Vector → Vector → Vector

open DriftVectorSpace public

record TriadicCurvatureDriftCell (space : DriftVectorSpace) : Set₁ where
  constructor triadic-curvature-drift-cell
  field
    leg0 leg1 leg2 : Vector space
    threeLegSum : Vector space
    threeLegSumIsZero : threeLegSum ≡ zero space

    samePhysicalOrbitReceipt : Set
    sameFluxSurfaceReceipt : Set
    sameEnergyPitchReceipt : Set
    equalPhaseSpacingReceipt : Set
    cyclicPermutationReceipt : Set
    curvatureDriftInterpretationReceipt : Set
    cellReference : String

open TriadicCurvatureDriftCell public

record RecursiveTriadicCurvatureCancellation
    (space : DriftVectorSpace) : Set₁ where
  constructor recursive-triadic-curvature-cancellation
  field
    ternaryDepth : Nat
    localCell : TriadicCurvatureDriftCell space
    eachRefinedParentSplitsIntoThreeReceipt : Set
    eachChildTriadClosesReceipt : Set
    recursiveRefinementPreservesZeroReceipt : Set
    sameOrbitPartitionAcrossRefinementReceipt : Set
    refinementReference : String

open RecursiveTriadicCurvatureCancellation public

record TriadicCurvatureDriftBoundary : Set where
  constructor triadic-curvature-drift-boundary
  field
    helicalWindingCountAloneProvesRadialCancellation : Bool
    helicalWindingCountAloneProvesRadialCancellationIsFalse :
      helicalWindingCountAloneProvesRadialCancellation ≡ false

    threePhaseLabelsAloneProvePhysicalCancellation : Bool
    threePhaseLabelsAloneProvePhysicalCancellationIsFalse :
      threePhaseLabelsAloneProvePhysicalCancellation ≡ false

    sameObjectThreeLegIdentificationRequired : Bool
    sameObjectThreeLegIdentificationRequiredIsTrue :
      sameObjectThreeLegIdentificationRequired ≡ true

    recursiveTriadicCancellationMayBeSearchCoordinate : Bool
    recursiveTriadicCancellationMayBeSearchCoordinateIsTrue :
      recursiveTriadicCancellationMayBeSearchCoordinate ≡ true

canonicalTriadicCurvatureDriftBoundary : TriadicCurvatureDriftBoundary
canonicalTriadicCurvatureDriftBoundary =
  triadic-curvature-drift-boundary
    false refl
    false refl
    true refl
    true refl

cyclicTriadDonorReference : String
cyclicTriadDonorReference =
  "DASHI.Physics.Plasma.MHDThreeOutputCyclicElsasserTriadExact -- structural donor only; curvature drift is a distinct physical observable."
