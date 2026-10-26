module DASHI.Mathematics.Symmetry.TrialecticT18CyclicBoundaryActionExact where

-- Reuse the original six-T3-cell T18 boundary owner.
-- The rotation is an A2/W(A2)=S3 even 3-cycle on the three
-- participant and three synthesis labels simultaneously.
-- This C3 is NOT identified with the tetragonal C4 rotation.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as T18

rotateCoordinates :
  T18.StructuredBoundaryCoordinates → T18.StructuredBoundaryCoordinates
rotateCoordinates (T18.structured-boundary-coordinates a b c sab sbc sca) =
  T18.structured-boundary-coordinates b c a sbc sca sab

rotateCoordinatesThree :
  (x : T18.StructuredBoundaryCoordinates) →
  rotateCoordinates (rotateCoordinates (rotateCoordinates x)) ≡ x
rotateCoordinatesThree
  (T18.structured-boundary-coordinates a b c sab sbc sca) = refl

rotateCompatible :
  T18.CompatibleThreeCellTrialecticBoundary →
  T18.CompatibleThreeCellTrialecticBoundary
rotateCompatible boundary =
  T18.coordinatesToCompatibleBoundary
    (rotateCoordinates (T18.compatibleBoundaryToCoordinates boundary))

rotateCompatibleThreeOnCoordinates :
  (x : T18.StructuredBoundaryCoordinates) →
  rotateCoordinates (rotateCoordinates (rotateCoordinates x)) ≡ x
rotateCompatibleThreeOnCoordinates = rotateCoordinatesThree

-- Transport square on the canonical coordinates; the arbitrary boundary
-- case requires the existing boundary-coordinate round-trip theorem.
canonicalTransportSquare :
  (x : T18.StructuredBoundaryCoordinates) →
  rotateCompatible (T18.coordinatesToCompatibleBoundary x)
  ≡ T18.coordinatesToCompatibleBoundary (rotateCoordinates x)
canonicalTransportSquare
  (T18.structured-boundary-coordinates a b c sab sbc sca) = refl
