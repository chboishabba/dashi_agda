module DASHI.Mathematics.Symmetry.TrialecticT18BoundaryNaturalityExact where

-- Extends existing T18 six-cell coordinate round trips to an arbitrary
-- compatible boundary C3 action. Classical cyclic permutation action;
-- no equation about the irreducible triadic face is inferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as T18
import DASHI.Mathematics.Symmetry.TrialecticT18CyclicBoundaryActionExact as C3

rotate : T18.CompatibleThreeCellTrialecticBoundary →
  T18.CompatibleThreeCellTrialecticBoundary
rotate = C3.rotateCompatible

-- The coordinate square commutes for arbitrary compatible boundaries,
-- using the genuine source boundary-coordinate round trip.
coordinateNaturality :
  (b : T18.CompatibleThreeCellTrialecticBoundary) →
  T18.compatibleBoundaryToCoordinates (rotate b)
  ≡ C3.rotateCoordinates (T18.compatibleBoundaryToCoordinates b)
coordinateNaturality b =
  T18.coordinatesBoundaryRoundTrip
    (C3.rotateCoordinates (T18.compatibleBoundaryToCoordinates b))

rotateAsCoordinates :
  (b : T18.CompatibleThreeCellTrialecticBoundary) →
  rotate b ≡
  T18.coordinatesToCompatibleBoundary
    (C3.rotateCoordinates (T18.compatibleBoundaryToCoordinates b))
rotateAsCoordinates b = refl

rotateThree :
  (b : T18.CompatibleThreeCellTrialecticBoundary) →
  rotate (rotate (rotate b)) ≡ b
rotateThree b
  rewrite T18.coordinatesBoundaryRoundTrip
            (C3.rotateCoordinates (T18.compatibleBoundaryToCoordinates b))
        | T18.coordinatesBoundaryRoundTrip
            (C3.rotateCoordinates
              (C3.rotateCoordinates (T18.compatibleBoundaryToCoordinates b)))
        | C3.rotateCoordinatesThree (T18.compatibleBoundaryToCoordinates b)
  = T18.boundaryCoordinatesRoundTrip b
