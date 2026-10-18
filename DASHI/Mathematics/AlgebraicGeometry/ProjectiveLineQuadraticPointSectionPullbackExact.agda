module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineQuadraticPointSectionPullbackExact where

------------------------------------------------------------------------
-- TARGET POINT SECTION PULLBACK UNDER THE LITERAL QUADRATIC P¹ MAP
--
-- The target point [1:0] is cut out by the homogeneous linear section y1.
-- Pull it back along f([x0:x1])=[x0²:x1²]. The resulting polynomial section
-- is exactly x1*x1.
--
-- This is a genuine equation-level polynomial substitution on the same
-- projective coordinates, not an argument from the number of preimage points.
-- The repeated factor is explicit. In a scheme/divisor development it must
-- be shown to give the Cartier divisor 2·[1:0], and then its cycle-class
-- pullback. Neither multiplicity nor cycle-class action is presumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact as Overlap
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineQuadraticHomogeneousTransportExact as Square
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineQuadraticGraphEquationExact as Graph

------------------------------------------------------------------------
-- Actual homogeneous linear form defining the target point [1:0].
------------------------------------------------------------------------

targetPointSection :
  ∀ {field : CP.ComplexFieldPresentation} →
  P1.HomogeneousPair field →
  CP.Complex field
targetPointSection = P1.second

------------------------------------------------------------------------
-- Same literal map, same section: pullback is the SQUARE of the SOURCE
-- second coordinate. No nonzero-root counting is substituted for this.
------------------------------------------------------------------------

pullbackTargetPointSection :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  P1.HomogeneousPair field →
  CP.Complex field
pullbackTargetPointSection laws source =
  targetPointSection (Square.squarePair laws source)

targetPointSectionPullbackIsSquare :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (source : P1.HomogeneousPair field) →
  pullbackTargetPointSection laws source
  ≡
  CP.multiply field
    (P1.second source)
    (P1.second source)
targetPointSectionPullbackIsSquare laws source = refl

------------------------------------------------------------------------
-- The pullback section is homogeneous of degree TWO. This equality is
-- proved via the existing rescaling-squared transport theorem, not by
-- postulating a geometric degree or Chow action.
------------------------------------------------------------------------

pointSectionPullbackRescalesQuadratically :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    {source source' : P1.HomogeneousPair field}
    (rescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine source)
        (P1.pairToHomogeneousLine source')) →
  pullbackTargetPointSection laws source'
  ≡
  CP.multiply field
    (CP.multiply field (CP.scalar rescale) (CP.scalar rescale))
    (pullbackTargetPointSection laws source)
pointSectionPullbackRescalesQuadratically
    {field} laws {source} {source'} rescale =
  trans
    (cong₂ (CP.multiply field)
      (Square.rescalingSecond rescale)
      (Square.rescalingSecond rescale))
    (Square.squareScaling laws (CP.scalar rescale) (P1.second source))

------------------------------------------------------------------------
-- The source (x1)^2 is the complete polynomial-level response for this
-- selected section. What remains to prove for Hodge is the divisor equality
-- f^*[1:0]=2[1:0] in CH^1(P¹), the Chern/cycle-class commutation, and a
-- correspondence capable of acting nontrivially on difficult primitive
-- rational Hodge classes on a higher-dimensional variety.
------------------------------------------------------------------------
