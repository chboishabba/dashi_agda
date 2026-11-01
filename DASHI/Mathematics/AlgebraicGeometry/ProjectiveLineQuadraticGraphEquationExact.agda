module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineQuadraticGraphEquationExact where

------------------------------------------------------------------------
-- QUADRATIC GRAPH EQUATION ON THE ACTUAL PROJECTIVE-LINE COORDINATES
--
-- Let x=[x0:x1] and y=[y0:y1] be literal homogeneous pairs.
-- The equation defining the graph of x↦[x0²:x1²] is
--
--              y0 * x1² = y1 * x0²
--
-- or, in a ring presentation, y0*x1²-y1*x0²=0.
--
-- Both monomials have source-degree two and target-degree one. For each
-- actual x, the target y=squarePair x satisfies the graph equation.
--
-- IMPORTANT: graph-equation membership is an actual coordinate-level
-- equation, NOT YET a closed subscheme, rational Chow divisor, or its
-- singular class. Scheme-theoretic inverse-image multiplicity two still
-- requires an integral/divisor and cycle-class owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact as Overlap
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineQuadraticHomogeneousTransportExact as Square

------------------------------------------------------------------------
-- Actual bidegree-(2,1) monomials, with no equality test or synthetic type
-- substituted for field multiplication.
------------------------------------------------------------------------

graphLeft :
  ∀ {field : CP.ComplexFieldPresentation} →
  P1.HomogeneousPair field →
  P1.HomogeneousPair field →
  CP.Complex field
graphLeft {field} source target =
  CP.multiply field
    (P1.first target)
    (CP.multiply field (P1.second source) (P1.second source))

graphRight :
  ∀ {field : CP.ComplexFieldPresentation} →
  P1.HomogeneousPair field →
  P1.HomogeneousPair field →
  CP.Complex field
graphRight {field} source target =
  CP.multiply field
    (P1.second target)
    (CP.multiply field (P1.first source) (P1.first source))

QuadraticGraphEquation :
  ∀ {field : CP.ComplexFieldPresentation} →
  P1.HomogeneousPair field →
  P1.HomogeneousPair field →
  Set
QuadraticGraphEquation source target =
  graphLeft source target ≡ graphRight source target

------------------------------------------------------------------------
-- The graph of the actual degree-two homogeneous coordinate map lies in
-- the literal bihomogeneous polynomial zero locus, by COMMUTATIVITY.
------------------------------------------------------------------------

squareMapSatisfiesGraphEquation :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (source : P1.HomogeneousPair field) →
  QuadraticGraphEquation source (Square.squarePair laws source)
squareMapSatisfiesGraphEquation {field} laws source =
  Overlap.multiplyCommutative laws
    (CP.multiply field (P1.first source) (P1.first source))
    (CP.multiply field (P1.second source) (P1.second source))

------------------------------------------------------------------------
-- Actual monomial scaling: changing the homogeneous source by s, and the
-- target by t, multiplies EACH graph monomial by t*(s*s).
------------------------------------------------------------------------

commuteInnerMonomial :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (t s² y x : CP.Complex field) →
  CP.multiply field
    (CP.multiply field t y)
    (CP.multiply field s² x)
  ≡
  CP.multiply field
    (CP.multiply field t s²)
    (CP.multiply field y x)
commuteInnerMonomial {field} laws t s² y x =
  trans
    (sym (CP.multiplyAssociative (Overlap.base laws)
      t y (CP.multiply field s² x)))
    (trans
      (cong (CP.multiply field t)
        (trans
          (CP.multiplyAssociative (Overlap.base laws) y s² x)
          (trans
            (cong (λ a → CP.multiply field a x)
              (Overlap.multiplyCommutative laws y s²))
            (sym
              (CP.multiplyAssociative (Overlap.base laws)
                s² y x)))))
      (CP.multiplyAssociative (Overlap.base laws)
        t s² (CP.multiply field y x)))

graphLeftScales :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    {source source' target target' : P1.HomogeneousPair field}
    (sourceRescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine source)
        (P1.pairToHomogeneousLine source'))
    (targetRescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine target)
        (P1.pairToHomogeneousLine target')) →
  graphLeft source' target'
  ≡
  CP.multiply field
    (CP.multiply field
      (CP.scalar targetRescale)
      (CP.multiply field
        (CP.scalar sourceRescale)
        (CP.scalar sourceRescale)))
    (graphLeft source target)
graphLeftScales {field} laws
    {source} {source'} {target} {target'}
    sourceRescale targetRescale =
  trans
    (cong₂ (CP.multiply field)
      (Square.rescalingFirst targetRescale)
      (cong₂ (CP.multiply field)
        (Square.rescalingSecond sourceRescale)
        (Square.rescalingSecond sourceRescale)))
    (trans
      (cong
        (λ value →
          CP.multiply field
            (CP.multiply field
              (CP.scalar targetRescale)
              (P1.first target))
            value)
        (Square.squareScaling laws
          (CP.scalar sourceRescale)
          (P1.second source)))
      (commuteInnerMonomial laws
        (CP.scalar targetRescale)
        (CP.multiply field
          (CP.scalar sourceRescale)
          (CP.scalar sourceRescale))
        (P1.first target)
        (CP.multiply field
          (P1.second source)
          (P1.second source))))

graphRightScales :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    {source source' target target' : P1.HomogeneousPair field}
    (sourceRescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine source)
        (P1.pairToHomogeneousLine source'))
    (targetRescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine target)
        (P1.pairToHomogeneousLine target')) →
  graphRight source' target'
  ≡
  CP.multiply field
    (CP.multiply field
      (CP.scalar targetRescale)
      (CP.multiply field
        (CP.scalar sourceRescale)
        (CP.scalar sourceRescale)))
    (graphRight source target)
graphRightScales {field} laws
    {source} {source'} {target} {target'}
    sourceRescale targetRescale =
  trans
    (cong₂ (CP.multiply field)
      (Square.rescalingSecond targetRescale)
      (cong₂ (CP.multiply field)
        (Square.rescalingFirst sourceRescale)
        (Square.rescalingFirst sourceRescale)))
    (trans
      (cong
        (λ value →
          CP.multiply field
            (CP.multiply field
              (CP.scalar targetRescale)
              (P1.second target))
            value)
        (Square.squareScaling laws
          (CP.scalar sourceRescale)
          (P1.first source)))
      (commuteInnerMonomial laws
        (CP.scalar targetRescale)
        (CP.multiply field
          (CP.scalar sourceRescale)
          (CP.scalar sourceRescale))
        (P1.second target)
        (CP.multiply field
          (P1.first source)
          (P1.first source))))

------------------------------------------------------------------------
-- Genuine projective-representation invariance. This is the sheaf/gluing
-- prerequisite for the bidegree-(2,1) graph equation to define a locus on
-- P1×P1 instead of depending on the chosen affine/homogeneous charts.
------------------------------------------------------------------------

graphEquationRespectsProjectiveRescalings :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    {source source' target target' : P1.HomogeneousPair field}
    (sourceRescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine source)
        (P1.pairToHomogeneousLine source'))
    (targetRescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine target)
        (P1.pairToHomogeneousLine target')) →
  QuadraticGraphEquation source target →
  QuadraticGraphEquation source' target'
graphEquationRespectsProjectiveRescalings
    {field} laws {source} {source'} {target} {target'}
    sourceRescale targetRescale equation =
  trans
    (graphLeftScales laws sourceRescale targetRescale)
    (trans
      (cong
        (CP.multiply field
          (CP.multiply field
            (CP.scalar targetRescale)
            (CP.multiply field
              (CP.scalar sourceRescale)
              (CP.scalar sourceRescale))))
        equation)
      (sym (graphRightScales laws sourceRescale targetRescale)))

------------------------------------------------------------------------
-- Formula-level bidegree data, separately from geometric Chow ownership.
-- Every monomial has two SOURCE variables and one TARGET variable.
------------------------------------------------------------------------

record BihomogeneousDegree : Set where
  constructor bidegree
  field
    sourceDegree : Nat
    targetDegree : Nat

graphLeftDegree graphRightDegree : BihomogeneousDegree
graphLeftDegree = bidegree 2 1
graphRightDegree = bidegree 2 1

graphMonomialsSameBidegree :
  graphLeftDegree ≡ graphRightDegree
graphMonomialsSameBidegree = refl

------------------------------------------------------------------------
-- OPEN:
-- The zero locus must be shown to be the actual graph CLOSED SUBSCHEME of
-- P1×P1, with no parasitic components; the graph divisor must receive
-- its CH¹ class (2,1). Pullback of a target-point divisor must then be
-- derived scheme-theoretically as 2 times the corresponding source point.
-- None of those follows from the polynomial equation in a field alone.
------------------------------------------------------------------------
