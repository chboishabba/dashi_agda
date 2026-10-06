module DASHI.Foundations.F3SymplecticFourExteriorSquareExact where

------------------------------------------------------------------------
-- F3^4 SYMPLECTIC -> PRIMITIVE EXTERIOR-SQUARE FIVE-CARRIER
--
-- DASHI CONTRIBUTION
--
-- This owner introduces the exact algebraic carrier behind the local finite
-- computation:
--
--   V4 = F3^4 with omega(u,v)=u0v1-u1v0+u2v3-u3v2
--   wedge^2 V4 has Plucker coordinates p01,p02,p03,p12,p13,p23
--   omega(u,v)=0 implies the primitive relation p23=-p01
--
-- so an isotropic decomposable bivector is represented by five coordinates
--   (p01,p02,p03,p12,p13)
-- with Plucker/null equation
--   -p01^2 - p02*p13 + p03*p12 = 0.
--
-- IMPORTANT FIREWALL:
-- the raw punctured four-trit carrier F3^4\{0} and the derived oriented
-- Lagrangian bivector carrier are different typed objects even though both
-- have 80 elements in the finite q=3 model.  This file never promotes
-- cardinality agreement to same-object recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Add
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as Mul

infixl 6 _+₃_ _-₃_
infixl 7 _*₃_

_+₃_ : Trit → Trit → Trit
_+₃_ = Add._+3_

_*₃_ : Trit → Trit → Trit
_*₃_ = Mul._*3_

_-₃_ : Trit → Trit → Trit
a -₃ b = a +₃ Add.negate3 b

square₃ : Trit → Trit
square₃ a = a *₃ a

------------------------------------------------------------------------
-- 1. Four-trit symplectic carrier.
------------------------------------------------------------------------

record V4 : Set where
  constructor v4
  field
    x0 x1 x2 x3 : Trit
open V4 public

symplectic4 : V4 → V4 → Trit
symplectic4 u v =
  ((x0 u *₃ x1 v) -₃ (x1 u *₃ x0 v)) +₃
  ((x2 u *₃ x3 v) -₃ (x3 u *₃ x2 v))

------------------------------------------------------------------------
-- 2. Exterior-square and primitive five-coordinate chart.
------------------------------------------------------------------------

record Bivector6 : Set where
  constructor bivector6
  field
    p01 p02 p03 p12 p13 p23 : Trit
open Bivector6 public

minor : Trit → Trit → Trit → Trit → Trit
minor ua ub va vb = (ua *₃ vb) -₃ (ub *₃ va)

wedge4 : V4 → V4 → Bivector6
wedge4 u v =
  bivector6
    (minor (x0 u) (x1 u) (x0 v) (x1 v))
    (minor (x0 u) (x2 u) (x0 v) (x2 v))
    (minor (x0 u) (x3 u) (x0 v) (x3 v))
    (minor (x1 u) (x2 u) (x1 v) (x2 v))
    (minor (x1 u) (x3 u) (x1 v) (x3 v))
    (minor (x2 u) (x3 u) (x2 v) (x3 v))

record Primitive5 : Set where
  constructor primitive5
  field
    q01 q02 q03 q12 q13 : Trit
open Primitive5 public

primitiveProjection : Bivector6 → Primitive5
primitiveProjection p = primitive5 (p01 p) (p02 p) (p03 p) (p12 p) (p13 p)

wedgePrimitive : V4 → V4 → Primitive5
wedgePrimitive u v = primitiveProjection (wedge4 u v)

primitiveP23 : Primitive5 → Trit
primitiveP23 p = Add.negate3 (q01 p)

primitiveQuadratic : Primitive5 → Trit
primitiveQuadratic p =
  (Add.negate3 (square₃ (q01 p))) +₃
  ((q03 p *₃ q12 p) -₃ (q02 p *₃ q13 p))

primitiveBilinear : Primitive5 → Primitive5 → Trit
primitiveBilinear p r =
  Add.negate3 ((q01 p *₃ q01 r) +₃ (q01 r *₃ q01 p)) +₃
  (((q03 p *₃ q12 r) +₃ (q03 r *₃ q12 p)) -₃
   ((q02 p *₃ q13 r) +₃ (q02 r *₃ q13 p)))

------------------------------------------------------------------------
-- 3. Typed witnesses.  The Plucker/null receipt is proof-relevant rather
--    than inferred from the 80-count.  A later theorem may construct this
--    receipt from isotropy alone without changing downstream interfaces.
------------------------------------------------------------------------

data IsNonzeroTrit : Trit → Set where
  negNonzero : IsNonzeroTrit neg
  posNonzero : IsNonzeroTrit pos

data PrimitiveAxis : Set where
  axis01 axis02 axis03 axis12 axis13 : PrimitiveAxis

primitiveCoordinate : PrimitiveAxis → Primitive5 → Trit
primitiveCoordinate axis01 p = q01 p
primitiveCoordinate axis02 p = q02 p
primitiveCoordinate axis03 p = q03 p
primitiveCoordinate axis12 p = q12 p
primitiveCoordinate axis13 p = q13 p

record PrimitiveNonzero (p : Primitive5) : Set where
  constructor primitive-nonzero
  field
    axis : PrimitiveAxis
    coordinateNonzero : IsNonzeroTrit (primitiveCoordinate axis p)
open PrimitiveNonzero public

record OrientedLagrangianBivector : Set where
  constructor oriented-lagrangian-bivector
  field
    left right : V4
    isotropic : symplectic4 left right ≡ zer
    nonzeroWedge : PrimitiveNonzero (wedgePrimitive left right)
    pluckerNull : primitiveQuadratic (wedgePrimitive left right) ≡ zer
open OrientedLagrangianBivector public

lagrangianPrimitive : OrientedLagrangianBivector → Primitive5
lagrangianPrimitive l = wedgePrimitive (left l) (right l)

record PrimitiveNullPoint : Set where
  constructor primitive-null-point
  field
    point : Primitive5
    pointNonzero : PrimitiveNonzero point
    pointNull : primitiveQuadratic point ≡ zer
open PrimitiveNullPoint public

lagrangianToPrimitiveNull : OrientedLagrangianBivector → PrimitiveNullPoint
lagrangianToPrimitiveNull l =
  primitive-null-point
    (lagrangianPrimitive l)
    (nonzeroWedge l)
    (pluckerNull l)

------------------------------------------------------------------------
-- 4. Recognition interface.
--
-- An exact same-object promotion requires BOTH directions and round trips.
-- The inverse is intentionally not manufactured from the equality 80=80.
------------------------------------------------------------------------

record OrientedLagrangianNullRecognition : Set₁ where
  field
    toNull : OrientedLagrangianBivector → PrimitiveNullPoint
    fromNull : PrimitiveNullPoint → OrientedLagrangianBivector
    fromAfterTo :
      (state : OrientedLagrangianBivector) →
      fromNull (toNull state) ≡ state
    toAfterFrom :
      (state : PrimitiveNullPoint) →
      toNull (fromNull state) ≡ state
open OrientedLagrangianNullRecognition public

record ProjectiveIncidenceDuality : Set₁ where
  field
    SymplecticProjectiveLine : Set
    QuadraticProjectiveNullPoint : Set
    linesMeet : SymplecticProjectiveLine → SymplecticProjectiveLine → Set
    nullOrthogonal :
      QuadraticProjectiveNullPoint → QuadraticProjectiveNullPoint → Set
    toNullPoint : SymplecticProjectiveLine → QuadraticProjectiveNullPoint
    fromNullPoint : QuadraticProjectiveNullPoint → SymplecticProjectiveLine
    fromAfterToProjective :
      (line : SymplecticProjectiveLine) →
      fromNullPoint (toNullPoint line) ≡ line
    toAfterFromProjective :
      (point : QuadraticProjectiveNullPoint) →
      toNullPoint (fromNullPoint point) ≡ point
    incidenceIffOrthogonality :
      (leftLine rightLine : SymplecticProjectiveLine) →
      linesMeet leftLine rightLine →
      nullOrthogonal (toNullPoint leftLine) (toNullPoint rightLine)

------------------------------------------------------------------------
-- 5. Action-level recognition socket.
------------------------------------------------------------------------

record ExteriorSquareActionRecognition : Set₁ where
  field
    Actor : Set
    actLag : Actor → OrientedLagrangianBivector → OrientedLagrangianBivector
    actNull : Actor → PrimitiveNullPoint → PrimitiveNullPoint
    recognition : OrientedLagrangianNullRecognition
    actionIntertwines :
      (g : Actor) → (state : OrientedLagrangianBivector) →
      toNull recognition (actLag g state)
      ≡ actNull g (toNull recognition state)
open ExteriorSquareActionRecognition public

------------------------------------------------------------------------
-- 6. Explicit firewall and max-cut boundary.
------------------------------------------------------------------------

record ExteriorSquareBoundary : Set where
  constructor exterior-square-boundary
  field
    primitiveExteriorSquareConstructed : Bool
    pluckerNullQuadraticRecorded : Bool
    orientedLagrangianRecognitionTyped : Bool
    projectiveIncidenceDualityTyped : Bool
    actionIntertwinerTyped : Bool
    rawPuncturedT4IdentifiedWithDerivedLag80 : Bool
    cardinalityAlonePromotesRecognition : Bool
    pluckerNullDerivedFromIsotropyInsideThisOwner : Bool
    fullPGSp4EqualsWE6MatrixGroupInsideThisOwner : Bool
open ExteriorSquareBoundary public

canonicalExteriorSquareBoundary : ExteriorSquareBoundary
canonicalExteriorSquareBoundary =
  exterior-square-boundary
    true true true true true
    false false false false
