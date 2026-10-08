module DASHI.Foundations.ExceptionalE6F3ExteriorSquareRecognitionExact where

------------------------------------------------------------------------
-- F3^4 EXTERIOR-SQUARE / E6 MOD-3 NULL-CONE RECOGNITION
--
-- DASHI CONTRIBUTION
--
-- This owner formalizes the exact finite coordinate bridge discovered by
-- exhaustive local computation:
--
--   four-trit symplectic carrier V = F3^4
--       -> primitive exterior-square coordinates Lambda^2_0 V ~= F3^5
--       -> standard five-coordinate quadratic carrier.
--
-- The raw punctured four-trit carrier V\{0} is NOT identified with the
-- resulting 80-state null carrier.  The exceptional 80 is the derived
-- nonzero decomposable/primitive null-bivector carrier.  Same-action
-- PGSp4(3) <-> W(E6) promotion remains behind an explicit recognition
-- interface; this file does not manufacture the group isomorphism from
-- cardinality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.List.Base using (map; concatMap; filterᵇ)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- 1. Concrete F3 helpers.
------------------------------------------------------------------------

infixl 6 _+3_
infixl 7 _*3_

_+3_ : Trit → Trit → Trit
_+3_ = G._+3_

_*3_ : Trit → Trit → Trit
_*3_ = H._*3_

-3_ : Trit → Trit
-3_ = G.negate3

tritEq : Trit → Trit → Bool
tritEq neg neg = true
tritEq neg zer = false
tritEq neg pos = false
tritEq zer neg = false
tritEq zer zer = true
tritEq zer pos = false
tritEq pos neg = false
tritEq pos zer = false
tritEq pos pos = true

infixr 4 _andB_
_andB_ : Bool → Bool → Bool
true andB b = b
false andB b = false

notB : Bool → Bool
notB true = false
notB false = true

infixr 3 _orB_
_orB_ : Bool → Bool → Bool
true orB b = true
false orB b = b

boolEq : Bool → Bool → Bool
boolEq true true = true
boolEq false false = true
boolEq _ _ = false

impliesB : Bool → Bool → Bool
impliesB a b = notB a orB b

allTrue : List Bool → Bool
allTrue [] = true
allTrue (b ∷ bs) = b andB allTrue bs

tritNonzero : Trit → Bool
tritNonzero neg = true
tritNonzero zer = false
tritNonzero pos = true

square : Trit → Trit
square x = x *3 x

sum3 : Trit → Trit → Trit → Trit
sum3 a b c = a +3 (b +3 c)

sum4 : Trit → Trit → Trit → Trit → Trit
sum4 a b c d = a +3 (b +3 (c +3 d))

sum5 : Trit → Trit → Trit → Trit → Trit → Trit
sum5 a b c d e = a +3 (b +3 (c +3 (d +3 e)))

------------------------------------------------------------------------
-- 2. Four-trit carrier and symplectic form.
------------------------------------------------------------------------

record F3Four : Set where
  constructor f3four
  field
    x1 x2 x3 x4 : Trit
open F3Four public

symplectic4 : F3Four → F3Four → Trit
symplectic4 u v =
  sum4
    (x1 u *3 x2 v)
    (-3 (x2 u *3 x1 v))
    (x3 u *3 x4 v)
    (-3 (x4 u *3 x3 v))

------------------------------------------------------------------------
-- 3. Primitive exterior-square coordinates.
--
-- Coordinates are (p12,p13,p14,p23,p24); on the symplectic primitive
-- hyperplane p34 = -p12, so the sixth Plucker coordinate is dependent.
------------------------------------------------------------------------

record PrimitiveBivector5 : Set where
  constructor primitiveBivector5
  field
    p12 p13 p14 p23 p24 : Trit
open PrimitiveBivector5 public

pluckerQ : PrimitiveBivector5 → Trit
pluckerQ p =
  sum3
    (-3 (square (p12 p)))
    (-3 (p13 p *3 p24 p))
    (p14 p *3 p23 p)

primitiveSupport : PrimitiveBivector5 → Bool
primitiveSupport p =
  tritNonzero (p12 p)
  orB tritNonzero (p13 p)
  orB tritNonzero (p14 p)
  orB tritNonzero (p23 p)
  orB tritNonzero (p24 p)

wedgePrimitiveCoordinates : F3Four → F3Four → PrimitiveBivector5
wedgePrimitiveCoordinates u v =
  primitiveBivector5
    ((x1 u *3 x2 v) +3 (-3 (x2 u *3 x1 v)))
    ((x1 u *3 x3 v) +3 (-3 (x3 u *3 x1 v)))
    ((x1 u *3 x4 v) +3 (-3 (x4 u *3 x1 v)))
    ((x2 u *3 x3 v) +3 (-3 (x3 u *3 x2 v)))
    ((x2 u *3 x4 v) +3 (-3 (x4 u *3 x2 v)))

------------------------------------------------------------------------
-- 4. Standard F3^5 quadratic carrier and explicit change of basis.
------------------------------------------------------------------------

record StandardFive : Set where
  constructor standardFive
  field
    z1 z2 z3 z4 z5 : Trit
open StandardFive public

standardQ : StandardFive → Trit
standardQ z =
  sum5
    (square (z1 z))
    (square (z2 z))
    (square (z3 z))
    (square (z4 z))
    (square (z5 z))

standardSupport : StandardFive → Bool
standardSupport z =
  tritNonzero (z1 z)
  orB tritNonzero (z2 z)
  orB tritNonzero (z3 z)
  orB tritNonzero (z4 z)
  orB tritNonzero (z5 z)

-- Matrix over F3:
-- [0 0 2 1 0]
-- [0 2 0 0 2]
-- [0 1 1 1 2]
-- [0 1 2 2 2]
-- [1 0 0 0 0]
primitiveToStandard : PrimitiveBivector5 → StandardFive
primitiveToStandard p =
  standardFive
    ((-3 p14 p) +3 p23 p)
    ((-3 p13 p) +3 (-3 p24 p))
    (sum4 (p13 p) (p14 p) (p23 p) (-3 p24 p))
    (sum4 (p13 p) (-3 p14 p) (-3 p23 p) (-3 p24 p))
    (p12 p)

-- Inverse matrix over F3:
-- [0 0 0 0 1]
-- [0 1 1 1 0]
-- [1 0 1 2 0]
-- [2 0 1 2 0]
-- [0 1 2 2 0]
standardToPrimitive : StandardFive → PrimitiveBivector5
standardToPrimitive z =
  primitiveBivector5
    (z5 z)
    (sum3 (z2 z) (z3 z) (z4 z))
    (sum3 (z1 z) (z3 z) (-3 z4 z))
    (sum3 (-3 z1 z) (z3 z) (-3 z4 z))
    (sum3 (z2 z) (-3 z3 z) (-3 z4 z))

------------------------------------------------------------------------
-- 5. Exact finite enumeration and decidable equality.
------------------------------------------------------------------------

trits : List Trit
trits = neg ∷ zer ∷ pos ∷ []

primitiveEnumeration : List PrimitiveBivector5
primitiveEnumeration =
  concatMap (λ a →
  concatMap (λ b →
  concatMap (λ c →
  concatMap (λ d →
  map (λ e → primitiveBivector5 a b c d e) trits)
  trits) trits) trits) trits

standardEnumeration : List StandardFive
standardEnumeration =
  concatMap (λ a →
  concatMap (λ b →
  concatMap (λ c →
  concatMap (λ d →
  map (λ e → standardFive a b c d e) trits)
  trits) trits) trits) trits

primitiveEq : PrimitiveBivector5 → PrimitiveBivector5 → Bool
primitiveEq a b =
  tritEq (p12 a) (p12 b)
  andB tritEq (p13 a) (p13 b)
  andB tritEq (p14 a) (p14 b)
  andB tritEq (p23 a) (p23 b)
  andB tritEq (p24 a) (p24 b)

standardEq : StandardFive → StandardFive → Bool
standardEq a b =
  tritEq (z1 a) (z1 b)
  andB tritEq (z2 a) (z2 b)
  andB tritEq (z3 a) (z3 b)
  andB tritEq (z4 a) (z4 b)
  andB tritEq (z5 a) (z5 b)

primitiveRoundTripCheck : PrimitiveBivector5 → Bool
primitiveRoundTripCheck p =
  primitiveEq (standardToPrimitive (primitiveToStandard p)) p

standardRoundTripCheck : StandardFive → Bool
standardRoundTripCheck z =
  standardEq (primitiveToStandard (standardToPrimitive z)) z

quadraticIntertwiningCheck : PrimitiveBivector5 → Bool
quadraticIntertwiningCheck p =
  tritEq
    (standardQ (primitiveToStandard p))
    (neg *3 pluckerQ p)

supportIntertwiningCheck : PrimitiveBivector5 → Bool
supportIntertwiningCheck p =
  boolEq
    (primitiveSupport p)
    (standardSupport (primitiveToStandard p))

primitiveRoundTripExhaustive :
  allTrue (map primitiveRoundTripCheck primitiveEnumeration) ≡ true
primitiveRoundTripExhaustive = refl

standardRoundTripExhaustive :
  allTrue (map standardRoundTripCheck standardEnumeration) ≡ true
standardRoundTripExhaustive = refl

quadraticIntertwiningExhaustive :
  allTrue (map quadraticIntertwiningCheck primitiveEnumeration) ≡ true
quadraticIntertwiningExhaustive = refl

supportIntertwiningExhaustive :
  allTrue (map supportIntertwiningCheck primitiveEnumeration) ≡ true
supportIntertwiningExhaustive = refl

------------------------------------------------------------------------
-- 6. Derived nonzero null carriers: the honest exceptional 80-state object.
------------------------------------------------------------------------

primitiveNullNonzero : PrimitiveBivector5 → Bool
primitiveNullNonzero p =
  tritEq (pluckerQ p) zer andB primitiveSupport p

standardNullNonzero : StandardFive → Bool
standardNullNonzero z =
  tritEq (standardQ z) zer andB standardSupport z

primitiveNull80Enumeration : List PrimitiveBivector5
primitiveNull80Enumeration =
  filterᵇ primitiveNullNonzero primitiveEnumeration

standardNull80Enumeration : List StandardFive
standardNull80Enumeration =
  filterᵇ standardNullNonzero standardEnumeration

primitiveNull80Count :
  Reindex.listLength primitiveNull80Enumeration ≡ 80
primitiveNull80Count = refl

standardNull80Count :
  Reindex.listLength standardNull80Enumeration ≡ 80
standardNull80Count = refl

nullPredicateIntertwiningCheck : PrimitiveBivector5 → Bool
nullPredicateIntertwiningCheck p =
  boolEq
    (primitiveNullNonzero p)
    (standardNullNonzero (primitiveToStandard p))

nullPredicateIntertwiningExhaustive :
  allTrue (map nullPredicateIntertwiningCheck primitiveEnumeration) ≡ true
nullPredicateIntertwiningExhaustive = refl

------------------------------------------------------------------------
-- 7. Recognition interfaces for the next same-action cut.
------------------------------------------------------------------------

record ProjectiveIncidenceDualityRecognition : Set₁ where
  field
    SymplecticProjectiveLine NullProjectivePoint : Set
    lineToNullPoint : SymplecticProjectiveLine → NullProjectivePoint
    nullPointToLine : NullProjectivePoint → SymplecticProjectiveLine
    lineRoundTrip :
      (line : SymplecticProjectiveLine) →
      nullPointToLine (lineToNullPoint line) ≡ line
    pointRoundTrip :
      (point : NullProjectivePoint) →
      lineToNullPoint (nullPointToLine point) ≡ point
    LinesIntersect NullPointsOrthogonal :
      SymplecticProjectiveLine → SymplecticProjectiveLine → Set
    incidenceMatchesOrthogonality :
      (left right : SymplecticProjectiveLine) →
      LinesIntersect left right →
      NullPointsOrthogonal (lineToNullPoint left) (lineToNullPoint right)

record PGSp4WeylRecognition : Set₁ where
  field
    PGSp4Actor WeylE6Actor FourState FiveState : Set
    actorToWeyl : PGSp4Actor → WeylE6Actor
    fourAction : PGSp4Actor → FourState → FourState
    fiveAction : WeylE6Actor → FiveState → FiveState
    exteriorSquareMap : FourState → FiveState
    sameActionIntertwiner :
      (g : PGSp4Actor) →
      (state : FourState) →
      exteriorSquareMap (fourAction g state)
      ≡ fiveAction (actorToWeyl g) (exteriorSquareMap state)

------------------------------------------------------------------------
-- 8. Fail-closed boundary.
------------------------------------------------------------------------

record ExceptionalE6F3ExteriorSquareRecognitionBoundary : Set where
  constructor exceptional-e6-f3-exterior-square-recognition-boundary
  field
    primitiveExteriorSquareConstructed : Bool
    pluckerStandardQuadraticIntertwinerPaid : Bool
    derivedOrientedLagrangianNullCarrierConstructed : Bool
    explicitTwoSidedCoordinateChartPaid : Bool
    projectiveIncidenceDualityRecorded : Bool
    pgsp4WeylRecognitionInterfaceRecorded : Bool
    rawPuncturedKernel4IdentifiedWithDerivedCarrier : Bool
    literalWeylGroupEqualityProvedHere : Bool
open ExceptionalE6F3ExteriorSquareRecognitionBoundary public

canonicalExceptionalE6F3ExteriorSquareRecognitionBoundary :
  ExceptionalE6F3ExteriorSquareRecognitionBoundary
canonicalExceptionalE6F3ExteriorSquareRecognitionBoundary =
  exceptional-e6-f3-exterior-square-recognition-boundary
    true true true true true true false false
