module DASHI.Foundations.Base369T4SymplecticExteriorSquareE6BridgeExact where

------------------------------------------------------------------------
-- T4 SYMPLECTIC EXTERIOR-SQUARE -> FIVE-DIMENSIONAL QUADRATIC BRIDGE
--
-- DASHI CONTRIBUTION
--
-- This owner formalizes the algebraic recognition surface discovered by exact
-- finite enumeration:
--
--   V4 = F3^4 with symplectic form omega
--   isotropic 2-plane <u,v> -> decomposable bivector u wedge v
--   omega(u,v)=0 -> p12+p34=0, hence a primitive five-coordinate carrier
--   primitive decomposable bivectors -> the nonzero null cone of a 5D
--   quadratic form after an explicit linear coordinate change.
--
-- IMPORTANT STATUS BOUNDARY
-- -------------------------
-- * The algebraic maps and recognition contracts below are Agda terms.
-- * The exhaustive finite counts 1920 / 80 / 40 and the full null-cone image
--   equality are independently checked by
--     scripts/check_e6_f3_exterior_square_bridge.py
--   and are NOT silently promoted here to kernel proofs.
-- * Raw punctured T4 (80 nonzero vectors) and the derived oriented
--   Lagrangian-bivector 80-carrier are distinct typed objects.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Add
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as Mul

infixl 6 _⊕_
infixl 7 _⊗_

_⊕_ : Trit → Trit → Trit
_⊕_ = Add._+3_

_⊗_ : Trit → Trit → Trit
_⊗_ = Mul._*3_

minus3 : Trit → Trit → Trit
minus3 x y = x ⊕ Add.negate3 y

------------------------------------------------------------------------
-- 1. Four-trit symplectic source carrier.
------------------------------------------------------------------------

record T4Point : Set where
  constructor t4
  field
    x1 x2 x3 x4 : Trit
open T4Point public

record Bivector6 : Set where
  constructor biv6
  field
    p12 p13 p14 p23 p24 p34 : Trit
open Bivector6 public

minor2 : Trit → Trit → Trit → Trit → Trit
minor2 a b c d = minus3 (a ⊗ d) (c ⊗ b)

wedge6 : T4Point → T4Point → Bivector6
wedge6 u v =
  biv6
    (minor2 (x1 u) (x1 v) (x2 u) (x2 v))
    (minor2 (x1 u) (x1 v) (x3 u) (x3 v))
    (minor2 (x1 u) (x1 v) (x4 u) (x4 v))
    (minor2 (x2 u) (x2 v) (x3 u) (x3 v))
    (minor2 (x2 u) (x2 v) (x4 u) (x4 v))
    (minor2 (x3 u) (x3 v) (x4 u) (x4 v))

-- Chosen standard symplectic form: omega = p12 + p34.
symplecticForm : T4Point → T4Point → Trit
symplecticForm u v = p12 (wedge6 u v) ⊕ p34 (wedge6 u v)

primitiveConstraint : Bivector6 → Trit
primitiveConstraint p = p12 p ⊕ p34 p

symplecticFormIsPrimitiveConstraint :
  (u v : T4Point) →
  symplecticForm u v ≡ primitiveConstraint (wedge6 u v)
symplecticFormIsPrimitiveConstraint u v = refl

------------------------------------------------------------------------
-- 2. Primitive five-coordinate quotient chart.
------------------------------------------------------------------------

record Primitive5 : Set where
  constructor primitive5
  field
    y12 y13 y14 y23 y24 : Trit
open Primitive5 public

forgetP34 : Bivector6 → Primitive5
forgetP34 p = primitive5 (p12 p) (p13 p) (p14 p) (p23 p) (p24 p)

-- On the isotropic/primitive locus p34 = -p12, so this reconstructs the full
-- bivector from five coordinates.
restorePrimitive : Primitive5 → Bivector6
restorePrimitive y =
  biv6
    (y12 y) (y13 y) (y14 y) (y23 y) (y24 y)
    (Add.negate3 (y12 y))

primitiveForgetRoundTrip :
  (y : Primitive5) → forgetP34 (restorePrimitive y) ≡ y
primitiveForgetRoundTrip (primitive5 a b c d e) = refl

restoredPrimitiveConstraint :
  (y : Primitive5) → primitiveConstraint (restorePrimitive y) ≡ zer
restoredPrimitiveConstraint (primitive5 neg b c d e) = refl
restoredPrimitiveConstraint (primitive5 zer b c d e) = refl
restoredPrimitiveConstraint (primitive5 pos b c d e) = refl

------------------------------------------------------------------------
-- 3. Pluecker quadratic residual on the primitive five-space.
------------------------------------------------------------------------

plueckerQ : Primitive5 → Trit
plueckerQ y =
  (Add.negate3 (y12 y ⊗ y12 y))
  ⊕ (Add.negate3 (y13 y ⊗ y24 y))
  ⊕ (y14 y ⊗ y23 y)

-- This predicate is the exact algebraic target for decomposability after the
-- primitive relation has removed p34.
record PrimitiveNull : Set where
  constructor primitive-null
  field
    point : Primitive5
    plueckerNull : plueckerQ point ≡ zer
open PrimitiveNull public

------------------------------------------------------------------------
-- 4. Explicit change of coordinates to the standard five-square form.
------------------------------------------------------------------------

record Standard5 : Set where
  constructor standard5
  field
    z1 z2 z3 z4 z5 : Trit
open Standard5 public

-- Matrix over F3, encoded with coefficients 0,1,2 as zer,pos,neg:
--
-- [0 0 2 1 0]
-- [0 2 0 0 2]
-- [0 1 1 1 2]
-- [0 1 2 2 2]
-- [1 0 0 0 0]
--
-- This is the concrete isometry chart found by the finite computation.
primitiveToStandard : Primitive5 → Standard5
primitiveToStandard y =
  standard5
    ((neg ⊗ y14 y) ⊕ y23 y)
    ((neg ⊗ y13 y) ⊕ (neg ⊗ y24 y))
    (y13 y ⊕ y14 y ⊕ y23 y ⊕ (neg ⊗ y24 y))
    (y13 y ⊕ (neg ⊗ y14 y) ⊕ (neg ⊗ y23 y) ⊕ (neg ⊗ y24 y))
    (y12 y)

standardQ : Standard5 → Trit
standardQ z =
  (z1 z ⊗ z1 z)
  ⊕ (z2 z ⊗ z2 z)
  ⊕ (z3 z ⊗ z3 z)
  ⊕ (z4 z ⊗ z4 z)
  ⊕ (z5 z ⊗ z5 z)

record StandardNull : Set where
  constructor standard-null
  field
    point5 : Standard5
    qNull : standardQ point5 ≡ zer
open StandardNull public

------------------------------------------------------------------------
-- 5. Recognition contract: the proof-bearing bridge we actually require.
------------------------------------------------------------------------

record ExteriorSquareNullRecognition : Set₁ where
  field
    OrientedLagrangian80 : Set
    NullCone80 : Set

    toPrimitive : OrientedLagrangian80 → PrimitiveNull
    toNullCone : OrientedLagrangian80 → NullCone80
    fromNullCone : NullCone80 → OrientedLagrangian80

    fromAfterTo :
      (state : OrientedLagrangian80) →
      fromNullCone (toNullCone state) ≡ state
    toAfterFrom :
      (state : NullCone80) →
      toNullCone (fromNullCone state) ≡ state

    Actor : Set
    actLag : Actor → OrientedLagrangian80 → OrientedLagrangian80
    actNull : Actor → NullCone80 → NullCone80

    intertwines :
      (g : Actor) → (state : OrientedLagrangian80) →
      toNullCone (actLag g state) ≡ actNull g (toNullCone state)

open ExteriorSquareNullRecognition public

------------------------------------------------------------------------
-- 6. Projective incidence/action recognition contract.
------------------------------------------------------------------------

record ProjectiveIncidenceRecognition : Set₁ where
  field
    LagrangianLines40 : Set
    NullPoints40 : Set
    lagIntersects : LagrangianLines40 → LagrangianLines40 → Set
    nullOrthogonal : NullPoints40 → NullPoints40 → Set

    toNullPoint : LagrangianLines40 → NullPoints40
    fromNullPoint : NullPoints40 → LagrangianLines40

    fromAfterToProjective :
      (line : LagrangianLines40) →
      fromNullPoint (toNullPoint line) ≡ line
    toAfterFromProjective :
      (point : NullPoints40) →
      toNullPoint (fromNullPoint point) ≡ point

    incidenceToOrthogonality :
      (left right : LagrangianLines40) →
      lagIntersects left right →
      nullOrthogonal (toNullPoint left) (toNullPoint right)

    orthogonalityToIncidence :
      (left right : LagrangianLines40) →
      nullOrthogonal (toNullPoint left) (toNullPoint right) →
      lagIntersects left right

open ProjectiveIncidenceRecognition public

------------------------------------------------------------------------
-- 7. Group-level exceptional recognition contract.
------------------------------------------------------------------------

-- The finite computation identifies the induced projective symplectic-
-- similitude action with the 5D mod-3 W(E6) matrix image.  This record keeps
-- the promotion criterion action-based: an abstract order match is not enough.
record PGSp4WeylE6Recognition : Set₁ where
  field
    PGSp4Actor WeylE6Actor FiveSpace : Set
    pgspAction : PGSp4Actor → FiveSpace → FiveSpace
    weylAction : WeylE6Actor → FiveSpace → FiveSpace

    toWeyl : PGSp4Actor → WeylE6Actor
    fromWeyl : WeylE6Actor → PGSp4Actor

    actorFromAfterTo :
      (g : PGSp4Actor) → fromWeyl (toWeyl g) ≡ g
    actorToAfterFrom :
      (w : WeylE6Actor) → toWeyl (fromWeyl w) ≡ w

    sameFiveDimensionalAction :
      (g : PGSp4Actor) → (x : FiveSpace) →
      pgspAction g x ≡ weylAction (toWeyl g) x

open PGSp4WeylE6Recognition public

------------------------------------------------------------------------
-- 8. Exact finite-computation metadata and promotion boundary.
------------------------------------------------------------------------

orderedIsotropicIndependentPairCount : Nat
orderedIsotropicIndependentPairCount = 1920

orientedLagrangianBivectorCount : Nat
orientedLagrangianBivectorCount = 80

projectiveLagrangianLineCount : Nat
projectiveLagrangianLineCount = 40

standardNonzeroNullCount : Nat
standardNonzeroNullCount = 80

projectiveNullPointCount : Nat
projectiveNullPointCount = 40

record T4ExteriorSquareE6BridgeBoundary : Set where
  constructor t4-exterior-square-e6-bridge-boundary
  field
    symplecticPrimitiveIdentityKernelPaid : Bool
    primitiveFiveCoordinateRoundTripKernelPaid : Bool
    restoredPrimitiveConstraintKernelPaid : Bool
    explicitFiveCoordinateMapDefined : Bool
    sameActionRecognitionInterfaceDefined : Bool
    projectiveIncidenceRecognitionInterfaceDefined : Bool
    pgsp4WeylRecognitionInterfaceDefined : Bool

    exhaustiveFiniteCertificateScriptPresent : Bool
    orientedBivectorCount80KernelPaidHere : Bool
    fullNullConeImageEqualityKernelPaidHere : Bool
    projectiveSRG401224KernelPaidHere : Bool
    pgsp4EqualsWeylE6MatrixImageKernelPaidHere : Bool

    rawPuncturedT4IdentifiedWithDerivedLag80 : Bool
    cardinalityAlonePromotesRecognition : Bool

canonicalT4ExteriorSquareE6BridgeBoundary : T4ExteriorSquareE6BridgeBoundary
canonicalT4ExteriorSquareE6BridgeBoundary =
  t4-exterior-square-e6-bridge-boundary
    true true true true true true true
    true
    false false false false
    false false
