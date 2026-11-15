module DASHI.Cognition.Teleodynamics.ExceptionalE6E8PluckerDualityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as F3Add
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as F3Mul
import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6

------------------------------------------------------------------------
-- EXPLICIT B2=C2 / PLUCKER DUALITY SURFACE
--
-- The E8 order-three quotient is a 4D symplectic F3-space.  Its totally
-- isotropic 2-planes have Plucker coordinates in the parabolic quadric
-- Q(4,3).  This owner records an explicit 5-coordinate presentation and an
-- explicit linear map to the E6 mod-3 null quadric, together with the inverse
-- coordinate map used by the local reconstruction diagnostic.
--
-- Recognition of actual E8 quotient lines is still gated by a supplied
-- same-object line carrier.  Local exhaustive Python verifies the finite map,
-- inverse reconstruction, and incidence law; that computation is evidence,
-- not an Agda kernel theorem.
------------------------------------------------------------------------

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = F3Add._+3_

infixl 7 _⊗_
_⊗_ : Trit → Trit → Trit
_⊗_ = F3Mul._*3_

neg3 : Trit → Trit
neg3 = F3Add.negate3

record Symplectic4 : Set where
  constructor s4
  field a b c d : Trit
open Symplectic4 public

symplectic : Symplectic4 → Symplectic4 → Trit
symplectic x y =
  (a x ⊗ b y) ⊕ neg3 (b x ⊗ a y) ⊕
  (c x ⊗ d y) ⊕ neg3 (d x ⊗ c y)

record Plucker5 : Set where
  constructor p5
  field p12 p13 p14 p23 p24 : Trit
open Plucker5 public

pluckerQuadratic : Plucker5 → Trit
pluckerQuadratic p =
  neg3 (p12 p ⊗ p12 p) ⊕
  neg3 (p13 p ⊗ p24 p) ⊕
  (p14 p ⊗ p23 p)

-- M =
-- [[0,0,1,1,2],
--  [0,0,0,0,1],
--  [0,1,0,0,2],
--  [1,2,1,2,1],
--  [1,0,2,1,2]]
-- with M^T B_E6 M = 2 B_Plucker.
pluckerToE6 : Plucker5 → E6.E6QuotientV5
pluckerToE6 p = E6.e6-v5
  (p14 p ⊕ p23 p ⊕ neg3 (p24 p))
  (p24 p)
  (p13 p ⊕ neg3 (p24 p))
  (p12 p ⊕ neg3 (p13 p) ⊕ p14 p ⊕ neg3 (p23 p) ⊕ p24 p)
  (p12 p ⊕ neg3 (p14 p) ⊕ p23 p ⊕ neg3 (p24 p))

-- M^-1 =
-- [[0,2,2,2,2],
--  [0,1,1,0,0],
--  [2,1,1,1,2],
--  [2,0,2,2,1],
--  [0,1,0,0,0]].
e6ToPlucker : E6.E6QuotientV5 → Plucker5
e6ToPlucker x = p5
  (neg3 (E6.x1 x) ⊕ neg3 (E6.x2 x) ⊕ neg3 (E6.x3 x) ⊕ neg3 (E6.x4 x))
  (E6.x1 x ⊕ E6.x2 x)
  (neg3 (E6.x0 x) ⊕ E6.x1 x ⊕ E6.x2 x ⊕ E6.x3 x ⊕ neg3 (E6.x4 x))
  (neg3 (E6.x0 x) ⊕ neg3 (E6.x2 x) ⊕ neg3 (E6.x3 x) ⊕ E6.x4 x)
  (E6.x1 x)

record PluckerMatrixReceipt : Set where
  constructor plucker-matrix-receipt
  field
    grade : E6.EvidenceGrade
    matrixRank : Nat
    gramCongruenceScalar : Nat
    gramIdentityCheckedOnAllEntries : Bool
    inverseMatrixIdentityChecked : Bool
    nullConePreservedOnAll243Vectors : Bool
    provenance : String
open PluckerMatrixReceipt public

canonicalPluckerMatrixReceipt : PluckerMatrixReceipt
canonicalPluckerMatrixReceipt =
  plucker-matrix-receipt
    E6.localFiniteComputation
    5 2 true true true
    "local exact F3 computation: rank(M)=5, M^-1 is explicit, and M^T B_E6 M = 2 B_Plucker"

record PluckerDualityComputationReceipt : Set where
  constructor plucker-duality-computation-receipt
  field
    grade : E6.EvidenceGrade
    symplecticProjectivePoints : Nat
    symplecticIsotropicLines : Nat
    e6NullProjectivePoints : Nat
    distinctPluckerImages : Nat
    pairCountChecked : Nat
    allImagesE6Null : Bool
    imageEqualsEntireE6NullQuadric : Bool
    lineIntersectionIffE6Orthogonality : Bool
    inverseSkewRankTwoAllPoints : Bool
    inversePlanesSymplecticIsotropicAllPoints : Bool
    twoSidedRoundTripAllPoints : Bool
    localPythonReproduced : Bool
    provenance : String
open PluckerDualityComputationReceipt public

canonicalPluckerDualityComputationReceipt : PluckerDualityComputationReceipt
canonicalPluckerDualityComputationReceipt =
  plucker-duality-computation-receipt
    E6.localFiniteComputation
    40 40 40 40 780
    true true true true true true true
    "all 40 W(3,3) isotropic lines and all 40 E6 null points; explicit forward Plucker map, inverse skew-matrix plane reconstruction, and exhaustive pairwise incidence test"

record E8LineToE6NullPluckerRecognition : Set₁ where
  field
    E8SymplecticLine : Set
    E6NullPoint : Set
    toPlucker : E8SymplecticLine → Plucker5
    toE6Null : E8SymplecticLine → E6NullPoint
    fromE6Null : E6NullPoint → E8SymplecticLine
    leftRoundTrip : (l : E8SymplecticLine) → fromE6Null (toE6Null l) ≡ l
    rightRoundTrip : (q : E6NullPoint) → toE6Null (fromE6Null q) ≡ q
    e8LineIntersects : E8SymplecticLine → E8SymplecticLine → Set
    e6Orthogonal : E6NullPoint → E6NullPoint → Set
    incidenceIntertwiner :
      (l m : E8SymplecticLine) →
      e8LineIntersects l m → e6Orthogonal (toE6Null l) (toE6Null m)
    provenance : String

data MatchingFortyCountsCreatePluckerRecognition : Set where
data GraphIsomorphismCreatesLinearIsometry : Set where
data LocalPythonCreatesKernelProof : Set where

matchingCountsDoNotCreatePluckerRecognition : MatchingFortyCountsCreatePluckerRecognition → ⊥
matchingCountsDoNotCreatePluckerRecognition ()

graphIsoDoesNotCreateLinearIsometry : GraphIsomorphismCreatesLinearIsometry → ⊥
graphIsoDoesNotCreateLinearIsometry ()

pythonDoesNotCreateKernelProof : LocalPythonCreatesKernelProof → ⊥
pythonDoesNotCreateKernelProof ()

record PluckerDualityBoundary : Set where
  constructor plucker-duality-boundary
  field
    explicitSymplecticFormWritten : Bool
    explicitPluckerQuadraticWritten : Bool
    explicitFiveByFiveMapWritten : Bool
    explicitInverseMapWritten : Bool
    localMatrixReceiptPresent : Bool
    localTwoSidedFortyPointReceiptPresent : Bool
    actualE8LineRecognitionInhabitedHere : Bool
    graphMatchPromotedToLinearTheorem : Bool
    pythonPromotedToKernelProof : Bool

canonicalPluckerDualityBoundary : PluckerDualityBoundary
canonicalPluckerDualityBoundary =
  plucker-duality-boundary true true true true true true false false false
