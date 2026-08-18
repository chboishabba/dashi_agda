module DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- Journal of the Ramanujan Mathematical Society 17 (2002), 115--147.
-- No DOI asserted here.
--
-- Schmidt's compact model for an unramified principal series is obtained by
-- restricting the induced representation to K = GL_2(o).  Lemma 2.1.1 gives
-- the K_2(2) / K_0(p^2) valuation cells.  The principal full-level-2 subgroup
-- K(2) instead gives the finite quotient B(F_2)\GL_2(F_2) = P^1(F_2).
--
-- DASHI CONTRIBUTION
--
-- Put the TWO three-dimensional fixed-vector models into the same finite
-- compact quotient B(Z/4)\GL_2(Z/4), whose six left cosets were already
-- independently enumerated in scripts/verify_p11_two_adic_local_averaging.py.
--
-- The right-orbit partitions are exactly
--
--   principal K(2): {0,2}, {1,3}, {4,5}
--   K_0(4):         {0,1,2,3}, {4}, {5}.
--
-- Hence a function invariant under both groups has exactly TWO independent
-- coordinates.  Equivalently, inside the principal three-coordinate model
-- the common subspace is (a,a,b); inside the K_0(4) model it is (a,b,b).
--
-- This strengthens the earlier rank-two averaging no-go: the two 3-spaces are
-- distinct subspaces of one local representation with a two-coordinate
-- intersection.  Therefore there is no identity-induced "change of basis";
-- any full 3D comparison requires extra local operator/test-vector data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as K0

------------------------------------------------------------------------
-- Six compact quotient states.
------------------------------------------------------------------------

data CompactSix : Set where
  s0 s1 s2 s3 s4 s5 : CompactSix

principalValue : Principal.Old3 → CompactSix → ℤ
principalValue v s0 = Principal.x1 v
principalValue v s1 = Principal.x2 v
principalValue v s2 = Principal.x1 v
principalValue v s3 = Principal.x2 v
principalValue v s4 = Principal.x4 v
principalValue v s5 = Principal.x4 v

k0Value : K0.Bruhat3 → CompactSix → ℤ
k0Value v s0 = K0.wide v
k0Value v s1 = K0.wide v
k0Value v s2 = K0.wide v
k0Value v s3 = K0.wide v
k0Value v s4 = K0.left v
k0Value v s5 = K0.right v

------------------------------------------------------------------------
-- Pointwise same-function comparison in the common compact ambient model.
------------------------------------------------------------------------

record SameCompactFunction (p : Principal.Old3) (k : K0.Bruhat3) : Set where
  field
    at0 : principalValue p s0 ≡ k0Value k s0
    at1 : principalValue p s1 ≡ k0Value k s1
    at2 : principalValue p s2 ≡ k0Value k s2
    at3 : principalValue p s3 ≡ k0Value k s3
    at4 : principalValue p s4 ≡ k0Value k s4
    at5 : principalValue p s5 ≡ k0Value k s5
open SameCompactFunction public

principalFirstTwoMustAgree :
  {p : Principal.Old3} {k : K0.Bruhat3} →
  SameCompactFunction p k → Principal.x1 p ≡ Principal.x2 p
principalFirstTwoMustAgree same = trans (at0 same) (sym (at1 same))

k0TerminalCoordinatesMustAgree :
  {p : Principal.Old3} {k : K0.Bruhat3} →
  SameCompactFunction p k → K0.left k ≡ K0.right k
k0TerminalCoordinatesMustAgree same = trans (sym (at4 same)) (at5 same)

------------------------------------------------------------------------
-- Exact two-coordinate normal form of the intersection.
------------------------------------------------------------------------

record Common2 : Set where
  constructor common2
  field
    first terminal : ℤ
open Common2 public

principalCommon : Common2 → Principal.Old3
principalCommon c = Principal.old3 (first c) (first c) (terminal c)

k0Common : Common2 → K0.Bruhat3
k0Common c = K0.bruhat3 (first c) (terminal c) (terminal c)

commonSameCompactFunction :
  (c : Common2) → SameCompactFunction (principalCommon c) (k0Common c)
commonSameCompactFunction c = record
  { at0 = refl
  ; at1 = refl
  ; at2 = refl
  ; at3 = refl
  ; at4 = refl
  ; at5 = refl
  }

principalCommonCoordinatesRecover :
  (c : Common2) →
  common2 (Principal.x1 (principalCommon c)) (Principal.x4 (principalCommon c)) ≡ c
principalCommonCoordinatesRecover (common2 a b) = refl

k0CommonCoordinatesRecover :
  (c : Common2) →
  common2 (K0.wide (k0Common c)) (K0.left (k0Common c)) ≡ c
k0CommonCoordinatesRecover (common2 a b) = refl

------------------------------------------------------------------------
-- Every common function is forced into that two-coordinate form.
------------------------------------------------------------------------

principalOfCommonIsTwoCoordinate :
  {p : Principal.Old3} {k : K0.Bruhat3} →
  (same : SameCompactFunction p k) →
  principalCommon (common2 (Principal.x1 p) (Principal.x4 p)) ≡ p
principalOfCommonIsTwoCoordinate {p = Principal.old3 x1 x2 x4} same
  rewrite principalFirstTwoMustAgree same = refl

k0OfCommonIsTwoCoordinate :
  {p : Principal.Old3} {k : K0.Bruhat3} →
  (same : SameCompactFunction p k) →
  k0Common (common2 (K0.wide k) (K0.left k)) ≡ k
k0OfCommonIsTwoCoordinate {k = K0.bruhat3 wide left right} same
  rewrite k0TerminalCoordinatesMustAgree same = refl

------------------------------------------------------------------------
-- Concrete witnesses that the two 3-spaces are not identical in the ambient
-- compact model.
------------------------------------------------------------------------

principalBasis1NotK0Invariant :
  (k : K0.Bruhat3) → SameCompactFunction Principal.oldBasis1 k → ⊥
principalBasis1NotK0Invariant k same with principalFirstTwoMustAgree same
... | ()

k0LeftBasis : K0.Bruhat3
k0LeftBasis = K0.bruhat3 0 1 0

k0LeftBasisNotPrincipalInvariant :
  (p : Principal.Old3) → SameCompactFunction p k0LeftBasis → ⊥
k0LeftBasisNotPrincipalInvariant p same with k0TerminalCoordinatesMustAgree same
... | ()

record P11Level44TwoAdicFixedSpaceIntersectionBoundary : Set where
  field
    sameCompactInducedAmbientUsed : Bool
    principalFixedCoordinates : Nat
    k0FixedCoordinates : Nat
    commonIntersectionCoordinates : Nat
    fixedSpacesDefinitionallyIdentical : Bool
    identityInducedThreeDimensionalComparisonExists : Bool
    extraLocalOperatorOrTestVectorStillRequired : Bool

canonicalP11Level44TwoAdicFixedSpaceIntersectionBoundary :
  P11Level44TwoAdicFixedSpaceIntersectionBoundary
canonicalP11Level44TwoAdicFixedSpaceIntersectionBoundary = record
  { sameCompactInducedAmbientUsed = true
  ; principalFixedCoordinates = 3
  ; k0FixedCoordinates = 3
  ; commonIntersectionCoordinates = 2
  ; fixedSpacesDefinitionallyIdentical = false
  ; identityInducedThreeDimensionalComparisonExists = false
  ; extraLocalOperatorOrTestVectorStillRequired = true
  }
