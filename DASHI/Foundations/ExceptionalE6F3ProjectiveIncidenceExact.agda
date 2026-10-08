module DASHI.Foundations.ExceptionalE6F3ProjectiveIncidenceExact where

------------------------------------------------------------------------
-- PROJECTIVE INCIDENCE DUALITY FOR THE F3 EXTERIOR-SQUARE E6 BRIDGE
--
-- Primitive nonzero null bivectors modulo sign give 40 canonical projective
-- representatives.  Standard nonzero null vectors modulo sign give another
-- 40.  The explicit change of basis from the exterior-square owner induces
-- a two-sided projective recognition and transports the Plucker polar-zero
-- relation to ordinary quadratic orthogonality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.List.Base using (map; concatMap; filterᵇ)

import DASHI.Foundations.ExceptionalE6F3ExteriorSquareRecognitionExact as E
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Canonical sign representatives modulo +/-1.
------------------------------------------------------------------------

canonicalSign5 : Trit → Trit → Trit → Trit → Trit → Bool
canonicalSign5 neg b c d e = false
canonicalSign5 pos b c d e = true
canonicalSign5 zer neg c d e = false
canonicalSign5 zer pos c d e = true
canonicalSign5 zer zer neg d e = false
canonicalSign5 zer zer pos d e = true
canonicalSign5 zer zer zer neg e = false
canonicalSign5 zer zer zer pos e = true
canonicalSign5 zer zer zer zer neg = false
canonicalSign5 zer zer zer zer pos = true
canonicalSign5 zer zer zer zer zer = false

negPrimitive : E.PrimitiveBivector5 → E.PrimitiveBivector5
negPrimitive p =
  E.primitiveBivector5
    (E.neg3 (E.p12 p))
    (E.neg3 (E.p13 p))
    (E.neg3 (E.p14 p))
    (E.neg3 (E.p23 p))
    (E.neg3 (E.p24 p))

negStandard : E.StandardFive → E.StandardFive
negStandard z =
  E.standardFive
    (E.neg3 (E.z1 z))
    (E.neg3 (E.z2 z))
    (E.neg3 (E.z3 z))
    (E.neg3 (E.z4 z))
    (E.neg3 (E.z5 z))

primitiveCanonical : E.PrimitiveBivector5 → Bool
primitiveCanonical p =
  canonicalSign5 (E.p12 p) (E.p13 p) (E.p14 p) (E.p23 p) (E.p24 p)

standardCanonical : E.StandardFive → Bool
standardCanonical z =
  canonicalSign5 (E.z1 z) (E.z2 z) (E.z3 z) (E.z4 z) (E.z5 z)

canonicalizePrimitive : E.PrimitiveBivector5 → E.PrimitiveBivector5
canonicalizePrimitive p with primitiveCanonical p
... | true = p
... | false = negPrimitive p

canonicalizeStandard : E.StandardFive → E.StandardFive
canonicalizeStandard z with standardCanonical z
... | true = z
... | false = negStandard z

primitiveProjectiveNull : E.PrimitiveBivector5 → Bool
primitiveProjectiveNull p = E.primitiveNullNonzero p E.andB primitiveCanonical p

standardProjectiveNull : E.StandardFive → Bool
standardProjectiveNull z = E.standardNullNonzero z E.andB standardCanonical z

primitiveProjectiveEnumeration : List E.PrimitiveBivector5
primitiveProjectiveEnumeration =
  filterᵇ primitiveProjectiveNull E.primitiveEnumeration

standardProjectiveEnumeration : List E.StandardFive
standardProjectiveEnumeration =
  filterᵇ standardProjectiveNull E.standardEnumeration

primitiveProjectiveEnumerationCount :
  Reindex.listLength primitiveProjectiveEnumeration ≡ 40
primitiveProjectiveEnumerationCount = refl

standardProjectiveEnumerationCount :
  Reindex.listLength standardProjectiveEnumeration ≡ 40
standardProjectiveEnumerationCount = refl

------------------------------------------------------------------------
-- Projectivized two-sided chart.
------------------------------------------------------------------------

projectiveToStandard : E.PrimitiveBivector5 → E.StandardFive
projectiveToStandard p = canonicalizeStandard (E.primitiveToStandard p)

projectiveToPrimitive : E.StandardFive → E.PrimitiveBivector5
projectiveToPrimitive z = canonicalizePrimitive (E.standardToPrimitive z)

projectivePrimitiveRoundTripCheck : E.PrimitiveBivector5 → Bool
projectivePrimitiveRoundTripCheck p =
  E.primitiveEq (projectiveToPrimitive (projectiveToStandard p)) p

projectiveStandardRoundTripCheck : E.StandardFive → Bool
projectiveStandardRoundTripCheck z =
  E.standardEq (projectiveToStandard (projectiveToPrimitive z)) z

projectivePrimitivePredicateCheck : E.PrimitiveBivector5 → Bool
projectivePrimitivePredicateCheck p =
  E.boolEq
    (primitiveProjectiveNull p)
    (standardProjectiveNull (projectiveToStandard p))

projectiveStandardPredicateCheck : E.StandardFive → Bool
projectiveStandardPredicateCheck z =
  E.boolEq
    (standardProjectiveNull z)
    (primitiveProjectiveNull (projectiveToPrimitive z))

projectivePrimitiveRoundTripExhaustive :
  E.allTrue (map projectivePrimitiveRoundTripCheck primitiveProjectiveEnumeration) ≡ true
projectivePrimitiveRoundTripExhaustive = refl

projectiveStandardRoundTripExhaustive :
  E.allTrue (map projectiveStandardRoundTripCheck standardProjectiveEnumeration) ≡ true
projectiveStandardRoundTripExhaustive = refl

projectivePrimitivePredicateExhaustive :
  E.allTrue (map projectivePrimitivePredicateCheck primitiveProjectiveEnumeration) ≡ true
projectivePrimitivePredicateExhaustive = refl

projectiveStandardPredicateExhaustive :
  E.allTrue (map projectiveStandardPredicateCheck standardProjectiveEnumeration) ≡ true
projectiveStandardPredicateExhaustive = refl

------------------------------------------------------------------------
-- Incidence / orthogonality relation.
------------------------------------------------------------------------

pluckerPolar : E.PrimitiveBivector5 → E.PrimitiveBivector5 → Trit
pluckerPolar p q =
  E.sum5
    (E.p12 p E.*3 E.p12 q)
    (E.neg3 (E.p13 p E.*3 E.p24 q))
    (E.neg3 (E.p13 q E.*3 E.p24 p))
    (E.p14 p E.*3 E.p23 q)
    (E.p14 q E.*3 E.p23 p)

standardDot : E.StandardFive → E.StandardFive → Trit
standardDot z w =
  E.sum5
    (E.z1 z E.*3 E.z1 w)
    (E.z2 z E.*3 E.z2 w)
    (E.z3 z E.*3 E.z3 w)
    (E.z4 z E.*3 E.z4 w)
    (E.z5 z E.*3 E.z5 w)

lineIncidence : E.PrimitiveBivector5 → E.PrimitiveBivector5 → Bool
lineIncidence p q = E.tritEq (pluckerPolar p q) zer

nullOrthogonality : E.StandardFive → E.StandardFive → Bool
nullOrthogonality z w = E.tritEq (standardDot z w) zer

incidenceOrthogonalityCheck : E.PrimitiveBivector5 → E.PrimitiveBivector5 → Bool
incidenceOrthogonalityCheck p q =
  E.boolEq
    (lineIncidence p q)
    (nullOrthogonality (projectiveToStandard p) (projectiveToStandard q))

incidenceOrthogonalityChecks : List Bool
incidenceOrthogonalityChecks =
  concatMap
    (λ p → map (incidenceOrthogonalityCheck p) primitiveProjectiveEnumeration)
    primitiveProjectiveEnumeration

incidenceOrthogonalityExhaustive :
  E.allTrue incidenceOrthogonalityChecks ≡ true
incidenceOrthogonalityExhaustive = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ExceptionalE6F3ProjectiveIncidenceBoundary : Set where
  constructor exceptional-e6-f3-projective-incidence-boundary
  field
    primitiveProjectiveCount40 : Bool
    standardProjectiveCount40 : Bool
    projectiveTwoSidedRecognitionPaid : Bool
    incidenceOrthogonalityIntertwiningPaid : Bool
    rawT4PointGeometryIdentified : Bool
open ExceptionalE6F3ProjectiveIncidenceBoundary public

canonicalExceptionalE6F3ProjectiveIncidenceBoundary :
  ExceptionalE6F3ProjectiveIncidenceBoundary
canonicalExceptionalE6F3ProjectiveIncidenceBoundary =
  exceptional-e6-f3-projective-incidence-boundary true true true true false
