module DASHI.Foundations.ExceptionalE6F3GeneratorActionExact where

------------------------------------------------------------------------
-- GENERATOR-LEVEL PGSp4(3) / W(E6) EXTERIOR-SQUARE ACTION BRIDGE
--
-- Six explicit 4x4 multiplier-minus-one symplectic similitudes lift the six
-- reduced E6 simple reflections.  Their exterior-square action on primitive
-- bivectors commutes with the standard five-coordinate E6 action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.List.Base using (map; concatMap)

import DASHI.Foundations.ExceptionalE6F3ExteriorSquareRecognitionExact as E

record Matrix4 : Set where
  constructor matrix4
  field r1 r2 r3 r4 : E.F3Four
open Matrix4 public

record Matrix5 : Set where
  constructor matrix5
  field s1 s2 s3 s4 s5 : E.StandardFive
open Matrix5 public

dot4 : E.F3Four → E.F3Four → Trit
dot4 a b =
  E.sum4
    (E._*3_ (E.x1 a) (E.x1 b))
    (E._*3_ (E.x2 a) (E.x2 b))
    (E._*3_ (E.x3 a) (E.x3 b))
    (E._*3_ (E.x4 a) (E.x4 b))

dot5 : E.StandardFive → E.StandardFive → Trit
dot5 a b =
  E.sum5
    (E._*3_ (E.z1 a) (E.z1 b))
    (E._*3_ (E.z2 a) (E.z2 b))
    (E._*3_ (E.z3 a) (E.z3 b))
    (E._*3_ (E.z4 a) (E.z4 b))
    (E._*3_ (E.z5 a) (E.z5 b))

apply4 : Matrix4 → E.F3Four → E.F3Four
apply4 m v =
  E.f3four
    (dot4 (r1 m) v)
    (dot4 (r2 m) v)
    (dot4 (r3 m) v)
    (dot4 (r4 m) v)

apply5 : Matrix5 → E.StandardFive → E.StandardFive
apply5 m v =
  E.standardFive
    (dot5 (s1 m) v)
    (dot5 (s2 m) v)
    (dot5 (s3 m) v)
    (dot5 (s4 m) v)
    (dot5 (s5 m) v)

primitiveAsFive : E.PrimitiveBivector5 → E.StandardFive
primitiveAsFive p = E.standardFive (E.p12 p) (E.p13 p) (E.p14 p) (E.p23 p) (E.p24 p)

fiveAsPrimitive : E.StandardFive → E.PrimitiveBivector5
fiveAsPrimitive z = E.primitiveBivector5 (E.z1 z) (E.z2 z) (E.z3 z) (E.z4 z) (E.z5 z)

applyPrimitive5 : Matrix5 → E.PrimitiveBivector5 → E.PrimitiveBivector5
applyPrimitive5 m p = fiveAsPrimitive (apply5 m (primitiveAsFive p))

data SimpleE6Generator : Set where
  s0 s1 s2 s3 s4 s5 : SimpleE6Generator

generators : List SimpleE6Generator
generators = s0 ∷ s1 ∷ s2 ∷ s3 ∷ s4 ∷ s5 ∷ []

v4 : Trit → Trit → Trit → Trit → E.F3Four
v4 = E.f3four

v5 : Trit → Trit → Trit → Trit → Trit → E.StandardFive
v5 = E.standardFive

lift4 : SimpleE6Generator → Matrix4
lift4 s0 = matrix4
  (v4 neg zer neg neg) (v4 zer neg neg pos)
  (v4 pos pos pos zer) (v4 pos neg zer pos)
lift4 s1 = matrix4
  (v4 zer zer neg zer) (v4 zer zer zer pos)
  (v4 pos zer zer zer) (v4 zer neg zer zer)
lift4 s2 = matrix4
  (v4 zer zer pos pos) (v4 zer zer pos zer)
  (v4 zer neg zer zer) (v4 neg pos zer zer)
lift4 s3 = matrix4
  (v4 zer zer neg pos) (v4 zer zer neg neg)
  (v4 neg neg zer zer) (v4 pos neg zer zer)
lift4 s4 = matrix4
  (v4 pos zer neg neg) (v4 zer pos zer neg)
  (v4 neg pos neg zer) (v4 zer neg zer neg)
lift4 s5 = matrix4
  (v4 zer zer pos pos) (v4 zer zer neg pos)
  (v4 pos neg zer zer) (v4 pos pos zer zer)

primitiveActionMatrix : SimpleE6Generator → Matrix5
primitiveActionMatrix s0 = matrix5
  (v5 zer pos neg neg neg) (v5 pos zer pos pos pos)
  (v5 neg pos zer neg neg) (v5 neg pos neg zer neg) (v5 neg pos neg neg zer)
primitiveActionMatrix s1 = matrix5
  (v5 pos zer zer zer zer) (v5 zer pos zer zer zer)
  (v5 zer zer zer neg zer) (v5 zer zer neg zer zer) (v5 zer zer zer zer pos)
primitiveActionMatrix s2 = matrix5
  (v5 pos zer zer zer zer) (v5 zer zer zer pos pos)
  (v5 zer pos pos neg neg) (v5 zer zer zer pos zer) (v5 zer pos zer neg zer)
primitiveActionMatrix s3 = matrix5
  (v5 pos zer zer zer zer) (v5 zer neg pos neg pos)
  (v5 zer pos neg neg pos) (v5 zer neg neg neg neg) (v5 zer pos pos neg neg)
primitiveActionMatrix s4 = matrix5
  (v5 zer zer neg pos pos) (v5 neg pos neg pos pos)
  (v5 pos zer neg neg neg) (v5 neg zer neg neg pos) (v5 zer zer zer zer pos)
primitiveActionMatrix s5 = matrix5
  (v5 pos zer zer zer zer) (v5 zer neg neg pos pos)
  (v5 zer neg neg neg neg) (v5 zer pos neg neg pos) (v5 zer pos neg pos neg)

weyl5 : SimpleE6Generator → Matrix5
weyl5 s0 = matrix5
  (v5 pos zer zer zer zer) (v5 zer pos zer zer zer)
  (v5 zer zer pos zer zer) (v5 zer zer zer zer pos) (v5 zer zer zer pos zer)
weyl5 s1 = matrix5
  (v5 pos zer zer zer zer) (v5 zer pos zer zer zer)
  (v5 zer zer zer pos zer) (v5 zer zer pos zer zer) (v5 zer zer zer zer pos)
weyl5 s2 = matrix5
  (v5 zer zer neg zer zer) (v5 zer pos zer zer zer)
  (v5 neg zer zer zer zer) (v5 zer zer zer pos zer) (v5 zer zer zer zer pos)
weyl5 s3 = matrix5
  (v5 zer neg zer zer zer) (v5 neg zer zer zer zer)
  (v5 zer zer pos zer zer) (v5 zer zer zer pos zer) (v5 zer zer zer zer pos)
weyl5 s4 = matrix5
  (v5 zer neg pos pos pos) (v5 neg zer pos pos pos)
  (v5 pos pos zer neg neg) (v5 pos pos neg zer neg) (v5 pos pos neg neg zer)
weyl5 s5 = matrix5
  (v5 zer pos zer zer zer) (v5 pos zer zer zer zer)
  (v5 zer zer pos zer zer) (v5 zer zer zer pos zer) (v5 zer zer zer zer pos)

fourEnumeration : List E.F3Four
fourEnumeration =
  concatMap (λ a →
  concatMap (λ b →
  concatMap (λ c →
  map (λ d → E.f3four a b c d) E.trits)
  E.trits) E.trits) E.trits

similitudeCheck : SimpleE6Generator → E.F3Four → E.F3Four → Bool
similitudeCheck g u v =
  E.tritEq
    (E.symplectic4 (apply4 (lift4 g) u) (apply4 (lift4 g) v))
    (E.neg3 (E.symplectic4 u v))

wedgeCovarianceCheck : SimpleE6Generator → E.F3Four → E.F3Four → Bool
wedgeCovarianceCheck g u v =
  E.primitiveEq
    (E.wedgePrimitiveCoordinates (apply4 (lift4 g) u) (apply4 (lift4 g) v))
    (applyPrimitive5 (primitiveActionMatrix g) (E.wedgePrimitiveCoordinates u v))

standardIntertwiningCheck : SimpleE6Generator → E.PrimitiveBivector5 → Bool
standardIntertwiningCheck g p =
  E.standardEq
    (E.primitiveToStandard (applyPrimitive5 (primitiveActionMatrix g) p))
    (apply5 (weyl5 g) (E.primitiveToStandard p))

weylQuadraticCheck : SimpleE6Generator → E.StandardFive → Bool
weylQuadraticCheck g z =
  E.tritEq (E.standardQ (apply5 (weyl5 g) z)) (E.standardQ z)

similitudeChecks : List Bool
similitudeChecks =
  concatMap
    (λ g → concatMap (λ u → map (similitudeCheck g u) fourEnumeration) fourEnumeration)
    generators

wedgeCovarianceChecks : List Bool
wedgeCovarianceChecks =
  concatMap
    (λ g → concatMap (λ u → map (wedgeCovarianceCheck g u) fourEnumeration) fourEnumeration)
    generators

standardIntertwiningChecks : List Bool
standardIntertwiningChecks =
  concatMap (λ g → map (standardIntertwiningCheck g) E.primitiveEnumeration) generators

weylQuadraticChecks : List Bool
weylQuadraticChecks =
  concatMap (λ g → map (weylQuadraticCheck g) E.standardEnumeration) generators

similitudeExhaustive : E.allTrue similitudeChecks ≡ true
similitudeExhaustive = refl

wedgeCovarianceExhaustive : E.allTrue wedgeCovarianceChecks ≡ true
wedgeCovarianceExhaustive = refl

standardIntertwiningExhaustive : E.allTrue standardIntertwiningChecks ≡ true
standardIntertwiningExhaustive = refl

weylQuadraticExhaustive : E.allTrue weylQuadraticChecks ≡ true
weylQuadraticExhaustive = refl

record ExceptionalE6F3GeneratorActionBoundary : Set where
  constructor exceptional-e6-f3-generator-action-boundary
  field
    sixExplicitSimilitudeLifts : Bool
    multiplierMinusOnePaid : Bool
    wedgeCovariancePaid : Bool
    standardWeylIntertwiningPaid : Bool
    standardQuadraticPreserved : Bool
    groupClosureOrder51840Paid : Bool
    projectiveKernelPlusMinusIPaid : Bool
open ExceptionalE6F3GeneratorActionBoundary public

canonicalExceptionalE6F3GeneratorActionBoundary :
  ExceptionalE6F3GeneratorActionBoundary
canonicalExceptionalE6F3GeneratorActionBoundary =
  exceptional-e6-f3-generator-action-boundary true true true true true false false
