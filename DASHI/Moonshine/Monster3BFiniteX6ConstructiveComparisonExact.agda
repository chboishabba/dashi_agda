module DASHI.Moonshine.Monster3BFiniteX6ConstructiveComparisonExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE EQUALITY / FIRST-DIFFERENCE DECISION ON X6 = F3^6
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorExact as Point

record SameTrit (a b : Trit) : Set where
  constructor sameTrit
  field sameProof : a ≡ b
open SameTrit public

data TritComparison (a b : Trit) : Set where
  same : a ≡ b → TritComparison a b
  different : V.tritEqual a b ≡ false → TritComparison a b

compareTrit : (a b : Trit) → TritComparison a b
compareTrit neg neg = same refl
compareTrit neg zer = different refl
compareTrit neg pos = different refl
compareTrit zer neg = different refl
compareTrit zer zer = same refl
compareTrit zer pos = different refl
compareTrit pos neg = different refl
compareTrit pos zer = different refl
compareTrit pos pos = same refl

data X6Comparison (a b : H.X6) : Set where
  sameX6 : a ≡ b → X6Comparison a b
  differentX6 : Point.CoordinateDifference a b → X6Comparison a b

compareX6 : (a b : H.X6) → X6Comparison a b
compareX6
  (H.x6 a0 a1 a2 a3 a4 a5)
  (H.x6 b0 b1 b2 b3 b4 b5)
  with compareTrit a0 b0
... | different d0 = differentX6 (Point.differs0 d0)
... | same refl with compareTrit a1 b1
...   | different d1 = differentX6 (Point.differs1 d1)
...   | same refl with compareTrit a2 b2
...     | different d2 = differentX6 (Point.differs2 d2)
...     | same refl with compareTrit a3 b3
...       | different d3 = differentX6 (Point.differs3 d3)
...       | same refl with compareTrit a4 b4
...         | different d4 = differentX6 (Point.differs4 d4)
...         | same refl with compareTrit a5 b5
...           | different d5 = differentX6 (Point.differs5 d5)
...           | same refl = sameX6 refl

tritEqualRefl : (a : Trit) → V.tritEqual a a ≡ true
tritEqualRefl neg = refl
tritEqualRefl zer = refl
tritEqualRefl pos = refl

x6EqualRefl : (x : H.X6) → V.x6Equal x x ≡ true
x6EqualRefl (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite tritEqualRefl a0 | tritEqualRefl a1 | tritEqualRefl a2
        | tritEqualRefl a3 | tritEqualRefl a4 | tritEqualRefl a5 = refl

andRightFalse : (b : Bool) → V._and_ b false ≡ false
andRightFalse false = refl
andRightFalse true = refl

record X6ComparisonBoundary : Set where
  constructor x6ComparisonBoundary
  field
    tritComparisonComplete : Bool
    x6ComparisonReturnsEqualityOrDifferenceCoordinate : Bool
    reflexiveBooleanEqualityProved : Bool
open X6ComparisonBoundary public

canonicalX6ComparisonBoundary : X6ComparisonBoundary
canonicalX6ComparisonBoundary = x6ComparisonBoundary true true true
