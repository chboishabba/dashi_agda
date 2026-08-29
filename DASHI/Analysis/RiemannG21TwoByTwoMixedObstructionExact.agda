module DASHI.Analysis.RiemannG21TwoByTwoMixedObstructionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact finite counterexample to the naive 2x2 determinant idea.
--
-- We encode an oriented determinant by its positive and negative monomials
-- rather than subtracting in Nat:
--
--   det [[a,c],[b,d]]  ~  (a*d , b*c).
--
-- Equality of these codes is stronger than equality after subtraction and is
-- sufficient for the regression witness below.
------------------------------------------------------------------------

Vec2 : Set
Vec2 = Nat × Nat

record OrientedDetCode : Set where
  constructor detCode
  field
    positiveMonomial : Nat
    negativeMonomial : Nat

open OrientedDetCode public

det2Code : Vec2 → Vec2 → OrientedDetCode
det2Code (a , b) (c , d) = detCode (a * d) (b * c)

_+v_ : Vec2 → Vec2 → Vec2
(a , b) +v (c , d) = (a + c , b + d)

commonPole : Vec2
commonPole = 1 , 0

zeroResidual : Vec2
zeroResidual = 0 , 0

transverseResidual : Vec2
transverseResidual = 0 , 1

responseLeft responseRight : Vec2
responseLeft = commonPole +v zeroResidual
responseRight = commonPole +v transverseResidual

purePoleRankOneDeterminant :
  det2Code commonPole commonPole ≡ detCode 0 0
purePoleRankOneDeterminant = refl

mixedResponseDeterminantSurvives :
  det2Code responseLeft responseRight ≡ detCode 1 0
mixedResponseDeterminantSurvives = refl

rankOnePoleDoesNotKillMixedTwoByTwoDeterminant :
  det2Code responseLeft responseRight
  ≡ det2Code commonPole commonPole
  → ⊥
rankOnePoleDoesNotKillMixedTwoByTwoDeterminant ()

record TwoByTwoMixedObstructionBoundary : Set where
  constructor twoByTwoMixedObstructionBoundary
  field
    purePoleRankOne : Bool
    purePoleRankOneIsTrue : purePoleRankOne ≡ true

    mixedTermCanSurvive : Bool
    mixedTermCanSurviveIsTrue : mixedTermCanSurvive ≡ true

    twoByTwoPoleRankOneSufficesForG21 : Bool
    twoByTwoPoleRankOneSufficesForG21IsFalse :
      twoByTwoPoleRankOneSufficesForG21 ≡ false

canonicalTwoByTwoMixedObstructionBoundary :
  TwoByTwoMixedObstructionBoundary
canonicalTwoByTwoMixedObstructionBoundary =
  twoByTwoMixedObstructionBoundary
    true refl
    true refl
    false refl
