module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality, specialized to the finite eight-point
-- periodic carrier.  The historical theorem in this module carries the
-- weaker factor 64 used by the legacy Luo finite-L2 path.
--
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ELABORATION REFACTOR
--
-- The repository now has the stronger arbitrary-finite, constant-one,
-- radical-free Holder theorem in
-- NSTriadKNLuoFiniteSixThreeHolderConstantOneV2Exact.  The former version of
-- this file reproved a weaker eight-point factor-64 estimate with a large
-- collection of 8/16-variable ring-solver normalisations; profiling showed
-- that legacy proof reaching roughly 14 GB RSS by itself.
--
-- This module is now deliberately a THIN BACKWARD-COMPATIBILITY ADAPTER:
--
--   constant-one finite Holder
--       -> specialize to the literal eight samples
--       -> weaken the nonnegative RHS by 1 <= 64.
--
-- The public EightSixThreeData/mass/theorem surface used by legacy consumers
-- is preserved.  No theorem is postulated and no physical NS hypothesis is
-- added.  Consumers no longer need the expensive historical proof graph.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeHolderConstantOneV2Exact as Strong

three four sixteen sixtyFour : ℚ
three = Int.+ 3 / 1
four = Int.+ 4 / 1
sixteen = Int.+ 16 / 1
sixtyFour = Int.+ 64 / 1

threeNonnegative : 0ℚ ≤ three
threeNonnegative = toWitness {a? = 0ℚ ≤? three} _

fourNonnegative : 0ℚ ≤ four
fourNonnegative = toWitness {a? = 0ℚ ≤? four} _

sixtyFourNonnegative : 0ℚ ≤ sixtyFour
sixtyFourNonnegative = toWitness {a? = 0ℚ ≤? sixtyFour} _

oneBelowSixtyFour : 1ℚ ≤ sixtyFour
oneBelowSixtyFour = toWitness {a? = 1ℚ ≤? sixtyFour} _

cube sixth : ℚ → ℚ
cube = Strong.cube
sixth = Strong.sixth

cubeMeaning : (value : ℚ) → cube value ≡ value * value * value
cubeMeaning value = refl

cubeNonnegative : (value : ℚ) → 0ℚ ≤ value → 0ℚ ≤ cube value
cubeNonnegative = Strong.cubeNonnegative

sixthNonnegative : (value : ℚ) → 0ℚ ≤ value → 0ℚ ≤ sixth value
sixthNonnegative value valueNN =
  Strong.pairProductNonnegative
    (cube value) (cube value)
    (cubeNonnegative value valueNN)
    (cubeNonnegative value valueNN)

scaleBound :
  (scale left right : ℚ) →
  0ℚ ≤ scale → left ≤ right → scale * left ≤ scale * right
scaleBound = Strong.scaleBound

------------------------------------------------------------------------
-- The only legacy algebraic helper still used by downstream kernel modules:
-- (x+y)^3 <= 4(x^3+y^3) for x,y >= 0.
------------------------------------------------------------------------

cubePairIdentityExpanded :
  (left right : ℚ) →
  cube (left + right)
    + three * (left + right) * ((left - right) * (left - right))
  ≡ four * (cube left + cube right)
cubePairIdentityExpanded left right =
  solve (left ∷ right ∷ [])

cubePairBound :
  (left right : ℚ) →
  0ℚ ≤ left → 0ℚ ≤ right →
  cube (left + right) ≤ four * (cube left + cube right)
cubePairBound left right leftNN rightNN =
  let
    sumNN = L2.addNonnegative leftNN rightNN
    squareDifferenceNN = L2.squareNonnegative (left - right)

    defectNN :
      0ℚ ≤ three * (left + right) * L2.square (left - right)
    defectNN =
      Strong.pairProductNonnegative
        (three * (left + right))
        (L2.square (left - right))
        (Strong.pairProductNonnegative
          three (left + right) threeNonnegative sumNN)
        squareDifferenceNN

    addDefect :
      cube (left + right)
      ≤ cube (left + right)
        + three * (left + right) * L2.square (left - right)
    addDefect =
      subst
        (λ lower →
          lower
          ≤ cube (left + right)
            + three * (left + right) * L2.square (left - right))
        (ℚP.+-identityʳ (cube (left + right)))
        (ℚP.+-monoʳ-≤ (cube (left + right)) defectNN)

    identity :
      cube (left + right)
        + three * (left + right) * L2.square (left - right)
      ≡ four * (cube left + cube right)
    identity = cubePairIdentityExpanded left right
  in
  subst (λ upper → cube (left + right) ≤ upper) identity addDefect

------------------------------------------------------------------------
-- Legacy eight-point carrier.
------------------------------------------------------------------------

record EightSixThreeData : Set where
  constructor eight-six-three-data
  field
    a0 a1 a2 a3 a4 a5 a6 a7 : ℚ
    b0 b1 b2 b3 b4 b5 b6 b7 : ℚ
    a0NN : 0ℚ ≤ a0
    a1NN : 0ℚ ≤ a1
    a2NN : 0ℚ ≤ a2
    a3NN : 0ℚ ≤ a3
    a4NN : 0ℚ ≤ a4
    a5NN : 0ℚ ≤ a5
    a6NN : 0ℚ ≤ a6
    a7NN : 0ℚ ≤ a7
    b0NN : 0ℚ ≤ b0
    b1NN : 0ℚ ≤ b1
    b2NN : 0ℚ ≤ b2
    b3NN : 0ℚ ≤ b3
    b4NN : 0ℚ ≤ b4
    b5NN : 0ℚ ≤ b5
    b6NN : 0ℚ ≤ b6
    b7NN : 0ℚ ≤ b7

open EightSixThreeData public

holderPairs : EightSixThreeData → List Strong.NonnegativePair
holderPairs dataSet =
    Strong.nonnegative-pair (a0 dataSet) (b0 dataSet) (a0NN dataSet) (b0NN dataSet)
  ∷ Strong.nonnegative-pair (a1 dataSet) (b1 dataSet) (a1NN dataSet) (b1NN dataSet)
  ∷ Strong.nonnegative-pair (a2 dataSet) (b2 dataSet) (a2NN dataSet) (b2NN dataSet)
  ∷ Strong.nonnegative-pair (a3 dataSet) (b3 dataSet) (a3NN dataSet) (b3NN dataSet)
  ∷ Strong.nonnegative-pair (a4 dataSet) (b4 dataSet) (a4NN dataSet) (b4NN dataSet)
  ∷ Strong.nonnegative-pair (a5 dataSet) (b5 dataSet) (a5NN dataSet) (b5NN dataSet)
  ∷ Strong.nonnegative-pair (a6 dataSet) (b6 dataSet) (a6NN dataSet) (b6NN dataSet)
  ∷ Strong.nonnegative-pair (a7 dataSet) (b7 dataSet) (a7NN dataSet) (b7NN dataSet)
  ∷ []

productSquare : ℚ → ℚ → ℚ
productSquare a b = L2.square (a * b)

productL2Squared : EightSixThreeData → ℚ
productL2Squared dataSet =
  Strong.sumBy Strong.productMass (holderPairs dataSet)

lowSixthMass : EightSixThreeData → ℚ
lowSixthMass dataSet =
  Strong.sumBy Strong.leftSixthMass (holderPairs dataSet)

highCubeMass : EightSixThreeData → ℚ
highCubeMass dataSet =
  Strong.sumBy Strong.rightCubeMass (holderPairs dataSet)

sumByNonnegative :
  ∀ {A : Set} (value : A → ℚ) (items : List A) →
  ((item : A) → 0ℚ ≤ value item) →
  0ℚ ≤ Strong.sumBy value items
sumByNonnegative value [] pointwise = ℚP.≤-refl
sumByNonnegative value (item ∷ items) pointwise =
  L2.addNonnegative
    (pointwise item)
    (sumByNonnegative value items pointwise)

leftSixthMassNonnegative :
  (pair : Strong.NonnegativePair) →
  0ℚ ≤ Strong.leftSixthMass pair
leftSixthMassNonnegative pair =
  sixthNonnegative (Strong.left pair) (Strong.leftNonnegative pair)

rightCubeMassNonnegative :
  (pair : Strong.NonnegativePair) →
  0ℚ ≤ Strong.rightCubeMass pair
rightCubeMassNonnegative pair =
  cubeNonnegative (Strong.right pair) (Strong.rightNonnegative pair)

legacyRightHandSideNonnegative :
  (dataSet : EightSixThreeData) →
  0ℚ ≤ lowSixthMass dataSet
    * (highCubeMass dataSet * highCubeMass dataSet)
legacyRightHandSideNonnegative dataSet =
  let
    lowNN = sumByNonnegative Strong.leftSixthMass
      (holderPairs dataSet) leftSixthMassNonnegative
    highNN = sumByNonnegative Strong.rightCubeMass
      (holderPairs dataSet) rightCubeMassNonnegative
    highSquareNN =
      Strong.pairProductNonnegative
        (highCubeMass dataSet) (highCubeMass dataSet) highNN highNN
  in
  Strong.pairProductNonnegative
    (lowSixthMass dataSet)
    (highCubeMass dataSet * highCubeMass dataSet)
    lowNN highSquareNN

------------------------------------------------------------------------
-- Main regression theorem.
--
-- Strong.finiteSixThreeHolderRadicalFree already proves the same statement
-- with coefficient 1 on an arbitrary finite list.  We only weaken the RHS to
-- the historical factor 64 expected by the old centered-kernel consumer.
------------------------------------------------------------------------

eightPointSixThreeHolderRadicalFree :
  (dataSet : EightSixThreeData) →
  cube (productL2Squared dataSet)
  ≤ sixtyFour
    * lowSixthMass dataSet
    * (highCubeMass dataSet * highCubeMass dataSet)
eightPointSixThreeHolderRadicalFree dataSet =
  let
    rhs = lowSixthMass dataSet
      * (highCubeMass dataSet * highCubeMass dataSet)

    sharp : cube (productL2Squared dataSet) ≤ rhs
    sharp = Strong.finiteSixThreeHolderRadicalFree (holderPairs dataSet)

    rhsNN : 0ℚ ≤ rhs
    rhsNN = legacyRightHandSideNonnegative dataSet

    weaken : 1ℚ * rhs ≤ sixtyFour * rhs
    weaken =
      L2.nonnegativeProductMonotone
        ℚP.0≤1 rhsNN
        sixtyFourNonnegative rhsNN
        oneBelowSixtyFour ℚP.≤-refl

    rhsBelowScaled : rhs ≤ sixtyFour * rhs
    rhsBelowScaled =
      subst (λ lower → lower ≤ sixtyFour * rhs)
        (ℚP.*-identityˡ rhs) weaken

    endpoint :
      sixtyFour * rhs
      ≡ sixtyFour * lowSixthMass dataSet
        * (highCubeMass dataSet * highCubeMass dataSet)
    endpoint = solve (lowSixthMass dataSet ∷ highCubeMass dataSet ∷ [])
  in
  ℚP.≤-trans sharp
    (subst
      (λ upper → rhs ≤ upper)
      endpoint
      rhsBelowScaled)
