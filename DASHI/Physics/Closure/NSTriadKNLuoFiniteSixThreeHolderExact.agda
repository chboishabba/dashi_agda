module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeHolderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality on a finite counting-measure space.
-- Repository-original radical-free Agda proof; no DOI is assigned.
--
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the exact finite, dimension-free radical-free form of
--
--   ||a b||_2 <= ||a||_6 ||b||_3.
--
-- For an arbitrary finite list of nonnegative pairs (a_i,b_i), the theorem is
--
--   (sum_i (a_i b_i)^2)^3
--     <= (sum_i a_i^6) (sum_i b_i^3)^2.
--
-- No cardinality constant appears.  The proof expands both sides over triples
-- of indices and uses the polynomial AM--GM identity
--
--   3xyz <= x^3+y^3+z^3.
--
-- For each triple i,j,k choose
--
--   x = a_i^2 b_j b_k,
--   y = a_j^2 b_k b_i,
--   z = a_k^2 b_i b_j.
--
-- Then xyz is the corresponding term in the cube of the L2 product mass,
-- while x^3,y^3,z^3 are cyclic terms in A6 B3^2.  Summing over all triples
-- and cancelling the positive factor three gives Hölder with constant one.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

three oneThird half : ℚ
three = Int.+ 3 / 1
oneThird = Int.+ 1 / 3
half = Int.+ 1 / 2

oneThirdNonnegative : 0ℚ ≤ oneThird
oneThirdNonnegative = toWitness {a? = 0ℚ ≤? oneThird} _

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

square cube sixth : ℚ → ℚ
square value = value * value
cube value = value * value * value
sixth value = cube value * cube value

record NonnegativePair : Set where
  constructor nonnegative-pair
  field
    left right : ℚ
    leftNonnegative : 0ℚ ≤ left
    rightNonnegative : 0ℚ ≤ right

open NonnegativePair public

sumBy : ∀ {A : Set} → (A → ℚ) → List A → ℚ
sumBy value [] = 0ℚ
sumBy value (item ∷ items) = value item + sumBy value items

sumByMonotone :
  ∀ {A : Set}
    (lower upper : A → ℚ)
    (items : List A) →
  ((item : A) → lower item ≤ upper item) →
  sumBy lower items ≤ sumBy upper items
sumByMonotone lower upper [] pointwise = ℚₚ.≤-refl
sumByMonotone lower upper (item ∷ items) pointwise =
  ℚₚ.+-mono-≤
    (pointwise item)
    (sumByMonotone lower upper items pointwise)

sumByAdd :
  ∀ {A : Set}
    (first second : A → ℚ)
    (items : List A) →
  sumBy (λ item → first item + second item) items
  ≡ sumBy first items + sumBy second items
sumByAdd first second [] = solve []
sumByAdd first second (item ∷ items)
  rewrite sumByAdd first second items =
  solve
    ( first item ∷ second item
    ∷ sumBy first items ∷ sumBy second items ∷ [])

sumByScaleLeft :
  ∀ {A : Set}
    (scale : ℚ)
    (value : A → ℚ)
    (items : List A) →
  sumBy (λ item → scale * value item) items
  ≡ scale * sumBy value items
sumByScaleLeft scale value [] = solve []
sumByScaleLeft scale value (item ∷ items)
  rewrite sumByScaleLeft scale value items =
  solve (scale ∷ value item ∷ sumBy value items ∷ [])

sumByScaleRight :
  ∀ {A : Set}
    (value : A → ℚ)
    (items : List A)
    (scale : ℚ) →
  sumBy (λ item → value item * scale) items
  ≡ sumBy value items * scale
sumByScaleRight value [] scale = solve []
sumByScaleRight value (item ∷ items) scale
  rewrite sumByScaleRight value items scale =
  solve (value item ∷ sumBy value items ∷ scale ∷ [])

sum2 :
  ∀ {A B : Set} →
  (A → B → ℚ) → List A → List B → ℚ
sum2 value first second =
  sumBy (λ leftItem → sumBy (value leftItem) second) first

sum3 :
  ∀ {A B C : Set} →
  (A → B → C → ℚ) →
  List A → List B → List C → ℚ
sum3 value first second third =
  sumBy
    (λ firstItem →
      sumBy
        (λ secondItem →
          sumBy (value firstItem secondItem) third)
        second)
    first

sum3Monotone :
  ∀ {A B C : Set}
    (lower upper : A → B → C → ℚ)
    (first : List A)
    (second : List B)
    (third : List C) →
  ((a : A) → (b : B) → (c : C) →
    lower a b c ≤ upper a b c) →
  sum3 lower first second third
  ≤ sum3 upper first second third
sum3Monotone lower upper [] second third pointwise = ℚₚ.≤-refl
sum3Monotone lower upper (a ∷ first) second third pointwise =
  ℚₚ.+-mono-≤
    (sumByMonotone
      (λ b → sumBy (lower a b) third)
      (λ b → sumBy (upper a b) third)
      second
      (λ b →
        sumByMonotone
          (lower a b)
          (upper a b)
          third
          (pointwise a b)))
    (sum3Monotone lower upper first second third pointwise)

sum3Add :
  ∀ {A B C : Set}
    (firstValue secondValue : A → B → C → ℚ)
    (first : List A)
    (second : List B)
    (third : List C) →
  sum3
    (λ a b c → firstValue a b c + secondValue a b c)
    first second third
  ≡ sum3 firstValue first second third
    + sum3 secondValue first second third
sum3Add firstValue secondValue [] second third = solve []
sum3Add firstValue secondValue (a ∷ first) second third
  rewrite sum3Add firstValue secondValue first second third =
  let
    inner :
      sumBy
        (λ b →
          sumBy
            (λ c → firstValue a b c + secondValue a b c)
            third)
        second
      ≡ sumBy
          (λ b → sumBy (firstValue a b) third)
          second
        + sumBy
          (λ b → sumBy (secondValue a b) third)
          second
    inner =
      let
        perSecond :
          (b : _) →
          sumBy
            (λ c → firstValue a b c + secondValue a b c)
            third
          ≡ sumBy (firstValue a b) third
            + sumBy (secondValue a b) third
        perSecond b =
          sumByAdd (firstValue a b) (secondValue a b) third
      in
      beginInner perSecond
  in
  solve
    ( sumBy (λ b → sumBy (firstValue a b) third) second
    ∷ sumBy (λ b → sumBy (secondValue a b) third) second
    ∷ sum3 firstValue first second third
    ∷ sum3 secondValue first second third
    ∷ [])
  where
    beginInner :
      ((b : _) →
        sumBy
          (λ c → firstValue a b c + secondValue a b c)
          third
        ≡ sumBy (firstValue a b) third
          + sumBy (secondValue a b) third) →
      sumBy
        (λ b →
          sumBy
            (λ c → firstValue a b c + secondValue a b c)
            third)
        second
      ≡ sumBy
          (λ b → sumBy (firstValue a b) third)
          second
        + sumBy
          (λ b → sumBy (secondValue a b) third)
          second
    beginInner pointwise =
      let
        rewriteOuter :
          sumBy
            (λ b →
              sumBy
                (λ c → firstValue a b c + secondValue a b c)
                third)
            second
          ≡ sumBy
              (λ b →
                sumBy (firstValue a b) third
                + sumBy (secondValue a b) third)
              second
        rewriteOuter =
          sumByCong
            (λ b →
              sumBy
                (λ c → firstValue a b c + secondValue a b c)
                third)
            (λ b →
              sumBy (firstValue a b) third
              + sumBy (secondValue a b) third)
            second
            pointwise
      in
      transEq
        rewriteOuter
        (sumByAdd
          (λ b → sumBy (firstValue a b) third)
          (λ b → sumBy (secondValue a b) third)
          second)

sumByCong :
  ∀ {A : Set}
    (first second : A → ℚ)
    (items : List A) →
  ((item : A) → first item ≡ second item) →
  sumBy first items ≡ sumBy second items
sumByCong first second [] pointwise = refl
sumByCong first second (item ∷ items) pointwise
  rewrite pointwise item
        | sumByCong first second items pointwise =
  refl

transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl refl = refl

sum2ProductFactorizes :
  ∀ {A B : Set}
    (firstValue : A → ℚ)
    (secondValue : B → ℚ)
    (first : List A)
    (second : List B) →
  sum2
    (λ a b → firstValue a * secondValue b)
    first second
  ≡ sumBy firstValue first * sumBy secondValue second
sum2ProductFactorizes firstValue secondValue [] second = solve []
sum2ProductFactorizes firstValue secondValue (a ∷ first) second
  rewrite sumByScaleLeft
            (firstValue a) secondValue second
        | sum2ProductFactorizes firstValue secondValue first second =
  solve
    ( firstValue a
    ∷ sumBy firstValue first
    ∷ sumBy secondValue second
    ∷ [])

sum3ProductFactorizes :
  ∀ {A B C : Set}
    (firstValue : A → ℚ)
    (secondValue : B → ℚ)
    (thirdValue : C → ℚ)
    (first : List A)
    (second : List B)
    (third : List C) →
  sum3
    (λ a b c →
      firstValue a * secondValue b * thirdValue c)
    first second third
  ≡ sumBy firstValue first
    * sumBy secondValue second
    * sumBy thirdValue third
sum3ProductFactorizes
  firstValue secondValue thirdValue [] second third = solve []
sum3ProductFactorizes
  firstValue secondValue thirdValue (a ∷ first) second third
  rewrite sum2ProductFactorizes secondValue thirdValue second third
        | sumByScaleLeft
            (firstValue a)
            (λ b → sumBy
              (λ c → secondValue b * thirdValue c)
              third)
            second
        | sum3ProductFactorizes
            firstValue secondValue thirdValue first second third =
  solve
    ( firstValue a
    ∷ sumBy firstValue first
    ∷ sumBy secondValue second
    ∷ sumBy thirdValue third
    ∷ [])

-- Polynomial AM--GM for three nonnegative rationals.
threeVariableAMGM :
  (x y z : ℚ) →
  0ℚ ≤ x → 0ℚ ≤ y → 0ℚ ≤ z →
  three * (x * y * z)
  ≤ cube x + cube y + cube z
threeVariableAMGM x y z xNN yNN zNN =
  let
    sumNN =
      L2.addNonnegative (L2.addNonnegative xNN yNN) zNN

    squareSumNN =
      L2.addNonnegative
        (L2.addNonnegative
          (L2.squareNonnegative (x - y))
          (L2.squareNonnegative (y - z)))
        (L2.squareNonnegative (z - x))

    halfSquareSumNN :
      0ℚ ≤ half
        * (L2.square (x - y)
          + L2.square (y - z)
          + L2.square (z - x))
    halfSquareSumNN =
      let
        instance
          halfNNI = nonNegative halfNonnegative
          squareSumNNI = nonNegative squareSumNN
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              half
              (L2.square (x - y)
                + L2.square (y - z)
                + L2.square (z - x))
      in
      ℚₚ.nonNegative⁻¹
        (half
          * (L2.square (x - y)
            + L2.square (y - z)
            + L2.square (z - x)))

    defectNN :
      0ℚ ≤ (x + y + z)
        * (half
          * (L2.square (x - y)
            + L2.square (y - z)
            + L2.square (z - x)))
    defectNN =
      let
        instance
          sumNNI = nonNegative sumNN
          halfSquareNNI = nonNegative halfSquareSumNN
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (x + y + z)
              (half
                * (L2.square (x - y)
                  + L2.square (y - z)
                  + L2.square (z - x)))
      in
      ℚₚ.nonNegative⁻¹
        ((x + y + z)
          * (half
            * (L2.square (x - y)
              + L2.square (y - z)
              + L2.square (z - x))))

    addDefect :
      three * (x * y * z)
      ≤ three * (x * y * z)
        + (x + y + z)
          * (half
            * (L2.square (x - y)
              + L2.square (y - z)
              + L2.square (z - x)))
    addDefect =
      subst
        (λ lower →
          lower
          ≤ three * (x * y * z)
            + (x + y + z)
              * (half
                * (L2.square (x - y)
                  + L2.square (y - z)
                  + L2.square (z - x))))
        (ℚₚ.+-identityʳ (three * (x * y * z)))
        (ℚₚ.+-monoʳ-≤ (three * (x * y * z)) defectNN)

    identity :
      three * (x * y * z)
        + (x + y + z)
          * (half
            * (L2.square (x - y)
              + L2.square (y - z)
              + L2.square (z - x)))
      ≡ cube x + cube y + cube z
    identity = solve (x ∷ y ∷ z ∷ [])
  in
  subst
    (λ upper → three * (x * y * z) ≤ upper)
    identity
    addDefect

productMass : NonnegativePair → ℚ
productMass item =
  square (left item * right item)

leftSixthMass : NonnegativePair → ℚ
leftSixthMass item = sixth (left item)

rightCubeMass : NonnegativePair → ℚ
rightCubeMass item = cube (right item)

pointwiseTripleHolder :
  (i j k : NonnegativePair) →
  three * (productMass i * productMass j * productMass k)
  ≤ leftSixthMass i * rightCubeMass j * rightCubeMass k
    + leftSixthMass j * rightCubeMass k * rightCubeMass i
    + leftSixthMass k * rightCubeMass i * rightCubeMass j
pointwiseTripleHolder i j k =
  let
    x = square (left i) * right j * right k
    y = square (left j) * right k * right i
    z = square (left k) * right i * right j

    squareLeftINN = L2.squareNonnegative (left i)
    squareLeftJNN = L2.squareNonnegative (left j)
    squareLeftKNN = L2.squareNonnegative (left k)

    xNN =
      L2.nonnegativeProductMonotone
        squareLeftINN
        (rightNonnegative j)
        squareLeftINN
        (rightNonnegative j)
        ℚₚ.≤-refl
        ℚₚ.≤-refl

    xFullNN : 0ℚ ≤ x
    xFullNN =
      let
        partialNN : 0ℚ ≤ square (left i) * right j
        partialNN =
          let
            instance
              leftNNI = nonNegative squareLeftINN
              rightNNI = nonNegative (rightNonnegative j)
              productNN =
                ℚₚ.nonNeg*nonNeg⇒nonNeg
                  (square (left i)) (right j)
          in
          ℚₚ.nonNegative⁻¹ (square (left i) * right j)
        instance
          partialNNI = nonNegative partialNN
          rightKNNI = nonNegative (rightNonnegative k)
          resultNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (square (left i) * right j) (right k)
      in
      ℚₚ.nonNegative⁻¹ x

    yFullNN : 0ℚ ≤ y
    yFullNN =
      let
        partialNN : 0ℚ ≤ square (left j) * right k
        partialNN =
          let
            instance
              leftNNI = nonNegative squareLeftJNN
              rightNNI = nonNegative (rightNonnegative k)
              productNN =
                ℚₚ.nonNeg*nonNeg⇒nonNeg
                  (square (left j)) (right k)
          in
          ℚₚ.nonNegative⁻¹ (square (left j) * right k)
        instance
          partialNNI = nonNegative partialNN
          rightINNI = nonNegative (rightNonnegative i)
          resultNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (square (left j) * right k) (right i)
      in
      ℚₚ.nonNegative⁻¹ y

    zFullNN : 0ℚ ≤ z
    zFullNN =
      let
        partialNN : 0ℚ ≤ square (left k) * right i
        partialNN =
          let
            instance
              leftNNI = nonNegative squareLeftKNN
              rightNNI = nonNegative (rightNonnegative i)
              productNN =
                ℚₚ.nonNeg*nonNeg⇒nonNeg
                  (square (left k)) (right i)
          in
          ℚₚ.nonNegative⁻¹ (square (left k) * right i)
        instance
          partialNNI = nonNegative partialNN
          rightJNNI = nonNegative (rightNonnegative j)
          resultNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (square (left k) * right i) (right j)
      in
      ℚₚ.nonNegative⁻¹ z

    amgm = threeVariableAMGM x y z xFullNN yFullNN zFullNN

    leftMeaning :
      three * (x * y * z)
      ≡ three * (productMass i * productMass j * productMass k)
    leftMeaning =
      solve
        ( left i ∷ right i
        ∷ left j ∷ right j
        ∷ left k ∷ right k ∷ [])

    rightMeaning :
      cube x + cube y + cube z
      ≡ leftSixthMass i * rightCubeMass j * rightCubeMass k
        + leftSixthMass j * rightCubeMass k * rightCubeMass i
        + leftSixthMass k * rightCubeMass i * rightCubeMass j
    rightMeaning =
      solve
        ( left i ∷ right i
        ∷ left j ∷ right j
        ∷ left k ∷ right k ∷ [])
  in
  subst
    (λ lower →
      lower
      ≤ leftSixthMass i * rightCubeMass j * rightCubeMass k
        + leftSixthMass j * rightCubeMass k * rightCubeMass i
        + leftSixthMass k * rightCubeMass i * rightCubeMass j)
    leftMeaning
    (subst
      (λ upper → three * (x * y * z) ≤ upper)
      rightMeaning
      amgm)

finiteSixThreeHolderRadicalFree :
  (items : List NonnegativePair) →
  cube (sumBy productMass items)
  ≤ sumBy leftSixthMass items
    * (sumBy rightCubeMass items * sumBy rightCubeMass items)
finiteSixThreeHolderRadicalFree items =
  let
    lower : NonnegativePair → NonnegativePair → NonnegativePair → ℚ
    lower i j k =
      three * (productMass i * productMass j * productMass k)

    firstRight : NonnegativePair → NonnegativePair → NonnegativePair → ℚ
    firstRight i j k =
      leftSixthMass i * rightCubeMass j * rightCubeMass k

    secondRight : NonnegativePair → NonnegativePair → NonnegativePair → ℚ
    secondRight i j k =
      leftSixthMass j * rightCubeMass k * rightCubeMass i

    thirdRight : NonnegativePair → NonnegativePair → NonnegativePair → ℚ
    thirdRight i j k =
      leftSixthMass k * rightCubeMass i * rightCubeMass j

    upper i j k = firstRight i j k + secondRight i j k + thirdRight i j k

    summed =
      sum3Monotone lower upper items items items pointwiseTripleHolder

    lowerFactor :
      sum3 lower items items items
      ≡ three * cube (sumBy productMass items)
    lowerFactor =
      let
        productFactor =
          sum3ProductFactorizes
            (λ item → three * productMass item)
            productMass
            productMass
            items items items

        firstScale = sumByScaleLeft three productMass items
      in
      subst
        (λ firstSum →
          sum3 lower items items items
          ≡ firstSum
            * sumBy productMass items
            * sumBy productMass items)
        firstScale
        productFactor

    upperSplit :
      sum3 upper items items items
      ≡ sum3 firstRight items items items
        + sum3 secondRight items items items
        + sum3 thirdRight items items items
    upperSplit =
      let
        firstSplit =
          sum3Add
            (λ i j k → firstRight i j k + secondRight i j k)
            thirdRight
            items items items

        secondSplit =
          sum3Add firstRight secondRight items items items
      in
      subst
        (λ firstTwo →
          sum3 upper items items items
          ≡ firstTwo + sum3 thirdRight items items items)
        secondSplit
        firstSplit

    firstFactor =
      sum3ProductFactorizes
        leftSixthMass rightCubeMass rightCubeMass
        items items items

    secondFactor =
      sum3ProductFactorizes
        rightCubeMass leftSixthMass rightCubeMass
        items items items

    thirdFactor =
      sum3ProductFactorizes
        rightCubeMass rightCubeMass leftSixthMass
        items items items

    upperFactor :
      sum3 upper items items items
      ≡ three
        * (sumBy leftSixthMass items
          * (sumBy rightCubeMass items * sumBy rightCubeMass items))
    upperFactor =
      subst
        (λ firstTerm →
          sum3 upper items items items
          ≡ firstTerm
            + sum3 secondRight items items items
            + sum3 thirdRight items items items)
        firstFactor
        (subst
          (λ secondTerm →
            sum3 upper items items items
            ≡ sumBy leftSixthMass items
                * sumBy rightCubeMass items
                * sumBy rightCubeMass items
              + secondTerm
              + sum3 thirdRight items items items)
          secondFactor
          (subst
            (λ thirdTerm →
              sum3 upper items items items
              ≡ sumBy leftSixthMass items
                  * sumBy rightCubeMass items
                  * sumBy rightCubeMass items
                + sumBy rightCubeMass items
                  * sumBy leftSixthMass items
                  * sumBy rightCubeMass items
                + thirdTerm)
            thirdFactor
            (subst
              (λ splitValue →
                splitValue
                ≡ three
                  * (sumBy leftSixthMass items
                    * (sumBy rightCubeMass items
                      * sumBy rightCubeMass items)))
              (sym upperSplit)
              (solve
                ( sumBy leftSixthMass items
                ∷ sumBy rightCubeMass items
                ∷ [])))))

    scaledInequality :
      three * cube (sumBy productMass items)
      ≤ three
        * (sumBy leftSixthMass items
          * (sumBy rightCubeMass items * sumBy rightCubeMass items))
    scaledInequality =
      subst
        (λ lowerValue →
          lowerValue
          ≤ three
            * (sumBy leftSixthMass items
              * (sumBy rightCubeMass items
                * sumBy rightCubeMass items)))
        lowerFactor
        (subst
          (λ upperValue → sum3 lower items items items ≤ upperValue)
          upperFactor
          summed)

    cancelScaled :
      oneThird * (three * cube (sumBy productMass items))
      ≤ oneThird
        * (three
          * (sumBy leftSixthMass items
            * (sumBy rightCubeMass items * sumBy rightCubeMass items)))
    cancelScaled =
      let instance oneThirdNN = nonNegative oneThirdNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg oneThird scaledInequality

    leftNormalize :
      oneThird * (three * cube (sumBy productMass items))
      ≡ cube (sumBy productMass items)
    leftNormalize = solve (sumBy productMass items ∷ [])

    rightNormalize :
      oneThird
        * (three
          * (sumBy leftSixthMass items
            * (sumBy rightCubeMass items * sumBy rightCubeMass items)))
      ≡ sumBy leftSixthMass items
        * (sumBy rightCubeMass items * sumBy rightCubeMass items)
    rightNormalize =
      solve
        ( sumBy leftSixthMass items
        ∷ sumBy rightCubeMass items
        ∷ [])
  in
  subst
    (λ lowerValue →
      lowerValue
      ≤ sumBy leftSixthMass items
        * (sumBy rightCubeMass items * sumBy rightCubeMass items))
    leftNormalize
    (subst
      (λ upperValue →
        oneThird * (three * cube (sumBy productMass items))
        ≤ upperValue)
      rightNormalize
      cancelScaled)
