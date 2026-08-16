module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeHolderConstantOneCompiledExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality on a finite counting-measure space.
-- Repository-original radical-free proof; no DOI is assigned.
--
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- COMPILER PURPOSE
--
-- This is the constant-one finite (L6,L3)->L2 theorem on the same rational
-- carrier as the historical V2 proof, but it deliberately imports only the
-- tiny ordered-rational core.  Profiling showed that the old V2 dependency on
-- NSTriadKNRationalOrderedFiniteL2 pulled in the recursive Gram proof and spent
-- about 263 s in finiteGramStep before V2 itself was reached.  None of that
-- Gram machinery is needed here: the proof uses only positivity, finite sums,
-- the polynomial three-variable AM-GM identity, and ring equalities.
--
-- The upper cyclic endpoint is assembled by explicit congruence/factorization
-- rather than a local rewrite-clause let binding.  This avoids the Agda-2.9
-- NotAValidLetBinding failure seen in the historical V2 file.
--
-- No postulate, analytic authority, or physical NS witness is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Core

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

productMass leftSixthMass rightCubeMass : NonnegativePair → ℚ
productMass pair = square (left pair * right pair)
leftSixthMass pair = sixth (left pair)
rightCubeMass pair = cube (right pair)

sumBy : ∀ {A : Set} → (A → ℚ) → List A → ℚ
sumBy value [] = 0ℚ
sumBy value (item ∷ items) = value item + sumBy value items

sumByCong :
  ∀ {A : Set}
    (first second : A → ℚ)
    (items : List A) →
  ((item : A) → first item ≡ second item) →
  sumBy first items ≡ sumBy second items
sumByCong first second [] pointwise = refl
sumByCong first second (item ∷ items) pointwise
  rewrite pointwise item
        | sumByCong first second items pointwise = refl

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
    (first item ∷ second item
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
  sumBy (λ a → sumBy (value a) second) first

sum3 :
  ∀ {A B C : Set} →
  (A → B → C → ℚ) →
  List A → List B → List C → ℚ
sum3 value first second third =
  sumBy
    (λ a → sumBy (λ b → sumBy (value a b) third) second)
    first

sum2Add :
  ∀ {A B : Set}
    (firstValue secondValue : A → B → ℚ)
    (first : List A)
    (second : List B) →
  sum2 (λ a b → firstValue a b + secondValue a b) first second
  ≡ sum2 firstValue first second + sum2 secondValue first second
sum2Add firstValue secondValue first second =
  trans
    (sumByCong
      (λ a → sumBy (λ b → firstValue a b + secondValue a b) second)
      (λ a → sumBy (firstValue a) second + sumBy (secondValue a) second)
      first
      (λ a → sumByAdd (firstValue a) (secondValue a) second))
    (sumByAdd
      (λ a → sumBy (firstValue a) second)
      (λ a → sumBy (secondValue a) second)
      first)

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
sum3Monotone lower upper first second third pointwise =
  sumByMonotone
    (λ a → sumBy (λ b → sumBy (lower a b) third) second)
    (λ a → sumBy (λ b → sumBy (upper a b) third) second)
    first
    (λ a →
      sumByMonotone
        (λ b → sumBy (lower a b) third)
        (λ b → sumBy (upper a b) third)
        second
        (λ b →
          sumByMonotone
            (lower a b)
            (upper a b)
            third
            (pointwise a b)))

sum3Add :
  ∀ {A B C : Set}
    (firstValue secondValue : A → B → C → ℚ)
    (first : List A)
    (second : List B)
    (third : List C) →
  sum3 (λ a b c → firstValue a b c + secondValue a b c)
    first second third
  ≡ sum3 firstValue first second third
    + sum3 secondValue first second third
sum3Add firstValue secondValue first second third =
  trans
    (sumByCong
      (λ a →
        sum2
          (λ b c → firstValue a b c + secondValue a b c)
          second third)
      (λ a →
        sum2 (firstValue a) second third
        + sum2 (secondValue a) second third)
      first
      (λ a → sum2Add (firstValue a) (secondValue a) second third))
    (sumByAdd
      (λ a → sum2 (firstValue a) second third)
      (λ a → sum2 (secondValue a) second third)
      first)

sum2ScaleLeft :
  ∀ {A B : Set}
    (scale : ℚ)
    (value : A → B → ℚ)
    (first : List A)
    (second : List B) →
  sum2 (λ a b → scale * value a b) first second
  ≡ scale * sum2 value first second
sum2ScaleLeft scale value first second =
  trans
    (sumByCong
      (λ a → sumBy (λ b → scale * value a b) second)
      (λ a → scale * sumBy (value a) second)
      first
      (λ a → sumByScaleLeft scale (value a) second))
    (sumByScaleLeft
      scale
      (λ a → sumBy (value a) second)
      first)

sum3ScaleLeft :
  ∀ {A B C : Set}
    (scale : ℚ)
    (value : A → B → C → ℚ)
    (first : List A)
    (second : List B)
    (third : List C) →
  sum3 (λ a b c → scale * value a b c) first second third
  ≡ scale * sum3 value first second third
sum3ScaleLeft scale value first second third =
  trans
    (sumByCong
      (λ a →
        sum2 (λ b c → scale * value a b c) second third)
      (λ a → scale * sum2 (value a) second third)
      first
      (λ a → sum2ScaleLeft scale (value a) second third))
    (sumByScaleLeft
      scale
      (λ a → sum2 (value a) second third)
      first)

sum2ProductFactorizes :
  ∀ {A B : Set}
    (firstValue : A → ℚ)
    (secondValue : B → ℚ)
    (first : List A)
    (second : List B) →
  sum2 (λ a b → firstValue a * secondValue b) first second
  ≡ sumBy firstValue first * sumBy secondValue second
sum2ProductFactorizes firstValue secondValue [] second = solve []
sum2ProductFactorizes firstValue secondValue (a ∷ first) second
  rewrite sumByScaleLeft (firstValue a) secondValue second
        | sum2ProductFactorizes firstValue secondValue first second =
  solve
    (firstValue a ∷ sumBy firstValue first
    ∷ sumBy secondValue second ∷ [])

sum3ProductFactorizes :
  ∀ {A B C : Set}
    (firstValue : A → ℚ)
    (secondValue : B → ℚ)
    (thirdValue : C → ℚ)
    (first : List A)
    (second : List B)
    (third : List C) →
  sum3
    (λ a b c → firstValue a * secondValue b * thirdValue c)
    first second third
  ≡ sumBy firstValue first
    * sumBy secondValue second
    * sumBy thirdValue third
sum3ProductFactorizes
  firstValue secondValue thirdValue first second third =
  let
    innerValue = λ b c → secondValue b * thirdValue c
    innerSum = sum2 innerValue second third

    reassociate =
      sum3Cong
        (λ a b c → firstValue a * secondValue b * thirdValue c)
        (λ a b c → firstValue a * (secondValue b * thirdValue c))
        first second third
        (λ a b c → solve
          (firstValue a ∷ secondValue b ∷ thirdValue c ∷ []))

    factorEachFirst =
      sumByCong
        (λ a →
          sum2
            (λ b c → firstValue a * innerValue b c)
            second third)
        (λ a → firstValue a * innerSum)
        first
        (λ a → sum2ScaleLeft (firstValue a) innerValue second third)

    factorOuter = sumByScaleRight firstValue first innerSum

    factorInner =
      sum2ProductFactorizes secondValue thirdValue second third

    endpoint :
      sumBy firstValue first
        * (sumBy secondValue second * sumBy thirdValue third)
      ≡ sumBy firstValue first
        * sumBy secondValue second
        * sumBy thirdValue third
    endpoint = solve
      (sumBy firstValue first
      ∷ sumBy secondValue second
      ∷ sumBy thirdValue third ∷ [])
  in
  trans reassociate
    (trans factorEachFirst
      (trans factorOuter
        (trans
          (cong (sumBy firstValue first *_) factorInner)
          endpoint)))

cubeNonnegative :
  (value : ℚ) → 0ℚ ≤ value → 0ℚ ≤ cube value
cubeNonnegative value valueNN =
  let
    instance
      valueNNI = nonNegative valueNN
      squareNN = ℚₚ.nonNeg*nonNeg⇒nonNeg value value
      resultNN = ℚₚ.nonNeg*nonNeg⇒nonNeg (value * value) value
  in
  ℚₚ.nonNegative⁻¹ (cube value)

pairProductNonnegative :
  (leftValue rightValue : ℚ) →
  0ℚ ≤ leftValue → 0ℚ ≤ rightValue →
  0ℚ ≤ leftValue * rightValue
pairProductNonnegative leftValue rightValue leftNN rightNN =
  let
    instance
      leftNNI = nonNegative leftNN
      rightNNI = nonNegative rightNN
      resultNN = ℚₚ.nonNeg*nonNeg⇒nonNeg leftValue rightValue
  in
  ℚₚ.nonNegative⁻¹ (leftValue * rightValue)

threeVariableAMGM :
  (x y z : ℚ) →
  0ℚ ≤ x → 0ℚ ≤ y → 0ℚ ≤ z →
  three * (x * y * z) ≤ cube x + cube y + cube z
threeVariableAMGM x y z xNN yNN zNN =
  let
    sumNN = Core.addNonnegative (Core.addNonnegative xNN yNN) zNN
    squareSumNN =
      Core.addNonnegative
        (Core.addNonnegative
          (Core.squareNonnegative (x - y))
          (Core.squareNonnegative (y - z)))
        (Core.squareNonnegative (z - x))

    halfSquaresNN =
      pairProductNonnegative
        half
        (square (x - y) + square (y - z) + square (z - x))
        halfNonnegative
        squareSumNN

    defectNN =
      pairProductNonnegative
        (x + y + z)
        (half * (square (x - y) + square (y - z) + square (z - x)))
        sumNN
        halfSquaresNN

    addDefect :
      three * (x * y * z)
      ≤ three * (x * y * z)
        + (x + y + z)
          * (half * (square (x - y) + square (y - z) + square (z - x)))
    addDefect =
      subst
        (λ lower →
          lower
          ≤ three * (x * y * z)
            + (x + y + z)
              * (half * (square (x - y) + square (y - z) + square (z - x))))
        (ℚₚ.+-identityʳ (three * (x * y * z)))
        (ℚₚ.+-monoʳ-≤ (three * (x * y * z)) defectNN)

    identity :
      three * (x * y * z)
        + (x + y + z)
          * (half * (square (x - y) + square (y - z) + square (z - x)))
      ≡ cube x + cube y + cube z
    identity = solve (x ∷ y ∷ z ∷ [])
  in
  subst (λ upper → three * (x * y * z) ≤ upper) identity addDefect

tripleTarget :
  NonnegativePair → NonnegativePair → NonnegativePair → ℚ
tripleTarget i j k =
  productMass i * productMass j * productMass k

xTerm yTerm zTerm :
  NonnegativePair → NonnegativePair → NonnegativePair → ℚ
xTerm i j k = leftSixthMass i * rightCubeMass j * rightCubeMass k
yTerm i j k = rightCubeMass i * leftSixthMass j * rightCubeMass k
zTerm i j k = rightCubeMass i * rightCubeMass j * leftSixthMass k

tripleAMGM :
  (i j k : NonnegativePair) →
  three * tripleTarget i j k
  ≤ xTerm i j k + yTerm i j k + zTerm i j k
tripleAMGM i j k =
  let
    x = square (left i) * right j * right k
    y = square (left j) * right k * right i
    z = square (left k) * right i * right j

    xNN =
      pairProductNonnegative
        (square (left i) * right j)
        (right k)
        (pairProductNonnegative
          (square (left i)) (right j)
          (Core.squareNonnegative (left i))
          (rightNonnegative j))
        (rightNonnegative k)
    yNN =
      pairProductNonnegative
        (square (left j) * right k)
        (right i)
        (pairProductNonnegative
          (square (left j)) (right k)
          (Core.squareNonnegative (left j))
          (rightNonnegative k))
        (rightNonnegative i)
    zNN =
      pairProductNonnegative
        (square (left k) * right i)
        (right j)
        (pairProductNonnegative
          (square (left k)) (right i)
          (Core.squareNonnegative (left k))
          (rightNonnegative i))
        (rightNonnegative j)

    base = threeVariableAMGM x y z xNN yNN zNN

    leftMeaning :
      three * (x * y * z) ≡ three * tripleTarget i j k
    leftMeaning = solve
      (left i ∷ left j ∷ left k ∷ right i ∷ right j ∷ right k ∷ [])

    rightMeaning :
      cube x + cube y + cube z
      ≡ xTerm i j k + yTerm i j k + zTerm i j k
    rightMeaning = solve
      (left i ∷ left j ∷ left k ∷ right i ∷ right j ∷ right k ∷ [])
  in
  subst
    (λ lower → lower ≤ xTerm i j k + yTerm i j k + zTerm i j k)
    leftMeaning
    (subst
      (λ upper → three * (x * y * z) ≤ upper)
      rightMeaning
      base)

scaleBound :
  (scale leftValue rightValue : ℚ) →
  0ℚ ≤ scale →
  leftValue ≤ rightValue →
  scale * leftValue ≤ scale * rightValue
scaleBound scale leftValue rightValue scaleNN bound =
  let instance scaleNNI = nonNegative scaleNN
  in ℚₚ.*-monoˡ-≤-nonNeg scale bound

cyclicUpperFactorization :
  (items : List NonnegativePair) →
  sum3
    (λ i j k → xTerm i j k + yTerm i j k + zTerm i j k)
    items items items
  ≡ three
    * (sumBy leftSixthMass items
      * (sumBy rightCubeMass items * sumBy rightCubeMass items))
cyclicUpperFactorization items =
  let
    splitOuter =
      sum3Add
        (λ i j k → xTerm i j k + yTerm i j k)
        zTerm items items items

    splitInner = sum3Add xTerm yTerm items items items

    splitAll =
      trans splitOuter
        (cong
          (λ xy → xy + sum3 zTerm items items items)
          splitInner)

    xFactor =
      sum3ProductFactorizes
        leftSixthMass rightCubeMass rightCubeMass
        items items items
    yFactor =
      sum3ProductFactorizes
        rightCubeMass leftSixthMass rightCubeMass
        items items items
    zFactor =
      sum3ProductFactorizes
        rightCubeMass rightCubeMass leftSixthMass
        items items items

    factorAll =
      cong₂ _+_
        (cong₂ _+_ xFactor yFactor)
        zFactor

    A = sumBy leftSixthMass items
    B = sumBy rightCubeMass items

    endpoint :
      (A * B * B + B * A * B) + B * B * A
      ≡ three * (A * (B * B))
    endpoint = solve (A ∷ B ∷ [])
  in
  trans splitAll (trans factorAll endpoint)

abstract
  finiteSixThreeHolderRadicalFree :
    (items : List NonnegativePair) →
    cube (sumBy productMass items)
    ≤ sumBy leftSixthMass items
      * (sumBy rightCubeMass items * sumBy rightCubeMass items)
  finiteSixThreeHolderRadicalFree items =
    let
      pointwise =
        sum3Monotone
          (λ i j k → three * tripleTarget i j k)
          (λ i j k → xTerm i j k + yTerm i j k + zTerm i j k)
          items items items
          tripleAMGM

      leftEndpoint :
        sum3 (λ i j k → three * tripleTarget i j k)
          items items items
        ≡ three * cube (sumBy productMass items)
      leftEndpoint =
        trans
          (sum3ScaleLeft three tripleTarget items items items)
          (cong (three *_)
            (trans
              (sum3ProductFactorizes
                productMass productMass productMass items items items)
              (solve (sumBy productMass items ∷ []))))

      upperEndpoint = cyclicUpperFactorization items

      threeBound :
        three * cube (sumBy productMass items)
        ≤ three
          * (sumBy leftSixthMass items
            * (sumBy rightCubeMass items * sumBy rightCubeMass items))
      threeBound =
        subst
          (λ lower →
            lower
            ≤ three
              * (sumBy leftSixthMass items
                * (sumBy rightCubeMass items * sumBy rightCubeMass items)))
          leftEndpoint
          (subst
            (λ upper →
              sum3 (λ i j k → three * tripleTarget i j k)
                items items items
              ≤ upper)
            upperEndpoint
            pointwise)

      rescaled =
        scaleBound
          oneThird
          (three * cube (sumBy productMass items))
          (three
            * (sumBy leftSixthMass items
              * (sumBy rightCubeMass items * sumBy rightCubeMass items)))
          oneThirdNonnegative
          threeBound

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
      rightNormalize = solve
        (sumBy leftSixthMass items ∷ sumBy rightCubeMass items ∷ [])
    in
    subst
      (λ lower →
        lower
        ≤ sumBy leftSixthMass items
          * (sumBy rightCubeMass items * sumBy rightCubeMass items))
      leftNormalize
      (subst
        (λ upper →
          oneThird * (three * cube (sumBy productMass items)) ≤ upper)
        rightNormalize
        rescaled)
