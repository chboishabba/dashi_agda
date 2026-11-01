module DASHI.Physics.Closure.NSTriadKNFiniteInitialCoherentEndpointRound460Exact where

------------------------------------------------------------------------
-- ROUND460 / FINITE POSITIVE INITIAL ENDPOINT WITHOUT CARDINALITY TAX
--
-- The Cauchy completion controls the negative terminal orientation by the
-- diagonal.  The positive initial orientation is different: positive coherent
-- cross terms can accumulate.  The right finite producer is therefore an
-- l1-type amplitude, not another L2 mass estimate.
--
-- This owner isolates the exact finite algebra.  If every cell has a
-- nonnegative amplitude a_i, every pair contribution obeys
--
--   pairFlux(i,j) <= 2 W a_i a_j,
--
-- and W >= 0, then the complete unordered off-diagonal fold satisfies
--
--   offDiagonal <= W (sum_i a_i)^2.
--
-- No fibre cardinality appears.  The remaining physical question is only how
-- the selected initial datum pays sum_i a_i on the literal companion carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

two : ℚ
two = 1ℚ + 1ℚ

record FiniteInitialCoherentEndpoint (Cell : Set) : Set₁ where
  constructor finite-initial-coherent-endpoint
  field
    amplitude : Cell → ℚ
    pairFlux : Cell → Cell → ℚ
    ceiling : ℚ
    ceilingNN : 0ℚ ≤ ceiling
    amplitudeNN : (cell : Cell) → 0ℚ ≤ amplitude cell
    pairFluxBelowAmplitudeProduct :
      (left right : Cell) →
      pairFlux left right
      ≤ two * ceiling * (amplitude left * amplitude right)

open FiniteInitialCoherentEndpoint public

sumAmplitude :
  ∀ {Cell} → FiniteInitialCoherentEndpoint Cell → List Cell → ℚ
sumAmplitude P [] = 0ℚ
sumAmplitude P (cell ∷ rest) = amplitude P cell + sumAmplitude P rest

headPairFlux :
  ∀ {Cell} → FiniteInitialCoherentEndpoint Cell → Cell → List Cell → ℚ
headPairFlux P head [] = 0ℚ
headPairFlux P head (cell ∷ rest) =
  pairFlux P head cell + headPairFlux P head rest

offDiagonalFlux :
  ∀ {Cell} → FiniteInitialCoherentEndpoint Cell → List Cell → ℚ
offDiagonalFlux P [] = 0ℚ
offDiagonalFlux P (head ∷ rest) =
  headPairFlux P head rest + offDiagonalFlux P rest

sumAmplitudeNN :
  ∀ {Cell} (P : FiniteInitialCoherentEndpoint Cell) (cells : List Cell) →
  0ℚ ≤ sumAmplitude P cells
sumAmplitudeNN P [] = ℚP.≤-refl
sumAmplitudeNN P (cell ∷ rest) =
  Rational.addNonnegative
    (amplitudeNN P cell)
    (sumAmplitudeNN P rest)

headPairFluxBelow :
  ∀ {Cell}
    (P : FiniteInitialCoherentEndpoint Cell)
    (head : Cell) (rest : List Cell) →
  headPairFlux P head rest
  ≤ two * ceiling P * (amplitude P head * sumAmplitude P rest)
headPairFluxBelow P head [] =
  subst
    (0ℚ ≤_)
    (solve (ceiling P ∷ amplitude P head ∷ []))
    ℚP.≤-refl
headPairFluxBelow P head (cell ∷ rest) =
  let
    first = pairFluxBelowAmplitudeProduct P head cell
    tail = headPairFluxBelow P head rest
    added = ℚP.+-mono-≤ first tail

    endpoint :
      two * ceiling P * (amplitude P head * amplitude P cell)
        + two * ceiling P * (amplitude P head * sumAmplitude P rest)
      ≡
      two * ceiling P
        * (amplitude P head * sumAmplitude P (cell ∷ rest))
    endpoint = solve
      ( ceiling P ∷ amplitude P head ∷ amplitude P cell
      ∷ sumAmplitude P rest ∷ [])
  in
  subst
    (λ upper → headPairFlux P head (cell ∷ rest) ≤ upper)
    endpoint
    added

ceilingTimesSquareNN :
  ∀ {Cell}
    (P : FiniteInitialCoherentEndpoint Cell)
    (value : ℚ) →
  0ℚ ≤ ceiling P * (value * value)
ceilingTimesSquareNN P value =
  let
    squareNN = Rational.squareNonnegative value
    instance
      ceilingNNI : NonNegative (ceiling P)
      ceilingNNI = nonNegative (ceilingNN P)
      squareNNI : NonNegative (value * value)
      squareNNI = nonNegative squareNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg (ceiling P) (value * value)
  in
  ℚP.nonNegative⁻¹ (ceiling P * (value * value))

offDiagonalBelowAmplitudeSquare :
  ∀ {Cell}
    (P : FiniteInitialCoherentEndpoint Cell)
    (cells : List Cell) →
  offDiagonalFlux P cells
  ≤ ceiling P * (sumAmplitude P cells * sumAmplitude P cells)
offDiagonalBelowAmplitudeSquare P [] =
  subst
    (0ℚ ≤_)
    (solve (ceiling P ∷ []))
    ℚP.≤-refl
offDiagonalBelowAmplitudeSquare P (head ∷ rest) =
  let
    a = amplitude P head
    s = sumAmplitude P rest
    W = ceiling P

    row = headPairFluxBelow P head rest
    tail = offDiagonalBelowAmplitudeSquare P rest
    combined = ℚP.+-mono-≤ row tail

    base = two * W * (a * s) + W * (s * s)
    gap = W * (a * a)

    combinedMeaning :
      two * W * (a * s) + W * (s * s) ≡ base
    combinedMeaning = refl

    gapNN : 0ℚ ≤ gap
    gapNN = ceilingTimesSquareNN P a

    addGapRaw : base + 0ℚ ≤ base + gap
    addGapRaw = ℚP.+-monoʳ-≤ base gapNN

    addGap : base ≤ base + gap
    addGap =
      subst
        (λ lower → lower ≤ base + gap)
        (ℚP.+-identityʳ base)
        addGapRaw

    endpoint :
      base + gap
      ≡ W * ((a + s) * (a + s))
    endpoint = solve (W ∷ a ∷ s ∷ [])

    first : offDiagonalFlux P (head ∷ rest) ≤ base
    first = subst
      (λ upper → offDiagonalFlux P (head ∷ rest) ≤ upper)
      combinedMeaning
      combined

    second : base ≤ W * ((a + s) * (a + s))
    second = subst (base ≤_) endpoint addGap
  in
  ℚP.≤-trans first second

round460FiniteInitialCoherentEndpointCompilerClosed : Bool
round460FiniteInitialCoherentEndpointCompilerClosed = true

round460IntroducesCardinalityTax : Bool
round460IntroducesCardinalityTax = false

round460RequiresInitialAmplitudeSumProducer : Bool
round460RequiresInitialAmplitudeSumProducer = true

round460ContainsPostulate : Bool
round460ContainsPostulate = false

round460PackageAClosed : Bool
round460PackageAClosed = false

round460ClayPromotion : Bool
round460ClayPromotion = false

round460IntroducesCardinalityTaxIsFalse :
  round460IntroducesCardinalityTax ≡ false
round460IntroducesCardinalityTaxIsFalse = refl

round460ContainsPostulateIsFalse :
  round460ContainsPostulate ≡ false
round460ContainsPostulateIsFalse = refl
