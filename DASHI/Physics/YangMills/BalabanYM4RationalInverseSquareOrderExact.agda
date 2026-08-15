module DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact where

------------------------------------------------------------------------
-- PRIMARY / CONSTRUCTIVE ARITHMETIC SOURCES
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Agda standard library, Data.Rational.Base / Data.Rational.Properties.
-- No independent DOI is assigned to the library modules.
--
-- DASHI CONTRIBUTION
--
-- Close the elementary order leaf left by the source-normalized YM coupling
-- history.  For positive rationals g,gamma, write
--
--       u g^2 = 1,        u_* gamma^2 = 1.
--
-- Then
--
--       u_* <= u   ==>   g <= gamma.
--
-- The proof does not appeal to a floating reciprocal or square root.  Multiply
-- the inverse-coupling inequality by the positive product gamma^2 g^2 to get
-- g^2 <= gamma^2, then reflect square order on the positive cone.  This is the
-- literal finite-rational dictionary required after the terminal-threshold
-- propagation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

square : ℚ → ℚ
square value = value * value

positiveImpliesNonnegative : ∀ value → Positive value → 0ℚ ≤ value
positiveImpliesNonnegative value positive =
  ℚP.<⇒≤ (ℚP.positive⁻¹ positive)

squareOrderReflectsPositive :
  ∀ g gamma →
  Positive g → Positive gamma →
  square g ≤ square gamma →
  g ≤ gamma
squareOrderReflectsPositive g gamma gPositive gammaPositive squareBelow
    with ℚP.<-cmp g gamma
... | tri< g<gamma _ _ = ℚP.<⇒≤ g<gamma
... | tri≈ _ g≡gamma _ = ℚP.≤-reflexive g≡gamma
... | tri> _ _ gamma<g =
  let
    instance
      gPos : Positive g
      gPos = gPositive
      gammaPos : Positive gamma
      gammaPos = gammaPositive

    gammaSquareBelowMixed : gamma * gamma < gamma * g
    gammaSquareBelowMixed = ℚP.*-monoʳ-<-pos gamma gamma<g

    mixedBelowGSquare : gamma * g < g * g
    mixedBelowGSquare = ℚP.*-monoˡ-<-pos g gamma<g

    gammaSquareBelowGSquare : square gamma < square g
    gammaSquareBelowGSquare =
      ℚP.<-trans gammaSquareBelowMixed mixedBelowGSquare

    impossible : square gamma < square gamma
    impossible = ℚP.<-≤-trans gammaSquareBelowGSquare squareBelow
  in
  ⊥-elim (ℚP.<-irrefl refl impossible)

record RationalInverseSquareOrderData : Set where
  field
    coupling thresholdCoupling : ℚ
    inverseCoupling inverseThreshold : ℚ

    couplingPositive : Positive coupling
    thresholdCouplingPositive : Positive thresholdCoupling

    inverseCouplingTimesSquare :
      inverseCoupling * square coupling ≡ 1ℚ
    inverseThresholdTimesSquare :
      inverseThreshold * square thresholdCoupling ≡ 1ℚ

open RationalInverseSquareOrderData public

productOfSquares : RationalInverseSquareOrderData → ℚ
productOfSquares dataSet =
  square (thresholdCoupling dataSet) * square (coupling dataSet)

productOfSquaresNonnegative :
  ∀ dataSet → 0ℚ ≤ productOfSquares dataSet
productOfSquaresNonnegative dataSet =
  let
    g = coupling dataSet
    gamma = thresholdCoupling dataSet
    gNN = positiveImpliesNonnegative g (couplingPositive dataSet)
    gammaNN = positiveImpliesNonnegative gamma
      (thresholdCouplingPositive dataSet)

    instance
      gNonnegative : NonNegative g
      gNonnegative = ℚ.nonNegative gNN
      gammaNonnegative : NonNegative gamma
      gammaNonnegative = ℚ.nonNegative gammaNN
      gSquareNonnegative : NonNegative (square g)
      gSquareNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg g g
      gammaSquareNonnegative : NonNegative (square gamma)
      gammaSquareNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg gamma gamma
  in
  ℚP.nonNegative⁻¹ (productOfSquares dataSet)

scaledThresholdMeaning : ∀ dataSet →
  productOfSquares dataSet * inverseThreshold dataSet
  ≡ square (coupling dataSet)
scaledThresholdMeaning dataSet =
  let
    gammaSquare = square (thresholdCoupling dataSet)
    gSquare = square (coupling dataSet)
    threshold = inverseThreshold dataSet
  in
  trans
    (ℚRing.solve-∀ gammaSquare gSquare threshold)
    (trans
      (cong (_* gSquare) (inverseThresholdTimesSquare dataSet))
      (ℚP.*-identityˡ gSquare))

scaledInverseCouplingMeaning : ∀ dataSet →
  productOfSquares dataSet * inverseCoupling dataSet
  ≡ square (thresholdCoupling dataSet)
scaledInverseCouplingMeaning dataSet =
  let
    gammaSquare = square (thresholdCoupling dataSet)
    gSquare = square (coupling dataSet)
    inverse = inverseCoupling dataSet
  in
  trans
    (ℚRing.solve-∀ gammaSquare gSquare inverse)
    (trans
      (cong (gammaSquare *_) (inverseCouplingTimesSquare dataSet))
      (ℚP.*-identityʳ gammaSquare))

inverseSquareOrderGivesSquareOrder :
  ∀ dataSet →
  inverseThreshold dataSet ≤ inverseCoupling dataSet →
  square (coupling dataSet) ≤ square (thresholdCoupling dataSet)
inverseSquareOrderGivesSquareOrder dataSet thresholdBelow =
  let
    product = productOfSquares dataSet
    productNN = productOfSquaresNonnegative dataSet
    instance productNonnegative : NonNegative product
    productNonnegative = ℚ.nonNegative productNN

    scaled :
      product * inverseThreshold dataSet
      ≤ product * inverseCoupling dataSet
    scaled = ℚP.*-monoˡ-≤-nonNeg product thresholdBelow
  in
  subst
    (λ lower → lower ≤ square (thresholdCoupling dataSet))
    (sym (scaledThresholdMeaning dataSet))
    (subst
      (λ upper → product * inverseThreshold dataSet ≤ upper)
      (scaledInverseCouplingMeaning dataSet)
      scaled)

inverseSquareThresholdImpliesSmallCoupling :
  ∀ dataSet →
  inverseThreshold dataSet ≤ inverseCoupling dataSet →
  coupling dataSet ≤ thresholdCoupling dataSet
inverseSquareThresholdImpliesSmallCoupling dataSet thresholdBelow =
  squareOrderReflectsPositive
    (coupling dataSet)
    (thresholdCoupling dataSet)
    (couplingPositive dataSet)
    (thresholdCouplingPositive dataSet)
    (inverseSquareOrderGivesSquareOrder dataSet thresholdBelow)

ym4PositiveRationalSquareOrderReflectionLevel : ProofLevel
ym4PositiveRationalSquareOrderReflectionLevel = machineChecked

ym4RationalInverseSquareOrderLevel : ProofLevel
ym4RationalInverseSquareOrderLevel = machineChecked
