module DASHI.Physics.YangMills.BalabanClayT4BishopPositiveReciprocalIntervalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis", Springer 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Marc Daumas, David Lester and César Muñoz, "Verified Real Number
-- Calculations: A Library for Interval Arithmetic", IEEE Trans. Computers 58
-- (2009), 226--237. DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- If a Bishop denominator d is enclosed by rational 0 < dL <= d <= dU,
-- construct d^{-1} from Murray's positive inverse and prove the exact reversed
-- rational enclosure
--
--      1/dU <= d^{-1} <= 1/dL.
--
-- The proof uses cross multiplication and positivity of d^{-1}; it does NOT
-- assume an abstract inverse-antitone theorem.  This is the semantic division
-- primitive needed by the physical one-loop interval evaluator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; toℚᵘ)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Real as Bishop
import RealProperties as BishopP
import Inverse as BishopInverse

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Product
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PositiveBishopInterval
    (value : Bishop.ℝ) (box : Eval.RationalInterval) : Set where
  constructor positiveBishopInterval
  field
    enclosure : Product.BishopLiesIn value box
    lowerPositive : 0ℚ < Eval.lower box
open PositiveBishopInterval public

upperPositive : ∀ {value box} → PositiveBishopInterval value box →
  0ℚ < Eval.upper box
upperPositive {box = box} positive =
  ℚP.<-≤-trans (lowerPositive positive) (Eval.ordered box)

valuePositive : ∀ {value box} → PositiveBishopInterval value box →
  Bishop.0ℝ Bishop.< value
valuePositive {value} {box} positive =
  BishopP.<-≤-trans
    (Product.embedStrictOrder (lowerPositive positive))
    (Product.lowerSound (enclosure positive))

valueNonzero : ∀ {value box} (positive : PositiveBishopInterval value box) →
  value Bishop.≄ Bishop.0ℝ
valueNonzero positive = inj₂ (valuePositive positive)

valueInverse : ∀ {value box} → PositiveBishopInterval value box → Bishop.ℝ
valueInverse {value} positive = BishopInverse._⁻¹ value (valueNonzero positive)

valueInverseNonnegative : ∀ {value box} (positive : PositiveBishopInterval value box) →
  Bishop.NonNegative (valueInverse positive)
valueInverseNonnegative positive =
  BishopP.pos⇒nonNeg
    (BishopInverse.posx⇒posx⁻¹
      (valueNonzero positive)
      (BishopP.0<x⇒posx (valuePositive positive)))

reciprocalLower : ∀ {value box} (positive : PositiveBishopInterval value box) → ℚ
reciprocalLower {box = box} positive =
  Quotient.positiveReciprocal (Eval.upper box) (upperPositive positive)

reciprocalUpper : ∀ {value box} (positive : PositiveBishopInterval value box) → ℚ
reciprocalUpper {box = box} positive =
  Quotient.positiveReciprocal (Eval.lower box) (lowerPositive positive)

reciprocalEndpointOrder : ∀ {value box} (positive : PositiveBishopInterval value box) →
  reciprocalLower positive ≤ reciprocalUpper positive
reciprocalEndpointOrder {box = box} positive =
  Quotient.reciprocalAntitonePositive
    (Eval.lower box) (Eval.upper box)
    (lowerPositive positive) (upperPositive positive)
    (Eval.ordered box)

reciprocalInterval : ∀ {value box} →
  PositiveBishopInterval value box → Eval.RationalInterval
reciprocalInterval positive =
  Eval.rationalInterval
    (reciprocalLower positive)
    (reciprocalUpper positive)
    (reciprocalEndpointOrder positive)

embedEndpointProductIsOne :
  ∀ denominator (denominatorPositive : 0ℚ < denominator) →
  ( Product.embed
      (Quotient.positiveReciprocal denominator denominatorPositive)
    Bishop.* Product.embed denominator )
  Bishop.≃ Bishop.1ℝ
embedEndpointProductIsOne denominator denominatorPositive =
  let
    reciprocal = Quotient.positiveReciprocal denominator denominatorPositive
    rationalProduct : reciprocal * denominator ≡ 1ℚ
    rationalProduct =
      trans
        (ℚP.*-comm reciprocal denominator)
        (Quotient.positiveReciprocalRightInverse
          denominator denominatorPositive)
  in
  BishopP.≃-trans
    (BishopP.≃-symm (Product.embedMul reciprocal denominator))
    (BishopP.≃-trans
      (BishopP.⋆-cong
        (cong toℚᵘ rationalProduct))
      Product.embedOne)

reciprocalLowerSound : ∀ {value box}
  (positive : PositiveBishopInterval value box) →
  Product.embed (reciprocalLower positive)
  Bishop.≤ valueInverse positive
reciprocalLowerSound {value} {box} positive =
  let
    q = Product.embed (reciprocalLower positive)
    dUpper = Product.embed (Eval.upper box)
    inverse = valueInverse positive
    qNonnegative =
      BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx
          (Product.embedStrictOrder
            (Quotient.positiveReciprocalPositive
              (Eval.upper box) (upperPositive positive))))

    multiplied :
      (q Bishop.* value) Bishop.≤ (q Bishop.* dUpper)
    multiplied =
      BishopP.*-monoˡ-≤-nonNeg
        (Product.upperSound (enclosure positive)) qNonnegative

    belowOne : (q Bishop.* value) Bishop.≤ Bishop.1ℝ
    belowOne =
      BishopP.≤-respʳ-≃
        (embedEndpointProductIsOne
          (Eval.upper box) (upperPositive positive))
        multiplied

    scaled :
      ((q Bishop.* value) Bishop.* inverse)
      Bishop.≤ (Bishop.1ℝ Bishop.* inverse)
    scaled =
      BishopP.*-monoʳ-≤-nonNeg belowOne
        (valueInverseNonnegative positive)

    leftCancel : ((q Bishop.* value) Bishop.* inverse) Bishop.≃ q
    leftCancel =
      BishopP.≃-trans
        (BishopP.*-assoc q value inverse)
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (BishopInverse.*-inverseʳ value (valueNonzero positive)))
          (BishopP.*-identityʳ q))

    rightIdentity : (Bishop.1ℝ Bishop.* inverse) Bishop.≃ inverse
    rightIdentity = BishopP.*-identityˡ inverse
  in
  BishopP.≤-respˡ-≃ leftCancel
    (BishopP.≤-respʳ-≃ rightIdentity scaled)

reciprocalUpperSound : ∀ {value box}
  (positive : PositiveBishopInterval value box) →
  valueInverse positive
  Bishop.≤ Product.embed (reciprocalUpper positive)
reciprocalUpperSound {value} {box} positive =
  let
    q = Product.embed (reciprocalUpper positive)
    dLower = Product.embed (Eval.lower box)
    inverse = valueInverse positive
    qNonnegative =
      BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx
          (Product.embedStrictOrder
            (Quotient.positiveReciprocalPositive
              (Eval.lower box) (lowerPositive positive))))

    multiplied :
      (q Bishop.* dLower) Bishop.≤ (q Bishop.* value)
    multiplied =
      BishopP.*-monoˡ-≤-nonNeg
        (Product.lowerSound (enclosure positive)) qNonnegative

    oneBelow : Bishop.1ℝ Bishop.≤ (q Bishop.* value)
    oneBelow =
      BishopP.≤-respˡ-≃
        (embedEndpointProductIsOne
          (Eval.lower box) (lowerPositive positive))
        multiplied

    scaled :
      (Bishop.1ℝ Bishop.* inverse)
      Bishop.≤ ((q Bishop.* value) Bishop.* inverse)
    scaled =
      BishopP.*-monoʳ-≤-nonNeg oneBelow
        (valueInverseNonnegative positive)

    leftIdentity : (Bishop.1ℝ Bishop.* inverse) Bishop.≃ inverse
    leftIdentity = BishopP.*-identityˡ inverse

    rightCancel : ((q Bishop.* value) Bishop.* inverse) Bishop.≃ q
    rightCancel =
      BishopP.≃-trans
        (BishopP.*-assoc q value inverse)
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (BishopInverse.*-inverseʳ value (valueNonzero positive)))
          (BishopP.*-identityʳ q))
  in
  BishopP.≤-respˡ-≃ leftIdentity
    (BishopP.≤-respʳ-≃ rightCancel scaled)

reciprocalIntervalSound : ∀ {value box}
  (positive : PositiveBishopInterval value box) →
  Product.BishopLiesIn
    (valueInverse positive)
    (reciprocalInterval positive)
reciprocalIntervalSound positive =
  Product.bishopLiesIn
    (reciprocalLowerSound positive)
    (reciprocalUpperSound positive)

bishopPositiveReciprocalIntervalLevel : ProofLevel
bishopPositiveReciprocalIntervalLevel = machineChecked

bishopPositiveDivisionCrossMultiplicationLevel : ProofLevel
bishopPositiveDivisionCrossMultiplicationLevel = machineChecked
