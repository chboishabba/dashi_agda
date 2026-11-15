module DASHI.Physics.YangMills.BalabanLiteralTotalRationalBackendExact where

-- Total computational backend for the ORIGINAL recursive expression evaluator.
-- Explicit semantics outside the physically admitted strictly-positive
-- denominator domain: return [0,0]. That fallback is NOT a sound
-- representation of division at a zero/nonpositive denominator.
--
-- On the positive domain, it agrees propositionally with the ORIGINAL
-- Typed.divideInterval, including its exact order-proof witness.
-- No external numerical data or source integrand is invented.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _<_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End
import DASHI.Physics.YangMills.BalabanLiteralProofIrrelevantIntervalBackendExact as Proofs
import DASHI.Physics.YangMills.BalabanLiteralEndpointEvaluatorCongruenceExact as Cong

-- Explicit total extension of ORIGINAL typed positive-only division.
totalDivide :
  Eval.RationalInterval → Eval.RationalInterval → Eval.RationalInterval
totalDivide numerator denominator with
  ℚP._<?_ 0ℚ (Eval.lower denominator)
... | yes positive =
  Typed.divideInterval numerator denominator positive
... | no _ = Typed.constantInterval 0ℚ

-- On the selected positive-denominator domain, even the ORDER WITNESS
-- and all full record fields agree with the original typed operation.
totalDivideEqualsTypedWhenPositive :
  (numerator denominator : Eval.RationalInterval) →
  (positive : 0ℚ < Eval.lower denominator) →
  totalDivide numerator denominator
    ≡ Typed.divideInterval numerator denominator positive
totalDivideEqualsTypedWhenPositive numerator denominator positive with
  ℚP._<?_ 0ℚ (Eval.lower denominator)
... | yes chosen =
  cong (Typed.divideInterval numerator denominator)
    (ℚP.<-irrelevant chosen positive)
... | no notPositive = ⊥-elim (notPositive positive)

-- Totality ensures the selected division respects full input equality
-- even when its fallback branch is taken; this is NOT general soundness
-- of division for nonpositive denominator intervals.
totalDivideCongruence :
  ∀ {a b c d : Eval.RationalInterval} →
  End.SameEndpoints a b → End.SameEndpoints c d →
  totalDivide a c ≡ totalDivide b d
totalDivideCongruence ab cd =
  cong₂ totalDivide
    (Proofs.originalIntervalExtensionality ab)
    (Proofs.originalIntervalExtensionality cd)

totalDivideEndpointCongruence :
  ∀ {a b c d : Eval.RationalInterval} →
  End.SameEndpoints a b → End.SameEndpoints c d →
  End.SameEndpoints (totalDivide a c) (totalDivide b d)
totalDivideEndpointCongruence ab cd =
  let equal = totalDivideCongruence ab cd in
  End.sameEndpoints (cong Eval.lower equal) (cong Eval.upper equal)

-- Actual selected original rational interval operators.
selectedArithmetic : Eval.RationalIntervalArithmetic
selectedArithmetic = record
  { Eval.zeroInterval = Typed.constantInterval 0ℚ
  ; Eval.oneInterval = Typed.constantInterval 1ℚ
  ; Eval.constantInterval = Typed.constantInterval
  ; Eval.addInterval = Typed.addInterval
  ; Eval.subtractInterval = Typed.subtractInterval
  ; Eval.multiplyInterval = Typed.multiplyInterval
  ; Eval.divideInterval = totalDivide
  ; Eval.negateInterval = Typed.negateInterval
  ; Eval.addIntervalSound = λ left right →
      ∀ {x y} →
      Typed.LiesIn x left → Typed.LiesIn y right →
      Typed.LiesIn (x + y) (Typed.addInterval left right)
  ; Eval.subtractIntervalSound = λ left right →
      ∀ {x y} →
      Typed.LiesIn x left → Typed.LiesIn y right →
      Typed.LiesIn (x - y) (Typed.subtractInterval left right)
  ; Eval.multiplyIntervalSound = λ left right →
      ∀ {x y} →
      Typed.LiesIn x left → Typed.LiesIn y right →
      Typed.LiesIn (x * y) (Typed.multiplyInterval left right)
  ; Eval.divideIntervalSound = λ numerator denominator →
      ∀ {x y}
        (insideN : Typed.LiesIn x numerator)
        (insideD : Typed.LiesIn y denominator)
        (positive : 0ℚ < Eval.lower denominator) →
      let actualPositive =
            ℚP.<-≤-trans positive (Typed.lowerSound insideD)
      in Typed.LiesIn
          (Quotient.dividePositive x y actualPositive)
          (totalDivide numerator denominator)
  ; Eval.negateIntervalSound = λ value →
      ∀ {x} → Typed.LiesIn x value →
      Typed.LiesIn (- x) (Typed.negateInterval value)
  ; Eval.denominatorStrictlyPositive = λ denominator →
      0ℚ < Eval.lower denominator
  ; Eval.divideRequiresPositiveDenominator = λ numerator denominator positive →
      ∀ {x y}
        (insideN : Typed.LiesIn x numerator)
        (insideD : Typed.LiesIn y denominator) →
      let actualPositive =
            ℚP.<-≤-trans positive (Typed.lowerSound insideD)
      in Typed.LiesIn
          (Quotient.dividePositive x y actualPositive)
          (totalDivide numerator denominator)
  }

-- The source declaration's "Sound" fields above are meaningful
-- propositions. The following TERMS actually prove them, avoiding
-- the false inference that declaring a Set constitutes a certificate.
selectedAddSound :
  ∀ left right →
  Eval.addIntervalSound selectedArithmetic left right
selectedAddSound left right = Typed.addIntervalSound

selectedSubtractSound :
  ∀ left right →
  Eval.subtractIntervalSound selectedArithmetic left right
selectedSubtractSound left right = Typed.subtractIntervalSound

selectedMultiplySound :
  ∀ left right →
  Eval.multiplyIntervalSound selectedArithmetic left right
selectedMultiplySound left right = Typed.multiplyIntervalSound

selectedNegateSound :
  ∀ value →
  Eval.negateIntervalSound selectedArithmetic value
selectedNegateSound value = Typed.negateIntervalSound

selectedDivideSound :
  ∀ numerator denominator →
  Eval.divideIntervalSound selectedArithmetic numerator denominator
selectedDivideSound numerator denominator insideN insideD positive =
  let sound = Typed.divideIntervalSound insideN insideD positive
  in substMembership
      (totalDivideEqualsTypedWhenPositive numerator denominator positive)
      sound

substMembership :
  ∀ {x : ℚ} {a b : Eval.RationalInterval} →
  a ≡ b → Typed.LiesIn x b → Typed.LiesIn x a
substMembership refl proof = proof

-- Congruence of every original evaluateExpression operation,
-- including the chosen explicit total extension.
selectedStable : Cong.EndpointStableBackend selectedArithmetic
selectedStable = record
  { Cong.addStable = λ ab cd →
      End.sameEndpoints
        (cong Eval.lower (Proofs.typedAddCongruenceFull ab cd))
        (cong Eval.upper (Proofs.typedAddCongruenceFull ab cd))
  ; Cong.subtractStable = λ ab cd →
      End.sameEndpoints
        (cong Eval.lower (Proofs.typedSubtractCongruenceFull ab cd))
        (cong Eval.upper (Proofs.typedSubtractCongruenceFull ab cd))
  ; Cong.multiplyStable = λ ab cd →
      End.sameEndpoints
        (cong Eval.lower (Proofs.typedMultiplyCongruenceFull ab cd))
        (cong Eval.upper (Proofs.typedMultiplyCongruenceFull ab cd))
  ; Cong.divideStable = totalDivideEndpointCongruence
  ; Cong.negateStable = λ ab →
      End.sameEndpoints
        (cong Eval.lower (Proofs.typedNegateCongruenceFull ab))
        (cong Eval.upper (Proofs.typedNegateCongruenceFull ab))
  }

-- This selected backend can evaluate the ORIGINAL AST, but the
-- physical seven-generator symmetry still needs the ACTUAL source
-- regularIntegrand and box atom covariance.
