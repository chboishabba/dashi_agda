module DASHI.Physics.YangMills.BalabanLiteralProofIrrelevantIntervalBackendExact where

-- Critical repair: the rational ordering fields are PROOF-IRRELEVANT
-- in Data.Rational.Properties. Therefore same rational endpoints DO
-- determine the full original interval record, including its ordered
-- witness, propositionally. Likewise strict positivity witnesses
-- for a fixed rational denominator are unique.
--
-- No axioms, postulates, or invented interval semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (0ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End
import DASHI.Physics.YangMills.BalabanLiteralFourCornerCommutativityExact as Four
import DASHI.Physics.YangMills.BalabanLiteralNestedHullAssociativityClosedExact as Closed

-- This is a CONCRETE theorem about the source's proof-carrying
-- RationalInterval constructor and the standard rational order proof.
originalIntervalExtensionality :
  ∀ {a b : Eval.RationalInterval} →
  End.SameEndpoints a b → a ≡ b
originalIntervalExtensionality
  {a = Eval.interval l u leftOrder}
  {b = Eval.interval .l .u rightOrder}
  (End.sameEndpoints refl refl) =
  cong (Eval.interval l u) (ℚP.≤-irrelevant leftOrder rightOrder)

-- Formerly endpoint-only laws can now be promoted to FULL record
-- equality, without a new quotient carrier or an extra assumption.

typedAddCommutativeFull : ∀ x y →
  Typed.addInterval x y ≡ Typed.addInterval y x
typedAddCommutativeFull x y =
  originalIntervalExtensionality (End.typedAddCommutative x y)

typedAddAssociativeFull : ∀ x y z →
  Typed.addInterval (Typed.addInterval x y) z
  ≡ Typed.addInterval x (Typed.addInterval y z)
typedAddAssociativeFull x y z =
  originalIntervalExtensionality (End.typedAddAssociative x y z)

typedMultiplyCommutativeFull : ∀ x y →
  Typed.multiplyInterval x y ≡ Typed.multiplyInterval y x
typedMultiplyCommutativeFull x y =
  originalIntervalExtensionality
    (Four.typedFourCornerMultiplyEndpointCommutative x y)

typedMultiplyAssociativeFull : ∀ x y z →
  Typed.multiplyInterval (Typed.multiplyInterval x y) z
  ≡ Typed.multiplyInterval x (Typed.multiplyInterval y z)
typedMultiplyAssociativeFull x y z =
  originalIntervalExtensionality
    (Closed.typedFourCornerMultiplyEndpointAssociative x y z)

typedAddCongruenceFull :
  ∀ {a b c d : Eval.RationalInterval} →
  End.SameEndpoints a b → End.SameEndpoints c d →
  Typed.addInterval a c ≡ Typed.addInterval b d
typedAddCongruenceFull ab cd =
  cong₂ Typed.addInterval
    (originalIntervalExtensionality ab)
    (originalIntervalExtensionality cd)

typedMultiplyCongruenceFull :
  ∀ {a b c d : Eval.RationalInterval} →
  End.SameEndpoints a b → End.SameEndpoints c d →
  Typed.multiplyInterval a c ≡ Typed.multiplyInterval b d
typedMultiplyCongruenceFull ab cd =
  cong₂ Typed.multiplyInterval
    (originalIntervalExtensionality ab)
    (originalIntervalExtensionality cd)

typedSubtractCongruenceFull :
  ∀ {a b c d : Eval.RationalInterval} →
  End.SameEndpoints a b → End.SameEndpoints c d →
  Typed.subtractInterval a c ≡ Typed.subtractInterval b d
typedSubtractCongruenceFull ab cd =
  cong₂ Typed.subtractInterval
    (originalIntervalExtensionality ab)
    (originalIntervalExtensionality cd)

typedNegateCongruenceFull :
  ∀ {a b : Eval.RationalInterval} →
  End.SameEndpoints a b →
  Typed.negateInterval a ≡ Typed.negateInterval b
typedNegateCongruenceFull ab =
  cong Typed.negateInterval (originalIntervalExtensionality ab)

-- The decisive TWO-SIDED theorem for the ACTUAL selected partial
-- typed quotient: both numerator and denominator can change as
-- entire proof-carrying interval records, and the two positive
-- lower-denominator witnesses may differ. All are canonicalized by
-- source-standard rational proof irrelevance.

typedPositiveDivideCongruenceFull :
  ∀ {a b c d : Eval.RationalInterval} →
  End.SameEndpoints a b →
  End.SameEndpoints c d →
  (p : 0ℚ < Eval.lower c) →
  (q : 0ℚ < Eval.lower d) →
  Typed.divideInterval a c p ≡ Typed.divideInterval b d q
typedPositiveDivideCongruenceFull
  {a} {b} {c} {d} ab cd p q
  with originalIntervalExtensionality ab
     | originalIntervalExtensionality cd
... | refl | refl =
  cong (Typed.divideInterval a c) (ℚP.<-irrelevant p q)

typedPositiveDivideCongruenceEndpoints :
  ∀ {a b c d : Eval.RationalInterval} →
  End.SameEndpoints a b →
  End.SameEndpoints c d →
  (p : 0ℚ < Eval.lower c) →
  (q : 0ℚ < Eval.lower d) →
  End.SameEndpoints
    (Typed.divideInterval a c p)
    (Typed.divideInterval b d q)
typedPositiveDivideCongruenceEndpoints ab cd p q =
  let eq = typedPositiveDivideCongruenceFull ab cd p q in
  End.sameEndpoints (cong Eval.lower eq) (cong Eval.upper eq)

-- IMPORTANT DOMAIN: Typed.divideInterval is positive-denominator
-- INDEXED. This theorem does not identify it with the arbitrary total
-- divideInterval field of Eval.RationalIntervalArithmetic.
