module DASHI.Physics.YangMills.BalabanLiteralNestedHullAssociativityCutExact where

-- Explicit smallest remaining algebraic CUT for the original four-corner
-- rational interval product. Nothing here equates dependent order proofs.
-- The eight rational corner reassociation is proved separately.
-- Only the FOUR hull-extremality comparisons remain as inputs.

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End
import DASHI.Physics.YangMills.BalabanLiteralEightCornerReassociationExact as Eight

record ActualNestedHullExtremality : Set₁ where
  field
    leftLowerEight : ∀ x y z →
      Eval.lower (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
      ≡ Eight.leftCorners Eight.min8 x y z
    rightLowerEight : ∀ x y z →
      Eval.lower (Typed.multiplyInterval x (Typed.multiplyInterval y z))
      ≡ Eight.rightCorners Eight.min8 x y z
    leftUpperEight : ∀ x y z →
      Eval.upper (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
      ≡ Eight.leftCorners Eight.max8 x y z
    rightUpperEight : ∀ x y z →
      Eval.upper (Typed.multiplyInterval x (Typed.multiplyInterval y z))
      ≡ Eight.rightCorners Eight.max8 x y z

open ActualNestedHullExtremality public

typedFourCornerMultiplyEndpointAssociative :
  ActualNestedHullExtremality →
  (x y z : Eval.RationalInterval) →
  End.SameEndpoints
    (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
    (Typed.multiplyInterval x (Typed.multiplyInterval y z))
typedFourCornerMultiplyEndpointAssociative hull x y z =
  End.sameEndpoints
    (trans (leftLowerEight hull x y z)
      (trans (Eight.eightCornerLowerReassociation x y z)
        (sym (rightLowerEight hull x y z))))
    (trans (leftUpperEight hull x y z)
      (trans (Eight.eightCornerUpperReassociation x y z)
        (sym (rightUpperEight hull x y z))))

-- The theorem is ENDPOINT-OBSERVATIONAL. It never asserts Agda's
-- propositional equality of arbitrary proof-bearing intervals.
-- An inhabitant of ActualNestedHullExtremality is still required.
