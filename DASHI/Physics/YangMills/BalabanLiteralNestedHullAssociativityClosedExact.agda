module DASHI.Physics.YangMills.BalabanLiteralNestedHullAssociativityClosedExact where

-- SOURCE-WRITTEN UNCONDITIONAL theorem about ORIGINAL Typed.multiplyInterval.
-- It proves equality of BOTH rational endpoints; proof fields of the
-- dependent RationalInterval are intentionally not identified.
-- No new axioms, arithmetic abstraction or postulated hull extrema.

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End
import DASHI.Physics.YangMills.BalabanLiteralNestedHullAssociativityCutExact as Cut
import DASHI.Physics.YangMills.BalabanLiteralLeftNestedHullExtremaExact as Left
import DASHI.Physics.YangMills.BalabanLiteralRightNestedHullExtremaExact as Right

actualNestedHullExtremality : Cut.ActualNestedHullExtremality
actualNestedHullExtremality = record
  { Cut.leftLowerEight = Left.leftLowerEight
  ; Cut.rightLowerEight = Right.rightLowerEight
  ; Cut.leftUpperEight = Left.leftUpperEight
  ; Cut.rightUpperEight = Right.rightUpperEight
  }

typedFourCornerMultiplyEndpointAssociative :
  (x y z : Eval.RationalInterval) →
  End.SameEndpoints
    (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
    (Typed.multiplyInterval x (Typed.multiplyInterval y z))
typedFourCornerMultiplyEndpointAssociative =
  Cut.typedFourCornerMultiplyEndpointAssociative actualNestedHullExtremality
