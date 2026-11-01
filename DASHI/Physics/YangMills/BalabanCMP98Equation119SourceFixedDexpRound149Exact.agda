{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SourceFixedDexpRound149Exact where

------------------------------------------------------------------------
-- ROUND149 A1 BIDI: FORCE ROUND147 TO USE THE SOURCE-CORRECT DEXP FAMILY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact as R148
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as LR
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

-- Round147 deliberately exposes four Lie-calculus fields so its path theorem is
-- independent of trivialisation.  On the strongest source route those fields
-- are not caller-selected.  Round148's source audit fixes the literal CMP98
-- roles as
--
--   g(-i ad Y)         -> dexpPlus
--   g^{-1}(-i ad Y_x) -> Jplus
--   R(e^{iY_x})        -> adjointExp.
--
-- The historical Round147 field names contain "Minus"; this adapter is the
-- authoritative interpretation and feeds the source-correct operators into
-- those fields.
withExistingDexpFamily :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C))) →
  R147.LiteralEquation119PathData C n Value group
withExistingDexpFamily pathData convention = record
  { R147.LiteralEquation119PathData.realization =
      R147.realization pathData
  ; R147.LiteralEquation119PathData.bondComponent =
      R147.bondComponent pathData
  ; R147.LiteralEquation119PathData.adjointLink =
      R147.adjointLink pathData
  ; R147.LiteralEquation119PathData.scaleV =
      R147.scaleV pathData
  ; R147.LiteralEquation119PathData.qSource =
      R147.qSource pathData
  ; R147.LiteralEquation119PathData.minusEmbedding =
      R147.minusEmbedding pathData
  ; R147.LiteralEquation119PathData.plusEmbedding =
      R147.plusEmbedding pathData
  ; R147.LiteralEquation119PathData.coarseSegment =
      R147.coarseSegment pathData
  ; R147.LiteralEquation119PathData.coarseSegmentEndsAtPlusCentre =
      R147.coarseSegmentEndsAtPlusCentre pathData
  ; R147.LiteralEquation119PathData.translationCommutation =
      R147.translationCommutation pathData
  ; R147.LiteralEquation119PathData.dexpMinusOuter =
      R148.outerPrintedGMinus convention
  ; R147.LiteralEquation119PathData.inverseDexpMinusAt =
      R148.pointPrintedGInverseMinus convention
  ; R147.LiteralEquation119PathData.adjointExpAt =
      R148.pointAdjointExp convention
  ; R147.LiteralEquation119PathData.adjointExpOuter =
      R148.outerAdjointExp convention
  }

sourceFixedEquation119QPrime :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
sourceFixedEquation119QPrime pathData convention =
  R147.literalEquation119QPrime
    (withExistingDexpFamily pathData convention)

sourceFixedOneStepAveragingDerivative :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
sourceFixedOneStepAveragingDerivative pathData convention =
  R147.asLiteralOneStepAveragingDerivative
    (withExistingDexpFamily pathData convention)

sourceFixedMultiscaleDerivative :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
sourceFixedMultiscaleDerivative pathData convention =
  R126.multiscaleAveragePrime
    (sourceFixedOneStepAveragingDerivative pathData convention)

sourceFixedPointInverseIsPrintedGInverseMinus :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  R147.inverseDexpMinusAt
      (withExistingDexpFamily pathData convention) step point vector
  ≡ R148.pointPrintedGInverseMinus convention step point vector
sourceFixedPointInverseIsPrintedGInverseMinus pathData convention step point vector = refl

sourceFixedPointAdjointIsExistingAdjointExp :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  R147.adjointExpAt
      (withExistingDexpFamily pathData convention) step point vector
  ≡ R148.pointAdjointExp convention step point vector
sourceFixedPointAdjointIsExistingAdjointExp pathData convention step point vector = refl

-- Literal CMP98 identity used immediately after Eq. (119):
--
--   g^{-1}(-z) e^z = g^{-1}(z).
--
-- Because the Eq. (119) inverse field is now source-correctly Jplus, composing
-- it with the actual adjoint field reduces to Jminus exactly by the existing
-- inverse-uniqueness theorem.
sourceFixedPrintedInverseTransport :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  R147.inverseDexpMinusAt
      (withExistingDexpFamily pathData convention) step point
      (R147.adjointExpAt
        (withExistingDexpFamily pathData convention) step point vector)
  ≡ LR.Jminus (R148.atPoint convention step point) vector
sourceFixedPrintedInverseTransport pathData convention step point =
  R148.pointPrintedInverseTransport convention step point

cmp98Equation119SourceFixedDexpCompilerRound149Level : ProofLevel
cmp98Equation119SourceFixedDexpCompilerRound149Level = machineChecked

cmp98Equation119SourceFixedCancellationRound149Level : ProofLevel
cmp98Equation119SourceFixedCancellationRound149Level = machineChecked

-- Strongest remaining A1 source leaves after the sign audit:
--   * identify the actual CMP98 Y/Y_x values with the existing LR family;
--   * identify source coarse bond c with the concrete signed fine-lattice axis
--     segment consumed by Round147 (translation of [x,x(c)] is then derived).
-- The printed g^{-1}(-z)e^z direction itself is no longer a source ambiguity.
literalCMP98Equation119SourceFixedDexpRound149Level : ProofLevel
literalCMP98Equation119SourceFixedDexpRound149Level = conditional
