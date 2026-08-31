{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SourceFixedDexpRound149Exact where

------------------------------------------------------------------------
-- ROUND149 A1 BIDI: FORCE ROUND147 TO USE THE EXISTING DEXP FAMILY
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
-- independent of trivialisation.  On the strongest source route, however,
-- those fields are not caller-selected.  They are replaced by projections of
-- the already-owned Round148 convention family.
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
  ; R147.LiteralEquation119PathData.coarseWord =
      R147.coarseWord pathData
  ; R147.LiteralEquation119PathData.coarseWordEndsAtPlusCentre =
      R147.coarseWordEndsAtPlusCentre pathData
  ; R147.LiteralEquation119PathData.crossingDirection =
      R147.crossingDirection pathData
  ; R147.LiteralEquation119PathData.plusOffset =
      R147.plusOffset pathData
  ; R147.LiteralEquation119PathData.crossingHitsPlusOffset =
      R147.crossingHitsPlusOffset pathData
  ; R147.LiteralEquation119PathData.dexpMinusOuter =
      R148.outerDexpMinus convention
  ; R147.LiteralEquation119PathData.inverseDexpMinusAt =
      R148.pointInverseDexpMinus convention
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

sourceFixedPointInverseIsExistingJminus :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  R147.inverseDexpMinusAt
      (withExistingDexpFamily pathData convention) step point vector
  ≡ R148.pointInverseDexpMinus convention step point vector
sourceFixedPointInverseIsExistingJminus pathData convention step point vector = refl

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

-- This is the nontrivial cancellation actually used by the source convention.
-- Because Round149 forces the Round147 fields to the Round148 projections, the
-- RHS is literally the inverse-dexp operator consumed by the Eq. (119) term.
sourceFixedOppositeTrivialisationCancellation :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  LR.Jplus (R148.atPoint convention step point)
    (R147.adjointExpAt
      (withExistingDexpFamily pathData convention) step point vector)
  ≡ R147.inverseDexpMinusAt
      (withExistingDexpFamily pathData convention) step point vector
sourceFixedOppositeTrivialisationCancellation pathData convention step point =
  R148.pointOppositeTrivialisationCancels convention step point

cmp98Equation119SourceFixedDexpCompilerRound149Level : ProofLevel
cmp98Equation119SourceFixedDexpCompilerRound149Level = machineChecked

cmp98Equation119SourceFixedCancellationRound149Level : ProofLevel
cmp98Equation119SourceFixedCancellationRound149Level = machineChecked

-- Strongest remaining A1 source leaves after R149:
--   * identify the printed CMP98 Y/Y_x trivialisation with the existing Dexp
--     family used above;
--   * identify the translated one-bond crossing/coarse-word geometry with the
--     printed Eq. (119) crossing convention.
literalCMP98Equation119SourceFixedDexpRound149Level : ProofLevel
literalCMP98Equation119SourceFixedDexpRound149Level = conditional
