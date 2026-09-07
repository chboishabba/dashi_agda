{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13T3PrintedOperatorAdapterExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): T3 RIGHT-JACOBIAN -> PRINTED CMP98 OPERATOR PACKAGE
--
-- The existing T3 owner names the standard SO(3)/SU(2) right Jacobian
--
--   J_r(a) = I - (1-cos theta)/theta^2 [a]_x
--                + (theta-sin theta)/theta^3 [a]_x^2,
--
-- and supplies a two-sided inverse on its chart ball.  R148/R153 identify the
-- literal CMP98 g(-i ad Y) role with the PLUS/opposite-trivialisation dexp.
-- This adapter therefore exposes a T3 data set in the corrected printed-role
-- shape: rightJacobian -> dexpPlus, rightJacobianInverse -> Jplus, and
-- adjointExponential -> Ad_exp.
--
-- This is a compiler only.  A physical Path13 use must still identify the T3
-- Parameter/State normalization and chart ball with the selected Path13 chart.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as T3
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedSemanticOperatorsExact as Printed
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

T3Path13DexpData : Set → Set₁
T3Path13DexpData Scalar =
  T3.SU2AdjointDexpData Lie.SU2LieAlgebra Lie.SU2LieAlgebra Scalar

fromT3RightJacobian :
  ∀ {Scalar} → T3Path13DexpData Scalar →
  Printed.PrintedSemanticOperators
fromT3RightJacobian dataSet = record
  { Printed.PrintedSemanticOperators.RelevantY = T3.inChartBall dataSet
  ; Printed.PrintedSemanticOperators.dexpPlus = T3.rightJacobian dataSet
  ; Printed.PrintedSemanticOperators.jPlus = T3.rightJacobianInverse dataSet
  ; Printed.PrintedSemanticOperators.adjointExp = T3.adjointExponential dataSet
  ; Printed.PrintedSemanticOperators.jPlusAfterDexpPlus =
      λ y inBall vector → T3.rightJacobianInverseLeft dataSet y vector inBall
  }

-- The other inverse direction is also inherited from T3, even though the
-- literal Eq. (119) consumer does not need to assume it separately.
t3DexpPlusAfterJplus :
  ∀ {Scalar} (dataSet : T3Path13DexpData Scalar) y →
  T3.inChartBall dataSet y →
  ∀ vector →
  Printed.dexpPlus (fromT3RightJacobian dataSet) y
    (Printed.jPlus (fromT3RightJacobian dataSet) y vector)
  ≡ vector
t3DexpPlusAfterJplus dataSet y inBall vector =
  T3.rightJacobianInverseRight dataSet y vector inBall

cmp98Path13T3PrintedOperatorAdapterLevel : ProofLevel
cmp98Path13T3PrintedOperatorAdapterLevel = machineChecked

-- No concrete T3 data set / selected-Path13 normalization is manufactured.
literalCMP98Path13T3DifferentialInstantiationLevel : ProofLevel
literalCMP98Path13T3DifferentialInstantiationLevel = conditional
