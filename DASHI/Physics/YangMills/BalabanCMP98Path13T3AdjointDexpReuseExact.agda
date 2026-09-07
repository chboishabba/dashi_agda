{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13T3AdjointDexpReuseExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): REUSE THE T3 ADJOINT/RIGHT-JACOBIAN LANE
--
-- T3 already packages exactly the operator shapes wanted here:
--   adjointExponential, rightJacobian, rightJacobianInverse,
-- with the two inverse laws on its chart ball.
--
-- This adapter forgets T3's additional quantitative remainder/bound fields and
-- exposes only the relevant-Y Eq.(119) semantics.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as T3
import DASHI.Physics.YangMills.BalabanCMP98Path13RelevantYSemanticOperatorsExact as Relevant
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

fromT3AdjointDexpData :
  T3.SU2AdjointDexpData Lie.SU2LieAlgebra Lie.SU2LieAlgebra ℝ →
  Relevant.RelevantYSemanticOperators
fromT3AdjointDexpData data = record
  { Relevant.RelevantYSemanticOperators.dexpMinus =
      T3.rightJacobian data
  ; Relevant.RelevantYSemanticOperators.jMinus =
      T3.rightJacobianInverse data
  ; Relevant.RelevantYSemanticOperators.adjointExp =
      T3.adjointExponential data
  ; Relevant.RelevantYSemanticOperators.RelevantY =
      T3.inChartBall data
  ; Relevant.RelevantYSemanticOperators.dexpMinusAfterJminus =
      λ y inBall vector → T3.rightJacobianInverseRight data y vector inBall
  ; Relevant.RelevantYSemanticOperators.jMinusAfterDexpMinus =
      λ y inBall vector → T3.rightJacobianInverseLeft data y vector inBall
  }

cmp98Path13T3AdjointDexpReuseLevel : ProofLevel
cmp98Path13T3AdjointDexpReuseLevel = machineChecked

-- The T3 record itself and the identification of its chart-ball convention with
-- the selected CMP98 principal-log convention remain separate source inputs.
literalCMP98Path13T3AdjointDexpDataLevel : ProofLevel
literalCMP98Path13T3AdjointDexpDataLevel = conditional
