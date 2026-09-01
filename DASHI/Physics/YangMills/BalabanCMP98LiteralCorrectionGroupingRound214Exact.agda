{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98LiteralCorrectionGroupingRound214Exact where

------------------------------------------------------------------------
-- ROUND214 BIDI: SPECIALIZE THE GROUPED EQ.(124) COMPILER TO THE REPOSITORY'S
-- ACTUAL REAL-SU(2) `linearizedAverage` IMPLEMENTATION.
--
-- The executable has the definitional shape
--
--   linearizedAverage = blockedMainTerm + linearizedAverageCorrection.
--
-- The blocked main term is already the explicit CMP98-(125) owner. Therefore
-- a source-exact Eq.(124) transcription for this implementation requires only
-- one remaining equality: its combined correction equals the sum of the four
-- printed correction terms. No separate main-term witness is accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4; Axis4)
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanSU2LiteralOperatorInstances as Literal
import DASHI.Physics.YangMills.BalabanSU2NestedRadialBlockPathTerm as Nested
import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator as Radial
import DASHI.Physics.YangMills.BalabanSU2LinearizedAverage as Linear
import DASHI.Physics.YangMills.BalabanSU2CMP98Equation124 as Eq124
import DASHI.Physics.YangMills.BalabanCMP98Equation124GroupedCorrectionRound213Exact as R213

record LiteralEquation124CorrectionAudit
    {M L : Nat} {{_ : NonZero (M * suc L)}}
    (mainWeight correctionWeight : ℝ)
    (rootOp junctionOp : Radial.RadialReducedOperator)
    (Y : Nested.SU2LieField4 (M * suc L))
    (U : Literal.SU2DirectedGaugeField4 (M * suc L))
    (A : Literal.SU2AdjointBondField4 (M * suc L))
    : Set₁ where
  field
    minusBlockFaceCorrection : Cube4 M → Axis4 → Lie.SU2LieAlgebra
    minusBlockBondCorrection : Cube4 M → Axis4 → Lie.SU2LieAlgebra
    signedPlusBlockFaceCorrection : Cube4 M → Axis4 → Lie.SU2LieAlgebra
    coarseBondCorrection : Cube4 M → Axis4 → Lie.SU2LieAlgebra

    correctionGrouping : ∀ coarse axis →
      Linear.linearizedAverageCorrection
        correctionWeight rootOp junctionOp Y U A coarse axis
      ≡
      Lie.lieAdd (minusBlockFaceCorrection coarse axis)
        (Lie.lieAdd (minusBlockBondCorrection coarse axis)
          (Lie.lieAdd (signedPlusBlockFaceCorrection coarse axis)
            (coarseBondCorrection coarse axis)))

open LiteralEquation124CorrectionAudit public

sourceTerms :
  ∀ {M L : Nat} {{nz : NonZero (M * suc L)}}
    {mainWeight correctionWeight : ℝ}
    {rootOp junctionOp : Radial.RadialReducedOperator}
    {Y : Nested.SU2LieField4 (M * suc L)}
    {U : Literal.SU2DirectedGaugeField4 (M * suc L)}
    {A : Literal.SU2AdjointBondField4 (M * suc L)} →
  LiteralEquation124CorrectionAudit
    mainWeight correctionWeight rootOp junctionOp Y U A →
  Cube4 M → Axis4 → Eq124.CMP98Equation124Terms
sourceTerms
    {mainWeight = mainWeight} {U = U} {A = A}
    audit coarse axis =
  Eq124.equation124Terms
    (Literal.su2BlockedLinearAverageMainTerm mainWeight U A coarse axis)
    (minusBlockFaceCorrection audit coarse axis)
    (minusBlockBondCorrection audit coarse axis)
    (signedPlusBlockFaceCorrection audit coarse axis)
    (coarseBondCorrection audit coarse axis)

literalLinearizedAverageIsEquation124 :
  ∀ {M L : Nat} {{nz : NonZero (M * suc L)}}
    {mainWeight correctionWeight : ℝ}
    {rootOp junctionOp : Radial.RadialReducedOperator}
    {Y : Nested.SU2LieField4 (M * suc L)}
    {U : Literal.SU2DirectedGaugeField4 (M * suc L)}
    {A : Literal.SU2AdjointBondField4 (M * suc L)}
    (audit : LiteralEquation124CorrectionAudit
      mainWeight correctionWeight rootOp junctionOp Y U A)
    coarse axis →
  Linear.linearizedAverage
    mainWeight correctionWeight rootOp junctionOp Y U A coarse axis
  ≡ Eq124.cmp98Equation124 (sourceTerms audit coarse axis)
literalLinearizedAverageIsEquation124
    {mainWeight = mainWeight} {correctionWeight = correctionWeight}
    {rootOp = rootOp} {junctionOp = junctionOp}
    {Y = Y} {U = U} {A = A} audit coarse axis =
  trans
    (Linear.linearAverageRegularBackgroundPerturbation
      mainWeight correctionWeight rootOp junctionOp Y U A coarse axis)
    (trans
      (cong₂ Lie.lieAdd refl (correctionGrouping audit coarse axis))
      (sym (R213.cmp98Equation124Grouped (sourceTerms audit coarse axis))))

cmp98LiteralCorrectionGroupingRound214Level : ProofLevel
cmp98LiteralCorrectionGroupingRound214Level = machineChecked

cmp98LiteralEquation124FromGroupedCorrectionRound214Level : ProofLevel
cmp98LiteralEquation124FromGroupedCorrectionRound214Level = machineChecked

-- This is now the sole Eq.(124) source-expression payment for the executable
-- real-SU(2) linearized average: identify the existing combined nested-radial
-- correction with the four printed correction summands.
literalCMP98FourCorrectionGroupingRound214Level : ProofLevel
literalCMP98FourCorrectionGroupingRound214Level = conditional
