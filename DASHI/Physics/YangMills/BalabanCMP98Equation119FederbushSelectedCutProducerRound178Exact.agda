{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact where

------------------------------------------------------------------------
-- ROUND178 A1 BIDI: SELECTED CUT + EXISTING FEDERBUSH FAMILY -> EQ. (119)
--
-- R176 removed the independent principal-recognition theorem.  R177 removes
-- the remaining arbitrary differential/adjoint calculus by deriving it from
-- the older physical Federbush reduced-adjoint convention family.
--
-- This module also instantiates R126/R146 on the repository's literal
-- three-coordinate su(2) carrier.  Thus the vector on which Eq. (119) acts is
-- definitionally the same `SU2LieAlgebra` on which the old Federbush calculus
-- acts; there is no extra vector-space representation isomorphism at this seam.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedExistingCutRound175Exact as R175
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedCutStrongestProducerRound176Exact as R176
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177

su2AdditiveCarrier : R126.AdditiveOperatorCarrier
su2AdditiveCarrier = record
  { R126.AdditiveOperatorCarrier.Vector = Lie.SU2LieAlgebra
  ; R126.AdditiveOperatorCarrier.zeroV = Lie.lieZero
  ; R126.AdditiveOperatorCarrier.addV = Lie.lieAdd
  }

su2SignedCarrier : R146.SignedAdditiveOperatorCarrier
su2SignedCarrier = record
  { R146.SignedAdditiveOperatorCarrier.additive = su2AdditiveCarrier
  ; R146.SignedAdditiveOperatorCarrier.negV = Lie.lieNegate
  }

su2VectorIsLiteralLie : R126.Vector (R146.additive su2SignedCarrier) → Lie.SU2LieAlgebra
su2VectorIsLiteralLie value = value

federbushSelectedCutOneStepDerivative :
  ∀ {n Value group CoarseField FineField}
    (source : R158.CanonicalL13Equation119Source
      su2SignedCarrier n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      source)
    (cutInputs : R175.SelectedExistingCutInputs source weld) →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative su2AdditiveCarrier
federbushSelectedCutOneStepDerivative source weld cutInputs family =
  R176.selectedCutOneStepDerivative
    source weld cutInputs
    (R177.asUniformAdjointDifferentialCalculus family)

federbushSelectedCutMultiscaleDerivative :
  ∀ {n Value group CoarseField FineField}
    (source : R158.CanonicalL13Equation119Source
      su2SignedCarrier n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      source)
    (cutInputs : R175.SelectedExistingCutInputs source weld) →
  R177.ExistingFederbushConventionFamily →
  Nat → R126.Operator su2AdditiveCarrier
federbushSelectedCutMultiscaleDerivative source weld cutInputs family =
  R176.selectedCutMultiscaleDerivative
    source weld cutInputs
    (R177.asUniformAdjointDifferentialCalculus family)

cmp98Equation119LiteralSU2CarrierRound178Level : ProofLevel
cmp98Equation119LiteralSU2CarrierRound178Level = machineChecked

cmp98Equation119FederbushSelectedCutProducerRound178Level : ProofLevel
cmp98Equation119FederbushSelectedCutProducerRound178Level = machineChecked

-- The strongest Eq. (119) boundary no longer takes an arbitrary calculus.
-- The surviving source-facing statement is only that the principal coordinate
-- Y produced from the literal relative holonomy is the Y indexing the already
-- owned Federbush convention family (plus the selected-cut scalar comparison).
literalCMP98PrincipalYIsExistingFederbushYRound178Level : ProofLevel
literalCMP98PrincipalYIsExistingFederbushYRound178Level = conditional
