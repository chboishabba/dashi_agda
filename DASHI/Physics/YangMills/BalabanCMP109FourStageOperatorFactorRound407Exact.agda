{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact where

------------------------------------------------------------------------
-- ROUND407 / CMP109 FOUR-STAGE OPERATOR-FACTOR ORDINARY BOUNDS
--
-- R406 has already reduced a differentiated selected term to an ordered
-- noncommutative operator-product difference.  The ordinary factor bounds in
-- that product are not new physical estimates: the existing Gate-4 CMP109
-- derivative-entry pipeline already carries the literal four stages
--
--   path derivative -> transport -> dexp^-1/log -> outer dexp
--
-- together with a norm bound for every stage.
--
-- This owner makes that finite factor carrier explicit and proves that one
-- common stage-majorant family bounds BOTH neighboring entries whenever the
-- two pipeline bound coordinates are identified with that common family.
-- Thus the ordinary half of R406/P0b1 is compiler-owned at source level.  The
-- remaining live source leaf is the marked DOMAIN-DIFFERENCE estimate for the
-- changed stage (CMP99 Theorem 3.14/(3.154), propagated through the literal
-- CMP109 entry), plus the same-object identification with the selected
-- R318/CMP116 term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Gate4

------------------------------------------------------------------------
-- Literal ordered four-stage carrier.
------------------------------------------------------------------------

data CMP109DerivativeStage : Set where
  outerDexpStage : CMP109DerivativeStage
  logarithmDexpInverseStage : CMP109DerivativeStage
  transportDerivativeStage : CMP109DerivativeStage
  pathDerivativeStage : CMP109DerivativeStage

cmp109DerivativeStages : List CMP109DerivativeStage
cmp109DerivativeStages =
  outerDexpStage ∷
  logarithmDexpInverseStage ∷
  transportDerivativeStage ∷
  pathDerivativeStage ∷ []

stageOperator :
  ∀ {Operator Bound} →
  Gate4.CMP109DerivativeEntryPipeline Operator Bound →
  CMP109DerivativeStage → Operator
stageOperator pipeline outerDexpStage = Gate4.outerDexp pipeline
stageOperator pipeline logarithmDexpInverseStage =
  Gate4.logarithmDexpInverse pipeline
stageOperator pipeline transportDerivativeStage =
  Gate4.transportDerivative pipeline
stageOperator pipeline pathDerivativeStage = Gate4.pathDerivative pipeline

stageBound :
  ∀ {Operator Bound} →
  Gate4.CMP109DerivativeEntryPipeline Operator Bound →
  CMP109DerivativeStage → Bound
stageBound pipeline outerDexpStage = Gate4.outerBound pipeline
stageBound pipeline logarithmDexpInverseStage = Gate4.logarithmBound pipeline
stageBound pipeline transportDerivativeStage = Gate4.transportBound pipeline
stageBound pipeline pathDerivativeStage = Gate4.pathBound pipeline

stageNormBound :
  ∀ {Operator Bound}
    (pipeline : Gate4.CMP109DerivativeEntryPipeline Operator Bound) →
  ∀ stage →
  Gate4.LessEqual (Gate4.algebra pipeline)
    (Gate4.operatorNorm (Gate4.algebra pipeline)
      (stageOperator pipeline stage))
    (stageBound pipeline stage)
stageNormBound pipeline outerDexpStage = Gate4.outerEstimate pipeline
stageNormBound pipeline logarithmDexpInverseStage =
  Gate4.logarithmEstimate pipeline
stageNormBound pipeline transportDerivativeStage =
  Gate4.transportEstimate pipeline
stageNormBound pipeline pathDerivativeStage = Gate4.pathEstimate pipeline

------------------------------------------------------------------------
-- Neighboring selected entries share one ordinary majorant family.
------------------------------------------------------------------------

record CMP109FourStageOrdinaryPair (Operator Bound : Set) : Set₁ where
  field
    before after : Gate4.CMP109DerivativeEntryPipeline Operator Bound

    -- R406's noncommutative telescope uses one operator algebra for both
    -- neighboring products.  This equality is a same-carrier condition, not
    -- an analytic estimate.
    sameOperatorNormAlgebra : Gate4.algebra before ≡ Gate4.algebra after

    ordinaryStageMajorant : CMP109DerivativeStage → Bound

    beforeStageBoundIsCommon : ∀ stage →
      stageBound before stage ≡ ordinaryStageMajorant stage

    afterStageBoundIsCommon : ∀ stage →
      stageBound after stage ≡ ordinaryStageMajorant stage

open CMP109FourStageOrdinaryPair public

beforeStageBelowCommonMajorant :
  ∀ {Operator Bound}
    (pair : CMP109FourStageOrdinaryPair Operator Bound) →
  ∀ stage →
  Gate4.LessEqual (Gate4.algebra (before pair))
    (Gate4.operatorNorm (Gate4.algebra (before pair))
      (stageOperator (before pair) stage))
    (ordinaryStageMajorant pair stage)
beforeStageBelowCommonMajorant pair stage =
  subst
    (λ upper →
      Gate4.LessEqual (Gate4.algebra (before pair))
        (Gate4.operatorNorm (Gate4.algebra (before pair))
          (stageOperator (before pair) stage))
        upper)
    (beforeStageBoundIsCommon pair stage)
    (stageNormBound (before pair) stage)

afterStageBelowCommonMajorant :
  ∀ {Operator Bound}
    (pair : CMP109FourStageOrdinaryPair Operator Bound) →
  ∀ stage →
  Gate4.LessEqual (Gate4.algebra (after pair))
    (Gate4.operatorNorm (Gate4.algebra (after pair))
      (stageOperator (after pair) stage))
    (ordinaryStageMajorant pair stage)
afterStageBelowCommonMajorant pair stage =
  subst
    (λ upper →
      Gate4.LessEqual (Gate4.algebra (after pair))
        (Gate4.operatorNorm (Gate4.algebra (after pair))
          (stageOperator (after pair) stage))
        upper)
    (afterStageBoundIsCommon pair stage)
    (stageNormBound (after pair) stage)

-- Transport the AFTER estimate onto the BEFORE algebra used by one selected
-- noncommutative product telescope.  No norm inequality is spent here.
afterStageBelowCommonMajorantOnBeforeAlgebra :
  ∀ {Operator Bound}
    (pair : CMP109FourStageOrdinaryPair Operator Bound) →
  ∀ stage →
  Gate4.LessEqual (Gate4.algebra (before pair))
    (Gate4.operatorNorm (Gate4.algebra (before pair))
      (stageOperator (after pair) stage))
    (ordinaryStageMajorant pair stage)
afterStageBelowCommonMajorantOnBeforeAlgebra pair stage =
  subst
    (λ selectedAlgebra →
      Gate4.LessEqual selectedAlgebra
        (Gate4.operatorNorm selectedAlgebra
          (stageOperator (after pair) stage))
        (ordinaryStageMajorant pair stage))
    (sym (sameOperatorNormAlgebra pair))
    (afterStageBelowCommonMajorant pair stage)

------------------------------------------------------------------------
-- Status / Pareto boundary.
------------------------------------------------------------------------

round407LiteralFourStageCarrierWritten : Bool
round407LiteralFourStageCarrierWritten = true

round407LiteralFourStageCarrierWrittenIsTrue :
  round407LiteralFourStageCarrierWritten ≡ true
round407LiteralFourStageCarrierWrittenIsTrue = refl

round407OrdinaryFactorBoundsCompilerOwned : Bool
round407OrdinaryFactorBoundsCompilerOwned = true

round407OrdinaryFactorBoundsCompilerOwnedIsTrue :
  round407OrdinaryFactorBoundsCompilerOwned ≡ true
round407OrdinaryFactorBoundsCompilerOwnedIsTrue = refl

round407MarkedStageDifferenceStillProofBearing : Bool
round407MarkedStageDifferenceStillProofBearing = true

round407MarkedStageDifferenceStillProofBearingIsTrue :
  round407MarkedStageDifferenceStillProofBearing ≡ true
round407MarkedStageDifferenceStillProofBearingIsTrue = refl

round407SameObjectSelectedTermWeldStillProofBearing : Bool
round407SameObjectSelectedTermWeldStillProofBearing = true

round407SameObjectSelectedTermWeldStillProofBearingIsTrue :
  round407SameObjectSelectedTermWeldStillProofBearing ≡ true
round407SameObjectSelectedTermWeldStillProofBearingIsTrue = refl

round407KernelCertifiedAtCurrentHead : Bool
round407KernelCertifiedAtCurrentHead = false

round407KernelCertifiedAtCurrentHeadIsFalse :
  round407KernelCertifiedAtCurrentHead ≡ false
round407KernelCertifiedAtCurrentHeadIsFalse = refl

-- Source has been written but this connector session has not observed an
-- Agda/kernel check for the exact R407 head, so the local status is deliberately
-- non-promotable until such a receipt exists.
round407CompilerLevel : ProofLevel
round407CompilerLevel = conditional
