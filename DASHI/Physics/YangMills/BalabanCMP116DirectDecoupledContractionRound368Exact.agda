module DASHI.Physics.YangMills.BalabanCMP116DirectDecoupledContractionRound368Exact where

------------------------------------------------------------------------
-- ROUND368 / KEEP SAME-PARAMETER CONTRACTION DISTINCT FROM PARAMETER DEFECT
--
-- CMP116 Part II, Sect. 1 takes the inherited linearizing fixed-point equation
-- and replaces H by the literal decoupled propagator H(s(Y0)).  Around
-- (1.12)--(1.14) it proves that, for each fixed decoupling parameter, the map
--
--   F_s(X) = C(A' - H(s) X)
--
-- preserves one small ball and is contractive there.
--
-- This source theorem pays the SAME-PARAMETER contraction used by R365.  It
-- does NOT by itself pay R366's CROSS-PARAMETER estimate comparing
--
--   C(A' - H_L X)   and   C(A' - H_R X).
--
-- R367 therefore remains a valid optional producer if an actual C-Lipschitz
-- theorem is acquired, but CMP116's sentence "it is contractive" must not be
-- silently retyped as that theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as QIF

------------------------------------------------------------------------
-- Direct source-shaped composite contraction carrier.
------------------------------------------------------------------------

record CMP116DecoupledCompositeContraction
    (Parameter Point Bound : Set) : Set₁ where
  field
    metric : QIF.QuantitativeMetricAlgebra Point Bound

    -- Literal source map after H -> H(s(Y0)).
    sourceMap : Parameter → Point → Point

    -- Each fixed parameter has its own source-proved invariant contraction
    -- ball.  A stronger common-ball weld may later identify these balls.
    sourceBall : Parameter → QIF.InvariantContractionBall metric

    sourceBallUsesLiteralMap :
      ∀ parameter →
      QIF.map (sourceBall parameter) ≡ sourceMap parameter

open CMP116DecoupledCompositeContraction public

symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

sourceMapPreservesItsBall :
  ∀ {Parameter Point Bound}
    (dataSet : CMP116DecoupledCompositeContraction Parameter Point Bound)
    parameter point →
  QIF.InBall (sourceBall dataSet parameter) point →
  QIF.InBall (sourceBall dataSet parameter)
    (sourceMap dataSet parameter point)
sourceMapPreservesItsBall dataSet parameter point inBall
  rewrite symEq (sourceBallUsesLiteralMap dataSet parameter) =
  QIF.mapPreservesBall (sourceBall dataSet parameter) point inBall

sourceMapContractiveAtFixedParameter :
  ∀ {Parameter Point Bound}
    (dataSet : CMP116DecoupledCompositeContraction Parameter Point Bound)
    parameter left right →
  QIF.InBall (sourceBall dataSet parameter) left →
  QIF.InBall (sourceBall dataSet parameter) right →
  QIF.LessEqual (metric dataSet)
    (QIF.distance (metric dataSet)
      (sourceMap dataSet parameter left)
      (sourceMap dataSet parameter right))
    (QIF.multiply (metric dataSet)
      (QIF.contractionFactor (sourceBall dataSet parameter))
      (QIF.distance (metric dataSet) left right))
sourceMapContractiveAtFixedParameter dataSet parameter left right leftIn rightIn
  rewrite symEq (sourceBallUsesLiteralMap dataSet parameter) =
  QIF.mapContractive (sourceBall dataSet parameter)
    left right leftIn rightIn

sourceContractionFactorBelowOne :
  ∀ {Parameter Point Bound}
    (dataSet : CMP116DecoupledCompositeContraction Parameter Point Bound)
    parameter →
  QIF.StrictlyBelowOne (metric dataSet)
    (QIF.contractionFactor (sourceBall dataSet parameter))
sourceContractionFactorBelowOne dataSet parameter =
  QIF.contractionFactorBelowOne (sourceBall dataSet parameter)

------------------------------------------------------------------------
-- Pareto / WrongType accounting.
------------------------------------------------------------------------

cmp116SameParameterCompositeContractionSourceLevel : ProofLevel
cmp116SameParameterCompositeContractionSourceLevel = standardImported

literalDecoupledMapSameObjectAttachmentLevel : ProofLevel
literalDecoupledMapSameObjectAttachmentLevel = conditional

commonBallAcrossTwoParametersLevel : ProofLevel
commonBallAcrossTwoParametersLevel = conditional

crossParameterMapDefectLevel : ProofLevel
crossParameterMapDefectLevel = conditional

sameParameterContractionPaysR365Factor : Bool
sameParameterContractionPaysR365Factor = true

sameParameterContractionPaysR365FactorIsTrue :
  sameParameterContractionPaysR365Factor ≡ true
sameParameterContractionPaysR365FactorIsTrue = refl

sameParameterContractionPaysR366CrossParameterDefect : Bool
sameParameterContractionPaysR366CrossParameterDefect = false

sameParameterContractionPaysR366CrossParameterDefectIsFalse :
  sameParameterContractionPaysR366CrossParameterDefect ≡ false
sameParameterContractionPaysR366CrossParameterDefectIsFalse = refl

cmp102ToCmp116CIdentityMandatoryBeforeSourceContraction : Bool
cmp102ToCmp116CIdentityMandatoryBeforeSourceContraction = false

cmp102ToCmp116CIdentityMandatoryBeforeSourceContractionIsFalse :
  cmp102ToCmp116CIdentityMandatoryBeforeSourceContraction ≡ false
cmp102ToCmp116CIdentityMandatoryBeforeSourceContractionIsFalse = refl

cLipschitzStillOptionalCrossParameterProducer : Bool
cLipschitzStillOptionalCrossParameterProducer = true

cLipschitzStillOptionalCrossParameterProducerIsTrue :
  cLipschitzStillOptionalCrossParameterProducer ≡ true
cLipschitzStillOptionalCrossParameterProducerIsTrue = refl

record Round368Boundary : Set where
  constructor round368-boundary
  field
    sourceCompositeContractionAndParameterSensitivityDistinct : Bool
    sourceCompositeContractionAndParameterSensitivityDistinctIsTrue :
      sourceCompositeContractionAndParameterSensitivityDistinct ≡ true

    directCMP116ContractionAvoidsCrossPaperCIdentity : Bool
    directCMP116ContractionAvoidsCrossPaperCIdentityIsTrue :
      directCMP116ContractionAvoidsCrossPaperCIdentity ≡ true

    cmp99HDefectStillNeedsSameObjectAttachment : Bool
    cmp99HDefectStillNeedsSameObjectAttachmentIsTrue :
      cmp99HDefectStillNeedsSameObjectAttachment ≡ true

canonicalRound368Boundary : Round368Boundary
canonicalRound368Boundary =
  round368-boundary true refl true refl true refl

round368SourceSeparationLevel : ProofLevel
round368SourceSeparationLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
