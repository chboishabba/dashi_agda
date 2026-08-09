module DASHI.Moonshine.SSPModularCharacterProjectionRound5Validation where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Biology.CoarseFineTenSectorProjectionExact as Projection
import DASHI.Biology.D4NineCellOrbitCompressionExact as D4
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Relational
import DASHI.Moonshine.C3CoarseFineRatioTypingExact as Ratios
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact as C3
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

validationExponent5 : Exponent.monsterOrderExponent Lane.p5 ≡ 9
validationExponent5 = Exponent.p5ExponentIsNine

validationExponent7 : Exponent.monsterOrderExponent Lane.p7 ≡ 6
validationExponent7 = Exponent.p7ExponentIsSix

validationExponent13 : Exponent.monsterOrderExponent Lane.p13 ≡ 3
validationExponent13 = Exponent.p13ExponentIsThree

validation3BDimension : C3.augmentation C3.monster3BCharacter ≡ 196883
validation3BDimension = C3.monster3BDimensionIs196883

validation3BTrace : C3.generatorTrace C3.monster3BCharacter ≡ 53
validation3BTrace = C3.monster3BGeneratorTraceIs53

validationV2Trace : C3.moonshineV2TraceAt3B ≡ 54
validationV2Trace = C3.moonshineV2TraceAt3BIs54

validationTypedFineDimension : Ratios.fineRegularDimension ≡ 196830
validationTypedFineDimension = Ratios.fineRegularDimensionIs196830

validationTypedCoarseShare :
  Ratios.TypedRatio Ratios.coarseShareOfWholeRatio
validationTypedCoarseShare = Ratios.coarseShareOfWhole

validationNonidentityCancellation :
  Ratios.fineContribution Ratios.nonidentityEvaluation ≡ 0
validationNonidentityCancellation = Ratios.nonidentityFineContributionIsZero

validationD4Carrier : D4.orbitSize D4.centreOrbit
                    + D4.orbitSize D4.edgeOrbit
                    + D4.orbitSize D4.cornerOrbit
                    ≡ 9
validationD4Carrier = D4.nineCellOrbitCount

validationCodec :
  (cell : D4.NineCell) →
  D4.decodeCell (D4.encodeCell cell) ≡ cell
validationCodec = D4.decodeAfterEncode

validationCommonMode :
  (value : ℚ) →
  Projection.average (Projection.broadcast value) ≡ value
validationCommonMode = Projection.averageBroadcast

validationResidual :
  (field : Projection.TenField) →
  Projection.sumTen (Projection.fineResidual field) ≡ 0ℚ
validationResidual = Projection.fineResidualHasZeroSum

validationAppraisalFibre : Relational.appraisalFibreStateCount ≡ 729
validationAppraisalFibre = Relational.appraisalFibreStateCountIs729

validationPointedExpansion :
  Relational.appraisalFibreStateCount ≡ (8 * 10 + 1) * 9
validationPointedExpansion = Relational.appraisalFibreAsPointedExpansion

validationRecursiveFineCarrier : Relational.recursiveFineCarrierSize ≡ 65610
validationRecursiveFineCarrier = Relational.recursiveFineCarrierSizeIs65610

validationCompleteCycle : Relational.completeCycleStateCount ≡ 531441
validationCompleteCycle = Relational.completeCycleStateCountIs531441

validationAddressLaw :
  11 ≡ 1 + 10
validationAddressLaw = refl

validationModularBoundary :
  Modular.ModularCurveBoundary
validationModularBoundary = Modular.canonicalModularCurveBoundary
