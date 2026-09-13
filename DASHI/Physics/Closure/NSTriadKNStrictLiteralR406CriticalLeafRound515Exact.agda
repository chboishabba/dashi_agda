module DASHI.Physics.Closure.NSTriadKNStrictLiteralR406CriticalLeafRound515Exact where

------------------------------------------------------------------------
-- ROUND515 / STRICT INTROSPECTIVE SCHEDULER FOR TERMINAL LEAF B
--
-- R509--R514 found that the old two-coordinate observer was under-specified.
-- The actual physical consumer distinguishes at least the following:
--
--   1. literal critical-observable realization on the live trajectory;
--   2. the critical energy inequality on those SAME observables;
--   3. the phase-sensitive signed-production estimate with literal R406
--      remainder on its RHS;
--   4. a cutoff-uniform initial-critical ceiling;
--   5. strictly positive retained viscosity.
--
-- R507 remains a useful adapter for importing an older Round104 slice, but it
-- is no longer sufficient by itself: only its remainder is welded to R406.
--
-- This scheduler is intentionally receipt-level.  It does not manufacture any
-- of the five physical inputs and therefore keeps Clay promotion false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR414CriticalObservableRealizationNoGoRound513Exact as R513
import DASHI.Physics.Closure.NSTriadKNRetainedViscosityPositivityNoGoRound514Exact as R514
import DASHI.Physics.Closure.NSTriadKNLiteralR406CriticalProductionProofSearchRound508Exact as R508
import DASHI.Physics.Closure.NSTriadKNInitialCriticalRealizationToR421Round512Exact as R512
import DASHI.Physics.Closure.NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact as R507

data StrictCriticalResidual : Set where
  missingPhysicalCriticalObservableRealization : StrictCriticalResidual
  missingCriticalEnergyInequality : StrictCriticalResidual
  missingPhaseSensitiveSignedProductionEstimate : StrictCriticalResidual
  missingUniformInitialCriticalCeiling : StrictCriticalResidual
  missingPositiveRetainedViscosity : StrictCriticalResidual
  strictCriticalLeafClosed : StrictCriticalResidual

record StrictCriticalStatus : Set where
  constructor strict-critical-status
  field
    physicalCriticalObservableRealizationPresent : Bool
    criticalEnergyInequalityPresent : Bool
    phaseSensitiveSignedProductionEstimatePresent : Bool
    uniformInitialCriticalCeilingPresent : Bool
    positiveRetainedViscosityPresent : Bool

open StrictCriticalStatus public

firstMissing : StrictCriticalStatus → StrictCriticalResidual
firstMissing (strict-critical-status false e p c v) =
  missingPhysicalCriticalObservableRealization
firstMissing (strict-critical-status true false p c v) =
  missingCriticalEnergyInequality
firstMissing (strict-critical-status true true false c v) =
  missingPhaseSensitiveSignedProductionEstimate
firstMissing (strict-critical-status true true true false v) =
  missingUniformInitialCriticalCeiling
firstMissing (strict-critical-status true true true true false) =
  missingPositiveRetainedViscosity
firstMissing (strict-critical-status true true true true true) =
  strictCriticalLeafClosed

data ProducerClass : Set where
  physicalCriticalObservableProducer : ProducerClass
  criticalEnergyIdentityProducer : ProducerClass
  signedNetworkCancellationProducer : ProducerClass
  initialCriticalRealizationProducer : ProducerClass
  retainedViscosityPositivityProducer : ProducerClass
  noProducerNeeded : ProducerClass

producerFor : StrictCriticalResidual → ProducerClass
producerFor missingPhysicalCriticalObservableRealization =
  physicalCriticalObservableProducer
producerFor missingCriticalEnergyInequality =
  criticalEnergyIdentityProducer
producerFor missingPhaseSensitiveSignedProductionEstimate =
  signedNetworkCancellationProducer
producerFor missingUniformInitialCriticalCeiling =
  initialCriticalRealizationProducer
producerFor missingPositiveRetainedViscosity =
  retainedViscosityPositivityProducer
producerFor strictCriticalLeafClosed = noProducerNeeded

data Mechanism : Set where
  LookWholeNetworkCriticalObservableFold : Mechanism
  ThinkCriticalEnergyIdentity : Mechanism
  ThinkExternalCrossTriadSignedPayment : Mechanism
  LookLiteralInitialCriticalRealization : Mechanism
  ProveRetainedViscosityPositive : Mechanism
  CompileR421 : Mechanism

mechanismFor : StrictCriticalResidual → Mechanism
mechanismFor missingPhysicalCriticalObservableRealization =
  LookWholeNetworkCriticalObservableFold
mechanismFor missingCriticalEnergyInequality =
  ThinkCriticalEnergyIdentity
mechanismFor missingPhaseSensitiveSignedProductionEstimate =
  ThinkExternalCrossTriadSignedPayment
mechanismFor missingUniformInitialCriticalCeiling =
  LookLiteralInitialCriticalRealization
mechanismFor missingPositiveRetainedViscosity =
  ProveRetainedViscosityPositive
mechanismFor strictCriticalLeafClosed = CompileR421

currentStatus : StrictCriticalStatus
currentStatus = strict-critical-status false false false false false

currentFirstMissing :
  firstMissing currentStatus
  ≡ missingPhysicalCriticalObservableRealization
currentFirstMissing = refl

currentMechanism :
  mechanismFor (firstMissing currentStatus)
  ≡ LookWholeNetworkCriticalObservableFold
currentMechanism = refl

------------------------------------------------------------------------
-- Audit regressions.
------------------------------------------------------------------------

round515R513TrajectoryIndexNotPhysicalRealization : Bool
round515R513TrajectoryIndexNotPhysicalRealization =
  R513.round513R414TrajectoryIndexAloneRealizesCriticalObservables

round515R514PositiveRetainedViscosityMissingFromOldSlice : Bool
round515R514PositiveRetainedViscosityMissingFromOldSlice =
  R514.round514PositiveRetainedViscosityTypedInRound104Slice

round515R507RemainderOnlyAdapterNotFullPhysicalRealization : Bool
round515R507RemainderOnlyAdapterNotFullPhysicalRealization = true

round515R512InitialCeilingCompilerAvailable : Bool
round515R512InitialCeilingCompilerAvailable = true

round515R508OldFirstMissingWasAnalyticPayment : Bool
round515R508OldFirstMissingWasAnalyticPayment = true

round515IntrospectionMovesFirstMissingEarlierToPhysicalRealization : Bool
round515IntrospectionMovesFirstMissingEarlierToPhysicalRealization = true

round515ClayPromotion : Bool
round515ClayPromotion = false

round515R513TrajectoryIndexNotPhysicalRealizationIsFalse :
  round515R513TrajectoryIndexNotPhysicalRealization ≡ false
round515R513TrajectoryIndexNotPhysicalRealizationIsFalse =
  R513.round513R414TrajectoryIndexAloneRealizesCriticalObservablesIsFalse

round515R514PositiveRetainedViscosityMissingFromOldSliceIsFalse :
  round515R514PositiveRetainedViscosityMissingFromOldSlice ≡ false
round515R514PositiveRetainedViscosityMissingFromOldSliceIsFalse =
  R514.round514PositiveRetainedViscosityTypedInRound104SliceIsFalse

round515IntrospectionMovesFirstMissingEarlierToPhysicalRealizationIsTrue :
  round515IntrospectionMovesFirstMissingEarlierToPhysicalRealization ≡ true
round515IntrospectionMovesFirstMissingEarlierToPhysicalRealizationIsTrue = refl

round515ClayPromotionIsFalse : round515ClayPromotion ≡ false
round515ClayPromotionIsFalse = refl
