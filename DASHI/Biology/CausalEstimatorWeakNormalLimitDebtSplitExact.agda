module DASHI.Biology.CausalEstimatorWeakNormalLimitDebtSplitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Biology.CausalEstimatorFiniteTestDistributionConvergenceExact as FiniteTest

------------------------------------------------------------------------
-- WEAK / NORMAL LIMIT DEBT SPLIT
--
-- Standard weak-convergence / CLT / limiting-calibration theorems are
-- established mathematics, but no exact source statement has yet been
-- transcribed and aligned in this lane.  That is transcription debt.
--
-- The stronger statement that THIS estimator family, under THIS scaling and
-- THESE hypotheses, has THIS limiting law is a separate application theorem.
-- Until those hypotheses and the same-object bridge are supplied it remains
-- mathematical debt, not certification debt.
------------------------------------------------------------------------

data StandardAsymptoticTheoremFamily : Set where
  determiningClassWeakConvergence
  classicalCentralLimit
  limitingStandardErrorCalibration : StandardAsymptoticTheoremFamily

standardTheoremRoute : StandardAsymptoticTheoremFamily → Debt.ProofDebtRoutingReceipt
standardTheoremRoute _ =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.notTranscribed
    Debt.uncertified
    Debt.sourceOnly
    Debt.transcriptionDebt
    refl

standardWeakConvergenceNeedsTranscription :
  Debt.routedDebt (standardTheoremRoute determiningClassWeakConvergence)
  ≡ Debt.transcriptionDebt
standardWeakConvergenceNeedsTranscription = refl

standardCLTNeedsTranscription :
  Debt.routedDebt (standardTheoremRoute classicalCentralLimit)
  ≡ Debt.transcriptionDebt
standardCLTNeedsTranscription = refl

standardCalibrationNeedsTranscription :
  Debt.routedDebt (standardTheoremRoute limitingStandardErrorCalibration)
  ≡ Debt.transcriptionDebt
standardCalibrationNeedsTranscription = refl

standardTheoremSchedulerAction :
  (family : StandardAsymptoticTheoremFamily) →
  Debt.scheduleAction
    (Debt.routedDebt (standardTheoremRoute family))
    (Debt.statementStatus (standardTheoremRoute family))
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
standardTheoremSchedulerAction family = refl

------------------------------------------------------------------------
-- Application-specific normal-limit requirement.
------------------------------------------------------------------------

record ApplicationNormalLimitRequirement : Set₁ where
  constructor application-normal-limit-requirement
  field
    EstimatorFamily : Set
    Scaling : Set
    LimitingLaw : Set
    HypothesisPackage : Set

    estimatorFamily : EstimatorFamily
    scaling : Scaling
    limitingLaw : LimitingLaw

    hypotheses : HypothesisPackage

    sameEstimatorAsLiveConsumer : Set
    sameEstimatorReceipt : sameEstimatorAsLiveConsumer

    sameScalingAsClaimedLimit : Set
    sameScalingReceipt : sameScalingAsClaimedLimit

    sameTargetLawAsClaimedLimit : Set
    sameTargetLawReceipt : sameTargetLawAsClaimedLimit

open ApplicationNormalLimitRequirement public

applicationNormalLimitRoute :
  ApplicationNormalLimitRequirement → Debt.ProofDebtRoutingReceipt
applicationNormalLimitRoute _ =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.novelOpen
    Debt.notTranscribed
    Debt.uncertified
    Debt.sourceOnly
    Debt.mathematicalDebt
    refl

applicationNormalLimitNeedsMathematics :
  (requirement : ApplicationNormalLimitRequirement) →
  Debt.routedDebt (applicationNormalLimitRoute requirement)
  ≡ Debt.mathematicalDebt
applicationNormalLimitNeedsMathematics requirement = refl

applicationNormalLimitSchedulerAction :
  (requirement : ApplicationNormalLimitRequirement) →
  Debt.scheduleAction
    (Debt.routedDebt (applicationNormalLimitRoute requirement))
    (Debt.statementStatus (applicationNormalLimitRoute requirement))
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.researchMathematics
applicationNormalLimitSchedulerAction requirement = refl

------------------------------------------------------------------------
-- Once an exact theorem statement has been sourced and aligned, downstream
-- consumers may be developed conditionally.  The deferred source receipt still
-- contains no inhabitant of the theorem proposition.
------------------------------------------------------------------------

record AlignedNormalLimitTheorem (T : Set) : Set where
  constructor aligned-normal-limit-theorem
  field
    deferred : Debt.SourceAlignedDeferredTheorem T

open AlignedNormalLimitTheorem public

alignedNormalLimitRoute :
  {T : Set} →
  AlignedNormalLimitTheorem T →
  Debt.ProofDebtRoutingReceipt
alignedNormalLimitRoute _ =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.sourceAligned
    Debt.proofDeferred
    Debt.externalLean
    Debt.certificationDebt
    refl

alignedNormalLimitIsCertificationDebt :
  {T : Set} →
  (aligned : AlignedNormalLimitTheorem T) →
  Debt.routedDebt (alignedNormalLimitRoute aligned)
  ≡ Debt.certificationDebt
alignedNormalLimitIsCertificationDebt aligned = refl

alignedNormalLimitSchedulerAction :
  {T : Set} →
  (aligned : AlignedNormalLimitTheorem T) →
  Debt.scheduleAction
    (Debt.routedDebt (alignedNormalLimitRoute aligned))
    (Debt.statementStatus (alignedNormalLimitRoute aligned))
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.sendAristotleLean
alignedNormalLimitSchedulerAction aligned = refl

ConditionalNormalLimitConsumer : Set → Set → Set
ConditionalNormalLimitConsumer T Result = Debt.ConditionalDevelopment T Result

runConditionalNormalLimitConsumer :
  {T Result : Set} →
  ConditionalNormalLimitConsumer T Result →
  T → Result
runConditionalNormalLimitConsumer = Debt.runConditionalDevelopment

------------------------------------------------------------------------
-- Existing finite-test convergence is an input boundary, not a weak-limit
-- theorem.  A determining-class theorem is still needed to promote it.
------------------------------------------------------------------------

finiteTestBoundary : FiniteTest.CausalEstimatorFiniteTestDistributionBoundary
finiteTestBoundary = FiniteTest.canonicalCausalEstimatorFiniteTestDistributionBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data StandardCLTCitationAppliesToArbitraryEstimatorPermission : Set where

data FiniteTestConvergenceMeansWeakConvergencePermission : Set where

data SourceAlignedDeferredTheoremMeansTheoremProvedPermission : Set where

data ApplicationHypothesesMeanNormalLimitPermission : Set where

data TranscriptionDebtMeansMathematicalDebtPermission : Set where

standardCLTDoesNotApplyToArbitraryEstimator :
  StandardCLTCitationAppliesToArbitraryEstimatorPermission → ⊥
standardCLTDoesNotApplyToArbitraryEstimator ()

finiteTestConvergenceStillNeedsDeterminingClassTheorem :
  FiniteTestConvergenceMeansWeakConvergencePermission → ⊥
finiteTestConvergenceStillNeedsDeterminingClassTheorem ()

deferredSourceDoesNotManufactureTheorem :
  SourceAlignedDeferredTheoremMeansTheoremProvedPermission → ⊥
deferredSourceDoesNotManufactureTheorem ()

hypothesesAloneDoNotManufactureNormalLimit :
  ApplicationHypothesesMeanNormalLimitPermission → ⊥
hypothesesAloneDoNotManufactureNormalLimit ()

transcriptionDebtIsNotNovelMathematics :
  TranscriptionDebtMeansMathematicalDebtPermission → ⊥
transcriptionDebtIsNotNovelMathematics ()

record WeakNormalLimitDebtSplitBoundary : Set where
  constructor weak-normal-limit-debt-split-boundary
  field
    standardWeakConvergenceIsEstablishedMath : Bool
    standardCLTIsEstablishedMath : Bool
    standardTheoremTranscriptionStillRequired : Bool
    applicationSameEstimatorTheoremStillRequired : Bool
    alignedDeferredRoutesToCertificationDebt : Bool
    finiteTestConvergenceAlreadyAvailable : Bool
    sourceAlignmentCreatesProof : Bool
    standardCitationAutoClosesApplication : Bool

canonicalWeakNormalLimitDebtSplitBoundary : WeakNormalLimitDebtSplitBoundary
canonicalWeakNormalLimitDebtSplitBoundary =
  weak-normal-limit-debt-split-boundary
    true true true true true true false false
