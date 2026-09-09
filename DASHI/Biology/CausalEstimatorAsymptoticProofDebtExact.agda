module DASHI.Biology.CausalEstimatorAsymptoticProofDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Biology.CausalEstimatorMetricConsistencyExact as MetricConsistency
import DASHI.Biology.CausalEstimatorFiniteDispersionExact as FiniteDispersion
import DASHI.Biology.CausalEstimatorFiniteProbabilityConsistencyExact as FiniteProbability
import DASHI.Biology.CausalEstimatorFiniteTestDistributionConvergenceExact as FiniteDistribution
import DASHI.Biology.CausalEstimatorWeakNormalLimitDebtSplitExact as DebtSplit

------------------------------------------------------------------------
-- ASYMPTOTIC FRONTIER
--
-- The bounded finite-law lane owns two genuine distributional precursors:
-- (1) outside-ball probability mass -> 0, and (2) convergence of exact finite
-- expectations for every declared test function to an explicit finite target
-- law.  Standard weak-convergence / CLT / calibration theorem families are
-- established mathematics but remain untranscribed in this lane; their next
-- action is source/transcription audit.  The same-estimator normal-limit bridge
-- is separately application-specific mathematical debt.
------------------------------------------------------------------------

data AsymptoticResidual : Set where
  generalProbabilityMeasureSemantics : AsymptoticResidual
  generalWeakConvergenceSemantics : AsymptoticResidual
  asymptoticNormalityTheorem : AsymptoticResidual
  standardErrorLimitCalibration : AsymptoticResidual

data AsymptoticProducerClass : Set where
  probabilityMeasureOwner : AsymptoticProducerClass
  weakConvergenceOwner : AsymptoticProducerClass
  estimatorLimitTheoremOwner : AsymptoticProducerClass
  calibrationTheoremOwner : AsymptoticProducerClass

producerForResidual : AsymptoticResidual → AsymptoticProducerClass
producerForResidual generalProbabilityMeasureSemantics = probabilityMeasureOwner
producerForResidual generalWeakConvergenceSemantics = weakConvergenceOwner
producerForResidual asymptoticNormalityTheorem = estimatorLimitTheoremOwner
producerForResidual standardErrorLimitCalibration = calibrationTheoremOwner

------------------------------------------------------------------------
-- Application-specific selected debt remains mathematical.
------------------------------------------------------------------------

selectedAsymptoticDebtRoute : Debt.ProofDebtRoutingReceipt
selectedAsymptoticDebtRoute =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.novelOpen
    Debt.notTranscribed
    Debt.uncertified
    Debt.sourceOnly
    Debt.mathematicalDebt
    refl

selectedAsymptoticDebtIsMathematical :
  Debt.routedDebt selectedAsymptoticDebtRoute ≡ Debt.mathematicalDebt
selectedAsymptoticDebtIsMathematical = refl

selectedAsymptoticSchedulerAction :
  Debt.scheduleAction
    (Debt.routedDebt selectedAsymptoticDebtRoute)
    (Debt.statementStatus selectedAsymptoticDebtRoute)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.researchMathematics
selectedAsymptoticSchedulerAction = refl

------------------------------------------------------------------------
-- Standard theorem families have a different next action: transcription.
------------------------------------------------------------------------

standardWeakConvergenceRoute : Debt.ProofDebtRoutingReceipt
standardWeakConvergenceRoute =
  DebtSplit.standardTheoremRoute DebtSplit.determiningClassWeakConvergence

standardCLTRoute : Debt.ProofDebtRoutingReceipt
standardCLTRoute =
  DebtSplit.standardTheoremRoute DebtSplit.classicalCentralLimit

standardCalibrationRoute : Debt.ProofDebtRoutingReceipt
standardCalibrationRoute =
  DebtSplit.standardTheoremRoute DebtSplit.limitingStandardErrorCalibration

standardWeakConvergenceSchedulerAction :
  Debt.scheduleAction
    (Debt.routedDebt standardWeakConvergenceRoute)
    (Debt.statementStatus standardWeakConvergenceRoute)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
standardWeakConvergenceSchedulerAction = refl

standardCLTSchedulerAction :
  Debt.scheduleAction
    (Debt.routedDebt standardCLTRoute)
    (Debt.statementStatus standardCLTRoute)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
standardCLTSchedulerAction = refl

standardCalibrationSchedulerAction :
  Debt.scheduleAction
    (Debt.routedDebt standardCalibrationRoute)
    (Debt.statementStatus standardCalibrationRoute)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
standardCalibrationSchedulerAction = refl

------------------------------------------------------------------------
-- Closed-coordinate witnesses.
------------------------------------------------------------------------

metricConsistencyBoundary :
  MetricConsistency.CausalEstimatorMetricConsistencyBoundary
metricConsistencyBoundary =
  MetricConsistency.canonicalCausalEstimatorMetricConsistencyBoundary

finiteDispersionBoundary :
  FiniteDispersion.CausalEstimatorFiniteDispersionBoundary
finiteDispersionBoundary =
  FiniteDispersion.canonicalCausalEstimatorFiniteDispersionBoundary

finiteProbabilityConsistencyBoundary :
  FiniteProbability.CausalEstimatorFiniteProbabilityConsistencyBoundary
finiteProbabilityConsistencyBoundary =
  FiniteProbability.canonicalCausalEstimatorFiniteProbabilityConsistencyBoundary

finiteTestDistributionBoundary :
  FiniteDistribution.CausalEstimatorFiniteTestDistributionBoundary
finiteTestDistributionBoundary =
  FiniteDistribution.canonicalCausalEstimatorFiniteTestDistributionBoundary

weakNormalDebtSplitBoundary : DebtSplit.WeakNormalLimitDebtSplitBoundary
weakNormalDebtSplitBoundary = DebtSplit.canonicalWeakNormalLimitDebtSplitBoundary

introspectiveBoundary : Introspective.IntrospectiveProofLoopBoundary
introspectiveBoundary = Introspective.canonicalIntrospectiveProofLoopBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteProbabilityConsistencyMeansGeneralMeasurePermission : Set where

data FiniteTestConvergenceMeansGeneralWeakConvergencePermission : Set where

data FiniteTargetLawMeansNormalLawPermission : Set where

data FiniteVarianceMeansAsymptoticNormalityPermission : Set where

data StandardCLTClosesApplicationEstimatorPermission : Set where

data MissingOwnerMayBeReportedClosedPermission : Set where

data MathematicalDebtMayBeCalledCertificationDebtPermission : Set where

finiteProbabilityConsistencyDoesNotBecomeGeneralMeasure :
  FiniteProbabilityConsistencyMeansGeneralMeasurePermission → ⊥
finiteProbabilityConsistencyDoesNotBecomeGeneralMeasure ()

finiteTestConvergenceDoesNotBecomeGeneralWeakConvergence :
  FiniteTestConvergenceMeansGeneralWeakConvergencePermission → ⊥
finiteTestConvergenceDoesNotBecomeGeneralWeakConvergence ()

finiteTargetLawDoesNotBecomeNormalLaw :
  FiniteTargetLawMeansNormalLawPermission → ⊥
finiteTargetLawDoesNotBecomeNormalLaw ()

finiteVarianceDoesNotBecomeAsymptoticNormality :
  FiniteVarianceMeansAsymptoticNormalityPermission → ⊥
finiteVarianceDoesNotBecomeAsymptoticNormality ()

standardCLTDoesNotCloseArbitraryEstimator :
  StandardCLTClosesApplicationEstimatorPermission → ⊥
standardCLTDoesNotCloseArbitraryEstimator ()

missingAsymptoticOwnerCannotBeReportedClosed :
  MissingOwnerMayBeReportedClosedPermission → ⊥
missingAsymptoticOwnerCannotBeReportedClosed ()

mathematicalDebtCannotBeRelabelledCertificationDebt :
  MathematicalDebtMayBeCalledCertificationDebtPermission → ⊥
mathematicalDebtCannotBeRelabelledCertificationDebt ()

record CausalEstimatorCompletionFrontier : Set where
  constructor causal-estimator-completion-frontier
  field
    finiteExpectationClosed : Bool
    finiteUnbiasednessClosed : Bool
    finiteVarianceAndMSEClosed : Bool
    metricConsistencyShapeClosed : Bool
    finiteLawConvergenceInProbabilityClosed : Bool
    finiteTestFunctionDistributionConvergenceClosed : Bool
    standardWeakConvergenceTheoremNeedsTranscription : Bool
    standardCLTNeedsTranscription : Bool
    standardCalibrationNeedsTranscription : Bool
    generalProbabilityMeasureClosed : Bool
    generalWeakConvergenceClosed : Bool
    applicationAsymptoticNormalityClosed : Bool
    standardErrorLimitCalibrationClosed : Bool
    applicationDebtStillMathematical : Bool
    certificationDebtClaimedForMissingMathematics : Bool

canonicalCausalEstimatorCompletionFrontier :
  CausalEstimatorCompletionFrontier
canonicalCausalEstimatorCompletionFrontier =
  causal-estimator-completion-frontier
    true true true true true true
    true true true
    false false false false
    true false
