module DASHI.Biology.CausalEstimatorAsymptoticProofDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Biology.CausalEstimatorMetricConsistencyExact as MetricConsistency
import DASHI.Biology.CausalEstimatorFiniteDispersionExact as FiniteDispersion
import DASHI.Biology.CausalEstimatorFiniteProbabilityConsistencyExact as FiniteProbability

------------------------------------------------------------------------
-- ASYMPTOTIC FRONTIER
--
-- The bounded finite-law lane now has an exact convergence-in-probability
-- analogue: for each estimator radius, the finite normalized probability mass
-- outside the target ball converges to zero via the existing metric kernel.
-- The remaining unpaid frontier is genuinely distributional: a general
-- probability/measure owner, weak/distributional convergence, a same-estimator
-- asymptotic-normality theorem, and standard-error limit calibration.
------------------------------------------------------------------------

data AsymptoticResidual : Set where
  generalProbabilityMeasureSemantics : AsymptoticResidual
  distributionalConvergenceSemantics : AsymptoticResidual
  asymptoticNormalityTheorem : AsymptoticResidual
  standardErrorLimitCalibration : AsymptoticResidual

data AsymptoticProducerClass : Set where
  probabilityMeasureOwner : AsymptoticProducerClass
  distributionConvergenceOwner : AsymptoticProducerClass
  estimatorLimitTheoremOwner : AsymptoticProducerClass
  calibrationTheoremOwner : AsymptoticProducerClass

producerForResidual : AsymptoticResidual → AsymptoticProducerClass
producerForResidual generalProbabilityMeasureSemantics = probabilityMeasureOwner
producerForResidual distributionalConvergenceSemantics = distributionConvergenceOwner
producerForResidual asymptoticNormalityTheorem = estimatorLimitTheoremOwner
producerForResidual standardErrorLimitCalibration = calibrationTheoremOwner

------------------------------------------------------------------------
-- Current exact selected debt.
--
-- For an arbitrary causal estimator, asymptotic normality is not available
-- merely from finite unbiasedness, finite variance, metric consistency, or the
-- bounded finite-law convergence-in-probability bridge.  Until a same-estimator
-- distributional theorem/source is identified and aligned, the exact
-- application claim remains mathematical debt under the canonical router.
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
-- Existing closed coordinates retained as witnesses to the introspective cut.
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

introspectiveBoundary : Introspective.IntrospectiveProofLoopBoundary
introspectiveBoundary = Introspective.canonicalIntrospectiveProofLoopBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteProbabilityConsistencyMeansGeneralMeasurePermission : Set where

data FiniteProbabilityConsistencyMeansWeakConvergencePermission : Set where

data FiniteVarianceMeansAsymptoticNormalityPermission : Set where

data FiniteUnbiasednessMeansCLTPermission : Set where

data MissingOwnerMayBeReportedClosedPermission : Set where

data MathematicalDebtMayBeCalledCertificationDebtPermission : Set where

finiteProbabilityConsistencyDoesNotBecomeGeneralMeasure :
  FiniteProbabilityConsistencyMeansGeneralMeasurePermission → ⊥
finiteProbabilityConsistencyDoesNotBecomeGeneralMeasure ()

finiteProbabilityConsistencyDoesNotBecomeWeakConvergence :
  FiniteProbabilityConsistencyMeansWeakConvergencePermission → ⊥
finiteProbabilityConsistencyDoesNotBecomeWeakConvergence ()

finiteVarianceDoesNotBecomeAsymptoticNormality :
  FiniteVarianceMeansAsymptoticNormalityPermission → ⊥
finiteVarianceDoesNotBecomeAsymptoticNormality ()

finiteUnbiasednessDoesNotBecomeCLT :
  FiniteUnbiasednessMeansCLTPermission → ⊥
finiteUnbiasednessDoesNotBecomeCLT ()

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
    generalProbabilityMeasureClosed : Bool
    distributionalConvergenceClosed : Bool
    asymptoticNormalityClosed : Bool
    standardErrorLimitCalibrationClosed : Bool
    currentDebtIsMathematicalOrSourceTheoremOwnership : Bool
    certificationDebtClaimedForMissingMathematics : Bool

canonicalCausalEstimatorCompletionFrontier :
  CausalEstimatorCompletionFrontier
canonicalCausalEstimatorCompletionFrontier =
  causal-estimator-completion-frontier
    true true true true true
    false false false false
    true false
