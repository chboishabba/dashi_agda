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

------------------------------------------------------------------------
-- ASYMPTOTIC FRONTIER
--
-- The bounded finite-law lane now owns two genuine distributional precursors:
-- (1) outside-ball probability mass -> 0, and (2) convergence of exact finite
-- expectations for every declared test function to an explicit finite target
-- law.  The second still requires a test-class adequacy receipt and is not
-- promoted to general weak convergence.  The remaining unpaid frontier is a
-- general probability/measure owner, a determining test-class/weak-convergence
-- theorem, a same-estimator asymptotic-normality theorem, and standard-error
-- limit calibration.
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

introspectiveBoundary : Introspective.IntrospectiveProofLoopBoundary
introspectiveBoundary = Introspective.canonicalIntrospectiveProofLoopBoundary

data FiniteProbabilityConsistencyMeansGeneralMeasurePermission : Set where

data FiniteTestConvergenceMeansGeneralWeakConvergencePermission : Set where

data FiniteTargetLawMeansNormalLawPermission : Set where

data FiniteVarianceMeansAsymptoticNormalityPermission : Set where

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
    generalProbabilityMeasureClosed : Bool
    generalWeakConvergenceClosed : Bool
    asymptoticNormalityClosed : Bool
    standardErrorLimitCalibrationClosed : Bool
    currentDebtIsMathematicalOrSourceTheoremOwnership : Bool
    certificationDebtClaimedForMissingMathematics : Bool

canonicalCausalEstimatorCompletionFrontier :
  CausalEstimatorCompletionFrontier
canonicalCausalEstimatorCompletionFrontier =
  causal-estimator-completion-frontier
    true true true true true true
    false false false false
    true false
