module DASHI.Physics.Closure.KernelAdmissibilityVacuumRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Geometry.AdmissibilityJetSpec as Spec
import DASHI.Geometry.InvariantSignatureDecidability as Decide
import DASHI.Physics.Closure.FirstWitnessVacuumBridge as Witness
import DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary as Vacuum

------------------------------------------------------------------------
-- Compact import/regression surface for the kernel -> admissibility ->
-- invariant signature -> first witness -> vacuum geometry candidate route.

metricDepthIsTwoJet :
  Spec.jetOrder Spec.metricDiffeomorphismTwoJetSpec ≡ suc (suc zero)
metricDepthIsTwoJet = refl

metricRouteIsQuotientFirst :
  Spec.quotientFirst Spec.metricDiffeomorphismTwoJetSpec ≡ true
metricRouteIsQuotientFirst = refl

metricRouteDoesNotClaimPhysicalDerivation :
  Spec.physicalDerivationClaimed Spec.metricDiffeomorphismTwoJetSpec ≡ false
metricRouteDoesNotClaimPhysicalDerivation = refl

currentInvariantFamilyDoesNotForceOrbitSeparation :
  Decide.currentDepthSeparatesAllOrbits Decide.canonicalDepthDecisionBoundary ≡ false
currentInvariantFamilyDoesNotForceOrbitSeparation = refl

invariantBoundaryPermitsDeeperLift :
  Decide.liftingPermitted Decide.canonicalDepthDecisionBoundary ≡ true
invariantBoundaryPermitsDeeperLift = refl

uniqueFirstWitnessHasExactOnceReceipt :
  Witness.exactOnceDischarge Witness.uniqueFailureRow ≡ true
uniqueFirstWitnessHasExactOnceReceipt = refl

uniqueFirstWitnessFinalQuotientIsScheduleInvariant :
  Witness.scheduleMayChangeFinalQuotient Witness.uniqueFailureRow ≡ false
uniqueFirstWitnessFinalQuotientIsScheduleInvariant = refl

competingWitnessLaneDoesNotClaimCommutativity :
  Witness.commutativityClaimed Witness.competingFailureRow ≡ false
competingWitnessLaneDoesNotClaimCommutativity = refl

valuationMetricIsNotDerived :
  Vacuum.metricDerivationClaimed Vacuum.canonicalValuationMetricBoundary ≡ false
valuationMetricIsNotDerived = refl

EinsteinVacuumEquationIsNotDerived :
  Vacuum.EinsteinVacuumEquationDerived Vacuum.canonicalEinsteinVacuumCandidate ≡ false
EinsteinVacuumEquationIsNotDerived = refl

residueCurvatureSourceIsNotDerived :
  Vacuum.curvatureSourceEquationDerived Vacuum.canonicalResidueCurvatureSourceCandidate ≡ false
residueCurvatureSourceIsNotDerived = refl

quantumGRUnificationIsNotPromoted :
  Vacuum.quantumGRUnificationProved Vacuum.canonicalVacuumGeometryPromotionBoundary ≡ false
quantumGRUnificationIsNotPromoted = refl

theoryOfEverythingPromotionIsBlocked :
  Vacuum.theoryOfEverythingClaimPermitted Vacuum.canonicalVacuumGeometryPromotionBoundary ≡ false
theoryOfEverythingPromotionIsBlocked = refl

candidateBridgeIsRecorded :
  Vacuum.candidateBridgeRecorded Vacuum.canonicalVacuumGeometryPromotionBoundary ≡ true
candidateBridgeIsRecorded = refl
