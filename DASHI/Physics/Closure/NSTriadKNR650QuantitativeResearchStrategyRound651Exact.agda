{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650QuantitativeResearchStrategyRound651Exact where

------------------------------------------------------------------------
-- ROUND651 / R650 QUANTITATIVE RESEARCH STRATEGY + VISCOSITY-ONLY NO-GO
--
-- R650 leaves exactly two new NS analytic inequalities.  At this point the
-- useful implementation work is theorem-search, not further representation
-- splitting.
--
-- For C2, one tempting strengthening is to delete the literal R406 remainder
-- altogether and ask for a fixed positive retained margin from viscosity alone:
--
--   P_N' <= (2 nu - delta) D_N'.
--
-- R104/R43 already rule out manufacturing such a universal arbitrary-data
-- theorem from amplitude-independent constants: the nonlinear production is
-- cubic under common amplitude scaling, while viscous dissipation is quadratic.
--
-- Thus the actual R650 C2 proof MUST retain scale-changing information:
-- signed cancellation, the literal R406 remainder, trajectory/history control,
-- or another data-dependent mechanism.  This is not a no-go for R650 C2; it is
-- a no-go for the stronger remainder-free shortcut.
--
-- Companion finite-Galerkin telemetry:
--   scripts/ns_r650_quantitative_stress_scan.py
--
-- The script is diagnostic only and explicitly does not evaluate R406/C1 or
-- acquire theorem/Clay authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNHHBadAmplitudeHomogeneityRound43Exact as R43
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as R104

r650StressScanPath : String
r650StressScanPath = "scripts/ns_r650_quantitative_stress_scan.py"

r650StressScanCheckPath : String
r650StressScanCheckPath = "scripts/check_ns_r650_quantitative_stress_scan.py"

r406PhysicalRealEvalPath : String
r406PhysicalRealEvalPath = "scripts/ns_r406_physical_real_eval.py"

r650DirectC2PhysicalRealScanPath : String
r650DirectC2PhysicalRealScanPath = "scripts/ns_r650_c2_physical_real_scan.py"

r650DirectC1PhysicalRealScanPath : String
r650DirectC1PhysicalRealScanPath = "scripts/ns_r650_c1_physical_real_scan.py"

r406R650PhysicalRealCheckPath : String
r406R650PhysicalRealCheckPath = "scripts/check_ns_r406_r650_physical_real.py"

round651CriticalProductionCubicScalingAvailable : Bool
round651CriticalProductionCubicScalingAvailable =
  R43.literalProductionAmplitudeDegree

round651ViscousDissipationQuadraticScalingAvailable : Bool
round651ViscousDissipationQuadraticScalingAvailable =
  R43.viscousChargeAmplitudeDegree

round651R104AlreadyRejectsRemainderFreeFixedCoefficientShortcut : Bool
round651R104AlreadyRejectsRemainderFreeFixedCoefficientShortcut =
  R104.round104LiteralProductionCubicViscosityQuadraticReused

-- The stronger universal strategy
--
--   critical production <= fixed sub-viscous coefficient * dissipation
--
-- with no R406/history/data-dependent term is not the surviving arbitrary-data
-- route after the exact amplitude audit.
round651UniversalViscosityOnlyC2ShortcutAdmissible : Bool
round651UniversalViscosityOnlyC2ShortcutAdmissible = false

round651ActualR650C2RefutedByScalingAudit : Bool
round651ActualR650C2RefutedByScalingAudit = false

round651ActualC2MustRetainScaleChangingMechanism : Bool
round651ActualC2MustRetainScaleChangingMechanism = true

round651LiteralR406RemainsCanonicalScaleChangingConsumer : Bool
round651LiteralR406RemainsCanonicalScaleChangingConsumer = true

round651FiniteGalerkinStressHarnessInstalled : Bool
round651FiniteGalerkinStressHarnessInstalled = true

round651StressHarnessHasTheoremAuthority : Bool
round651StressHarnessHasTheoremAuthority = false

round651PhysicalRealR406DirectCompanionEvaluatorInstalled : Bool
round651PhysicalRealR406DirectCompanionEvaluatorInstalled = true

round651DirectPhysicalRealC2TrajectoryScanInstalled : Bool
round651DirectPhysicalRealC2TrajectoryScanInstalled = true

round651DirectPhysicalRealC1CutoffScanInstalled : Bool
round651DirectPhysicalRealC1CutoffScanInstalled = true

round651FormalRationalHelicalNumericalSameObjectInstalled : Bool
round651FormalRationalHelicalNumericalSameObjectInstalled = false

round651NumericalDirectC2ScanClosesFormalC2 : Bool
round651NumericalDirectC2ScanClosesFormalC2 = false

round651IntroducesNewNSEstimate : Bool
round651IntroducesNewNSEstimate = false

round651ClayPromotion : Bool
round651ClayPromotion = false

round651CriticalProductionCubicScalingAvailableIsTrue :
  round651CriticalProductionCubicScalingAvailable ≡ true
round651CriticalProductionCubicScalingAvailableIsTrue =
  R43.literalProductionAmplitudeDegreeIsTrue

round651ViscousDissipationQuadraticScalingAvailableIsTrue :
  round651ViscousDissipationQuadraticScalingAvailable ≡ true
round651ViscousDissipationQuadraticScalingAvailableIsTrue =
  R43.viscousChargeAmplitudeDegreeIsTrue

round651R104AlreadyRejectsRemainderFreeFixedCoefficientShortcutIsTrue :
  round651R104AlreadyRejectsRemainderFreeFixedCoefficientShortcut ≡ true
round651R104AlreadyRejectsRemainderFreeFixedCoefficientShortcutIsTrue =
  R43.literalProductionAmplitudeDegreeIsTrue

round651UniversalViscosityOnlyC2ShortcutAdmissibleIsFalse :
  round651UniversalViscosityOnlyC2ShortcutAdmissible ≡ false
round651UniversalViscosityOnlyC2ShortcutAdmissibleIsFalse = refl

round651ActualR650C2RefutedByScalingAuditIsFalse :
  round651ActualR650C2RefutedByScalingAudit ≡ false
round651ActualR650C2RefutedByScalingAuditIsFalse = refl

round651ActualC2MustRetainScaleChangingMechanismIsTrue :
  round651ActualC2MustRetainScaleChangingMechanism ≡ true
round651ActualC2MustRetainScaleChangingMechanismIsTrue = refl

round651LiteralR406RemainsCanonicalScaleChangingConsumerIsTrue :
  round651LiteralR406RemainsCanonicalScaleChangingConsumer ≡ true
round651LiteralR406RemainsCanonicalScaleChangingConsumerIsTrue = refl

round651FiniteGalerkinStressHarnessInstalledIsTrue :
  round651FiniteGalerkinStressHarnessInstalled ≡ true
round651FiniteGalerkinStressHarnessInstalledIsTrue = refl

round651StressHarnessHasTheoremAuthorityIsFalse :
  round651StressHarnessHasTheoremAuthority ≡ false
round651StressHarnessHasTheoremAuthorityIsFalse = refl

round651PhysicalRealR406DirectCompanionEvaluatorInstalledIsTrue :
  round651PhysicalRealR406DirectCompanionEvaluatorInstalled ≡ true
round651PhysicalRealR406DirectCompanionEvaluatorInstalledIsTrue = refl

round651DirectPhysicalRealC2TrajectoryScanInstalledIsTrue :
  round651DirectPhysicalRealC2TrajectoryScanInstalled ≡ true
round651DirectPhysicalRealC2TrajectoryScanInstalledIsTrue = refl

round651DirectPhysicalRealC1CutoffScanInstalledIsTrue :
  round651DirectPhysicalRealC1CutoffScanInstalled ≡ true
round651DirectPhysicalRealC1CutoffScanInstalledIsTrue = refl

round651FormalRationalHelicalNumericalSameObjectInstalledIsFalse :
  round651FormalRationalHelicalNumericalSameObjectInstalled ≡ false
round651FormalRationalHelicalNumericalSameObjectInstalledIsFalse = refl

round651NumericalDirectC2ScanClosesFormalC2IsFalse :
  round651NumericalDirectC2ScanClosesFormalC2 ≡ false
round651NumericalDirectC2ScanClosesFormalC2IsFalse = refl

round651IntroducesNewNSEstimateIsFalse :
  round651IntroducesNewNSEstimate ≡ false
round651IntroducesNewNSEstimateIsFalse = refl

round651ClayPromotionIsFalse :
  round651ClayPromotion ≡ false
round651ClayPromotionIsFalse = refl
