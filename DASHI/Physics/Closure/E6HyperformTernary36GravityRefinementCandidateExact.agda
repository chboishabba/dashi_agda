module DASHI.Physics.Closure.E6HyperformTernary36GravityRefinementCandidateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformPoissonLorentzMetricExact as Metric

------------------------------------------------------------------------
-- TERNARY-DEPTH-36 GRAVITY CALIBRATION CANDIDATE
--
-- The E6 programme already owns 36 projective root lines independently of the
-- clock comparison.  The simplest one-trit-per-line suppression ansatz is
--
--   epsilon_36 = 3^-36.
--
-- This owner records the exact local executable comparison against the same
-- hyperfabric metric and exact SI Cs/c candidate edge used by the previous
-- atomic-clock falsifier.  It is a candidate scaling law for held-out tests,
-- NOT a derivation of gravity and NOT evidence that the root-line count causes
-- the physical coupling.
------------------------------------------------------------------------

projectiveE6RootLineCount : Nat
projectiveE6RootLineCount = 36

candidateAmplitude : String
candidateAmplitude = "3^-36 = 6.6624633053756668558384673044918727e-18"

candidateAtomicEdgeMM : String
candidateAtomicEdgeMM = "c / Delta_nu_Cs = 32.61225571749405556794101848 mm"

selectedChartPhi : String
selectedChartPhi = "phi = -11/54"

selectedChartVerticalDerivative : String
selectedChartVerticalDerivative = "d_z phi = 5/9"

weakClockGradientFormula : String
weakClockGradientFormula = "|d_z log(1 + epsilon*phi)| / edge_mm"

candidatePredictedGradient : String
candidatePredictedGradient = "1.1349624310105516583564335626e-19 mm^-1"

theoryGradient : String
theoryGradient = "1.09e-19 mm^-1"

correctedPublishedGradient : String
correctedPublishedGradient = "0.98(23)e-19 mm^-1"

synchronousPublishedGradient : String
synchronousPublishedGradient = "1.28(27)e-19 mm^-1"

record Ternary36GravityCalibrationLocalReceipt : Set where
  constructor ternary36-gravity-calibration-local-receipt
  field
    preExistingE6RootLineCountUsed : Bool
    rootLineCount : Nat
    suppressionBaseThreeUsed : Bool
    candidateDepth : Nat
    weakFieldFormulaUsesSameExceptionalMetric : Bool
    exactSIDefiningConstantsUsed : Bool
    theoryRelativeErrorBelowFivePercent : Bool
    correctedMeasurementInsideOneSigma : Bool
    synchronousMeasurementInsideOneSigma : Bool
    neighboringDepth35Worse : Bool
    neighboringDepth37Worse : Bool
    entropyOrRefinementTheoremDerivesDepth36 : Bool
    physicalMechanismDerivesOneTritPerRootLine : Bool
    heldOutClockPredictionPaid : Bool
    causalGravityPromotionPaid : Bool
    boundary : String
open Ternary36GravityCalibrationLocalReceipt public

canonicalTernary36GravityCalibrationLocalReceipt : Ternary36GravityCalibrationLocalReceipt
canonicalTernary36GravityCalibrationLocalReceipt =
  ternary36-gravity-calibration-local-receipt
    true 36 true 36 true true
    true true true true true
    false false false false
    "The pre-existing E6 root-line count 36 plus the explicit ansatz epsilon=3^-36 predicts a clock gradient within 5% of the public GR prediction and within the quoted corrected/synchronous uncertainty bands on the selected chart. No repository theorem currently derives one suppression trit per root line, no entropy-density result creates curvature by itself, and the relation was noticed after inspecting clock data. It is therefore a candidate scaling law requiring preregistered held-out tests, not a gravity derivation."

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data NumericalNearMatchCreatesGravityMechanism : Set where
data RootLineCountCreatesRefinementExponent : Set where
data EntropyDensityCreatesSuppressionLaw : Set where

nearMatchDoesNotCreateMechanism : NumericalNearMatchCreatesGravityMechanism → {A : Set} → A
nearMatchDoesNotCreateMechanism ()

rootCountDoesNotCreateExponent : RootLineCountCreatesRefinementExponent → {A : Set} → A
rootCountDoesNotCreateExponent ()

entropyDoesNotCreateSuppression : EntropyDensityCreatesSuppressionLaw → {A : Set} → A
entropyDoesNotCreateSuppression ()
