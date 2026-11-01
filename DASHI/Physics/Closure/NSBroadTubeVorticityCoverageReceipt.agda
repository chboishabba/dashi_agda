module DASHI.Physics.Closure.NSBroadTubeVorticityCoverageReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Broad-tube vorticity coverage socket receipt.
--
-- This file records a conditional broad-tube vorticity coverage socket.
-- The strict carrier lane is recorded as insufficient, the broad-tube
-- requirement is active, and the route is split into interior and exterior
-- lambda2 lanes.  Clay promotion remains false and no unconditional
-- coverage theorem is claimed.

data NSBroadTubeVorticityCoverageStatus : Set where
  broadTubeVorticityCoverageSocketRecorded :
    NSBroadTubeVorticityCoverageStatus

data NSBroadTubeVorticityCoverageDependency : Set where
  layerL2FractionTelemetry :
    NSBroadTubeVorticityCoverageDependency

  weightedLambda2QuantileTelemetry :
    NSBroadTubeVorticityCoverageDependency

  broadLayerFractionTelemetry :
    NSBroadTubeVorticityCoverageDependency

  broadTubeMassLowerBound :
    NSBroadTubeVorticityCoverageDependency

  coareaOmegaGradLambda2Telemetry :
    NSBroadTubeVorticityCoverageDependency

  broadTubeLambda2SplitTelemetry :
    NSBroadTubeVorticityCoverageDependency

  deepInteriorControl :
    NSBroadTubeVorticityCoverageDependency

  exteriorPressureCZL3Telemetry :
    NSBroadTubeVorticityCoverageDependency

  l3EnstrophyConditionalTelemetry :
    NSBroadTubeVorticityCoverageDependency

  conditionalL2GlobalBoundTelemetry :
    NSBroadTubeVorticityCoverageDependency

  coareaPartition :
    NSBroadTubeVorticityCoverageDependency

data NSBroadTubeVorticityCoverageKernelWitness : Set where
  deepInteriorControlWitness :
    NSBroadTubeVorticityCoverageKernelWitness

  broadLayerFractionWitness :
    NSBroadTubeVorticityCoverageKernelWitness

  coareaPartitionWitness :
    NSBroadTubeVorticityCoverageKernelWitness

  coareaOmegaGradLambda2Witness :
    NSBroadTubeVorticityCoverageKernelWitness

  broadTubeLambda2SplitWitness :
    NSBroadTubeVorticityCoverageKernelWitness

  deepInteriorGronwallWitness :
    NSBroadTubeVorticityCoverageKernelWitness

  exteriorPressureCZL3Witness :
    NSBroadTubeVorticityCoverageKernelWitness

  l3EnstrophyConditionalityWitness :
    NSBroadTubeVorticityCoverageKernelWitness

  conditionalL2BoundWitness :
    NSBroadTubeVorticityCoverageKernelWitness

  coverageKernelSpecificityWitness :
    NSBroadTubeVorticityCoverageKernelWitness

canonicalNSBroadTubeVorticityCoverageDependencies :
  List NSBroadTubeVorticityCoverageDependency
canonicalNSBroadTubeVorticityCoverageDependencies =
  layerL2FractionTelemetry
  ∷ weightedLambda2QuantileTelemetry
  ∷ broadLayerFractionTelemetry
  ∷ broadTubeMassLowerBound
  ∷ coareaOmegaGradLambda2Telemetry
  ∷ broadTubeLambda2SplitTelemetry
  ∷ deepInteriorControl
  ∷ exteriorPressureCZL3Telemetry
  ∷ l3EnstrophyConditionalTelemetry
  ∷ conditionalL2GlobalBoundTelemetry
  ∷ coareaPartition
  ∷ []

canonicalNSBroadTubeVorticityCoverageKernelWitnesses :
  List NSBroadTubeVorticityCoverageKernelWitness
canonicalNSBroadTubeVorticityCoverageKernelWitnesses =
  deepInteriorControlWitness
  ∷ broadLayerFractionWitness
  ∷ coareaPartitionWitness
  ∷ coareaOmegaGradLambda2Witness
  ∷ broadTubeLambda2SplitWitness
  ∷ deepInteriorGronwallWitness
  ∷ exteriorPressureCZL3Witness
  ∷ l3EnstrophyConditionalityWitness
  ∷ conditionalL2BoundWitness
  ∷ coverageKernelSpecificityWitness
  ∷ []

canonicalNSBroadTubeVorticityCoverageDependencyLabels :
  List String
canonicalNSBroadTubeVorticityCoverageDependencyLabels =
  "layerL2FractionTelemetry"
  ∷ "weightedLambda2QuantileTelemetry"
  ∷ "broadLayerFractionTelemetry"
  ∷ "broadTubeMassLowerBound"
  ∷ "coareaOmegaGradLambda2Telemetry"
  ∷ "broadTubeLambda2SplitTelemetry"
  ∷ "deepInteriorControl"
  ∷ "exteriorPressureCZL3Telemetry"
  ∷ "l3EnstrophyConditionalTelemetry"
  ∷ "conditionalL2GlobalBoundTelemetry"
  ∷ "coareaPartition"
  ∷ []

data NSBroadTubeVorticityCoverageHypothesis : Set where
  layerL2FractionTelemetryChecked :
    NSBroadTubeVorticityCoverageHypothesis

  weightedLambda2QuantileTelemetryChecked :
    NSBroadTubeVorticityCoverageHypothesis

  broadLayerFractionTelemetryChecked :
    NSBroadTubeVorticityCoverageHypothesis

  broadTubeMassLowerBoundChecked :
    NSBroadTubeVorticityCoverageHypothesis

  coareaOmegaGradLambda2Checked :
    NSBroadTubeVorticityCoverageHypothesis

  broadTubeLambda2SplitChecked :
    NSBroadTubeVorticityCoverageHypothesis

  deepInteriorControlChecked :
    NSBroadTubeVorticityCoverageHypothesis

  deepInteriorGronwallChecked :
    NSBroadTubeVorticityCoverageHypothesis

  exteriorPressureCZL3Checked :
    NSBroadTubeVorticityCoverageHypothesis

  l3EnstrophyConditionalChecked :
    NSBroadTubeVorticityCoverageHypothesis

  conditionalL2GlobalBoundChecked :
    NSBroadTubeVorticityCoverageHypothesis

  coareaPartitionChecked :
    NSBroadTubeVorticityCoverageHypothesis

data NSBroadTubeVorticityCoverageBlocker : Set where
  strictCarrierLaneInsufficient :
    NSBroadTubeVorticityCoverageBlocker

  broadLayerFractionNotYetPinned :
    NSBroadTubeVorticityCoverageBlocker

  coareaPartitionNotYetKernelSpecific :
    NSBroadTubeVorticityCoverageBlocker

  deepInteriorControlNotYetDischarged :
    NSBroadTubeVorticityCoverageBlocker

  assumptionsNotYetDischarged :
    NSBroadTubeVorticityCoverageBlocker

  exteriorPressureCZL3RouteNotYetDischarged :
    NSBroadTubeVorticityCoverageBlocker

  l3EnstrophyConditionalityNotYetDischarged :
    NSBroadTubeVorticityCoverageBlocker

  unconditionalCoverageTheoremAbsent :
    NSBroadTubeVorticityCoverageBlocker

  clayPromotionForbidden :
    NSBroadTubeVorticityCoverageBlocker

canonicalNSBroadTubeVorticityCoverageHypotheses :
  List NSBroadTubeVorticityCoverageHypothesis
canonicalNSBroadTubeVorticityCoverageHypotheses =
  layerL2FractionTelemetryChecked
  ∷ weightedLambda2QuantileTelemetryChecked
  ∷ broadLayerFractionTelemetryChecked
  ∷ broadTubeMassLowerBoundChecked
  ∷ coareaOmegaGradLambda2Checked
  ∷ broadTubeLambda2SplitChecked
  ∷ deepInteriorControlChecked
  ∷ deepInteriorGronwallChecked
  ∷ exteriorPressureCZL3Checked
  ∷ l3EnstrophyConditionalChecked
  ∷ conditionalL2GlobalBoundChecked
  ∷ coareaPartitionChecked
  ∷ []

canonicalNSBroadTubeVorticityCoverageBlockers :
  List NSBroadTubeVorticityCoverageBlocker
canonicalNSBroadTubeVorticityCoverageBlockers =
  strictCarrierLaneInsufficient
  ∷ broadLayerFractionNotYetPinned
  ∷ coareaPartitionNotYetKernelSpecific
  ∷ deepInteriorControlNotYetDischarged
  ∷ assumptionsNotYetDischarged
  ∷ exteriorPressureCZL3RouteNotYetDischarged
  ∷ l3EnstrophyConditionalityNotYetDischarged
  ∷ unconditionalCoverageTheoremAbsent
  ∷ clayPromotionForbidden
  ∷ []

canonicalNSBroadTubeVorticityCoverageHypothesisLabels :
  List String
canonicalNSBroadTubeVorticityCoverageHypothesisLabels =
  "layerL2FractionTelemetry"
  ∷ "weightedLambda2QuantileTelemetry"
  ∷ "broadLayerFractionTelemetry"
  ∷ "broadTubeMassLowerBound"
  ∷ "coareaOmegaGradLambda2Checked"
  ∷ "broadTubeLambda2SplitChecked"
  ∷ "deepInteriorControlChecked"
  ∷ "deepInteriorGronwallChecked"
  ∷ "exteriorPressureCZL3Checked"
  ∷ "l3EnstrophyConditionalChecked"
  ∷ "conditionalL2GlobalBoundChecked"
  ∷ "coareaPartitionChecked"
  ∷ []

data NSBroadTubeVorticityCoverageStep : Set where
  recordLayerL2FractionTelemetry :
    NSBroadTubeVorticityCoverageStep

  recordWeightedLambda2QuantileTelemetry :
    NSBroadTubeVorticityCoverageStep

  recordBroadTubeMassLowerBound :
    NSBroadTubeVorticityCoverageStep

  recordCoareaOmegaGradLambda2 :
    NSBroadTubeVorticityCoverageStep

  recordBroadTubeLambda2Split :
    NSBroadTubeVorticityCoverageStep

  recordDeepInteriorControl :
    NSBroadTubeVorticityCoverageStep

  recordDeepInteriorGronwall :
    NSBroadTubeVorticityCoverageStep

  recordExteriorPressureCZL3Route :
    NSBroadTubeVorticityCoverageStep

  recordL3EnstrophyConditionality :
    NSBroadTubeVorticityCoverageStep

  recordConditionalL2GlobalBound :
    NSBroadTubeVorticityCoverageStep

  recordCoareaPartition :
    NSBroadTubeVorticityCoverageStep

  constructConditionalCoverageSocket :
    NSBroadTubeVorticityCoverageStep

  recordCoverageBlockers :
    NSBroadTubeVorticityCoverageStep

canonicalNSBroadTubeVorticityCoverageSteps :
  List NSBroadTubeVorticityCoverageStep
canonicalNSBroadTubeVorticityCoverageSteps =
  recordLayerL2FractionTelemetry
  ∷ recordWeightedLambda2QuantileTelemetry
  ∷ recordBroadTubeMassLowerBound
  ∷ recordCoareaOmegaGradLambda2
  ∷ recordBroadTubeLambda2Split
  ∷ recordDeepInteriorControl
  ∷ recordDeepInteriorGronwall
  ∷ recordExteriorPressureCZL3Route
  ∷ recordL3EnstrophyConditionality
  ∷ recordConditionalL2GlobalBound
  ∷ recordCoareaPartition
  ∷ constructConditionalCoverageSocket
  ∷ recordCoverageBlockers
  ∷ []

data NSBroadTubeVorticityCoverageConclusion : Set where
  vorticityCoverageSocketConstructed :
    NSBroadTubeVorticityCoverageConclusion

broadTubeVorticityCoverageSocket :
  List NSBroadTubeVorticityCoverageHypothesis →
  List NSBroadTubeVorticityCoverageStep →
  NSBroadTubeVorticityCoverageConclusion
broadTubeVorticityCoverageSocket _ _ =
  vorticityCoverageSocketConstructed

coareaOmegaGradLambda2Formula : String
coareaOmegaGradLambda2Formula =
  "coarea identity for int |omega|^2 * |grad lambda2| (level-set weighted form)"

broadTubeLambda2SplitFormula : String
broadTubeLambda2SplitFormula =
  "split domain as { |lambda2| < eps } union { |lambda2| >= eps }"

deepInteriorGronwallRouteFormula : String
deepInteriorGronwallRouteFormula =
  "on {lambda2 <= -eps}, use vorticity transport in eigenbasis + maximum-principle budget on |omega|^2 and absorbable pressure term with Gronwall"

exteriorPressureCZL3RouteFormula : String
exteriorPressureCZL3RouteFormula =
  "on {lambda2 >= eps}, route is conditional: pressure estimate + Calderon-Zygmund + |omega|_L3 bound / enstrophy route"

conditionalL2GlobalBoundFormula : String
conditionalL2GlobalBoundFormula =
  "||omega||_L2(R3)^2 <= ||omega||_L2(broad tube)^2 + C(E0, T), conditional on L3 and enstrophy."

canonicalNSBroadTubeVorticityCoverageKernelStatement : String
canonicalNSBroadTubeVorticityCoverageKernelStatement =
  "Kernel-specific broad-tube vorticity coverage remains conditional: coarea of |omega|^2 |grad lambda2|, split-lambda2 lane decomposition, deep-interior max-principle/Gronwall control, exterior pressure-CZ-L3 conditional control, and the final conditional L2 inequality are recorded, while strict carrier insufficiency and unpaid assumptions keep unconditional status and Clay closed."

data NSBroadTubeVorticityCoverageNoPromotion : Set where

nsBroadTubeVorticityCoverageNoPromotion :
  NSBroadTubeVorticityCoverageNoPromotion →
  ⊥
nsBroadTubeVorticityCoverageNoPromotion ()

nsBroadTubeVorticityCoverageStatement : String
nsBroadTubeVorticityCoverageStatement =
  "Conditional broad-tube vorticity coverage socket: coarea formula, broad-tube lambda2 split, deep interior λ2<=-eps max-principle/Gronwall route, exterior λ2>=eps pressure/CZ/L3 conditional route, and final conditional inequality are recorded with explicit blockers."

nsBroadTubeVorticityCoverageBoundary : String
nsBroadTubeVorticityCoverageBoundary =
  "strict carrier insufficiency is explicit; assumptions are not discharged; interior and exterior conditional routes are active; final L2 inequality remains conditional on L3/enstrophy; no unconditional coverage theorem is claimed; Clay promotion stays false."

record NSBroadTubeVorticityCoverageORCSLPGF : Set where
  constructor mkNSBroadTubeVorticityCoverageORCSLPGF
  field
    O : String
    R : String
    C : String
    S : String
    L : String
    P : String
    G : String
    F : String

canonicalNSBroadTubeVorticityCoverageORCSLPGF :
  NSBroadTubeVorticityCoverageORCSLPGF
canonicalNSBroadTubeVorticityCoverageORCSLPGF =
  mkNSBroadTubeVorticityCoverageORCSLPGF
    "Record a conditional broad-tube vorticity coverage socket with explicit coarea and split-lane structure."
    "Use coareaOmegaGradLambda2Telemetry, broadTubeLambda2SplitTelemetry, deepInteriorGronwall, exteriorPressureCZL3Telemetry, L3/enstrophy conditional route, and conditional L2 bound telemetry."
    "The conclusion is the conditional socket vorticityCoverageSocketConstructed."
    "Record strict-carrier insufficiency and assumptionsNotYetDischarged alongside explicit blockers."
    "Link dependencies -> hypotheses -> step sequence with lane-split and route witnesses -> conditional socket construction."
    "No unconditional coverage theorem is established; the final estimate is conditional on explicit L3/enstrophy control."
    "Clay promotion is explicitly false; unconditionalCoverageTheorem remains false."
    "Keep the receipt fail-closed with canonical blockers and textual dependency witnesses."

record NSBroadTubeVorticityCoverageReceipt : Setω where
  field
    status :
      NSBroadTubeVorticityCoverageStatus

    statusIsCanonical :
      status ≡ broadTubeVorticityCoverageSocketRecorded

    dependencies :
      List NSBroadTubeVorticityCoverageDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalNSBroadTubeVorticityCoverageDependencies

    dependencyLabels :
      List String

    dependencyLabelsAreCanonical :
      dependencyLabels ≡ canonicalNSBroadTubeVorticityCoverageDependencyLabels

    hypotheses :
      List NSBroadTubeVorticityCoverageHypothesis

    hypothesesAreCanonical :
      hypotheses ≡ canonicalNSBroadTubeVorticityCoverageHypotheses

    hypothesisLabels :
      List String

    hypothesisLabelsAreCanonical :
      hypothesisLabels ≡ canonicalNSBroadTubeVorticityCoverageHypothesisLabels

    steps :
      List NSBroadTubeVorticityCoverageStep

    stepsAreCanonical :
      steps ≡ canonicalNSBroadTubeVorticityCoverageSteps

    coverageConclusion :
      NSBroadTubeVorticityCoverageConclusion

    coverageConclusionIsCanonical :
      coverageConclusion ≡
        broadTubeVorticityCoverageSocket hypotheses steps

    kernelWitnesses :
      List NSBroadTubeVorticityCoverageKernelWitness

    kernelWitnessesAreCanonical :
      kernelWitnesses
      ≡ canonicalNSBroadTubeVorticityCoverageKernelWitnesses

    coverageBlockers :
      List NSBroadTubeVorticityCoverageBlocker

    coverageBlockersAreCanonical :
      coverageBlockers ≡ canonicalNSBroadTubeVorticityCoverageBlockers

    strictCarrierInsufficient :
      Bool

    strictCarrierInsufficientIsTrue :
      strictCarrierInsufficient ≡ true

    broadTubeRequired :
      Bool

    broadTubeRequiredIsTrue :
      broadTubeRequired ≡ true

    broadLayerFractionTelemetryRecorded :
      Bool

    broadLayerFractionTelemetryRecordedIsTrue :
      broadLayerFractionTelemetryRecorded ≡ true

    coareaPartitionTelemetry :
      Bool

    coareaPartitionTelemetryIsTrue :
      coareaPartitionTelemetry ≡ true

    deepInteriorControlRecorded :
      Bool

    deepInteriorControlRecordedIsTrue :
      deepInteriorControlRecorded ≡ true

    assumptionsDischarged :
      Bool

    assumptionsDischargedIsFalse :
      assumptionsDischarged ≡ false

    coareaOmegaGradLambda2Recorded :
      Bool

    coareaOmegaGradLambda2RecordedIsTrue :
      coareaOmegaGradLambda2Recorded ≡ true

    broadTubeLambda2SplitRecorded :
      Bool

    broadTubeLambda2SplitRecordedIsTrue :
      broadTubeLambda2SplitRecorded ≡ true

    deepInteriorGronwallRecorded :
      Bool

    deepInteriorGronwallRecordedIsTrue :
      deepInteriorGronwallRecorded ≡ true

    exteriorPressureCZL3Recorded :
      Bool

    exteriorPressureCZL3RecordedIsTrue :
      exteriorPressureCZL3Recorded ≡ true

    l3EnstrophyConditionalityRecorded :
      Bool

    l3EnstrophyConditionalityRecordedIsTrue :
      l3EnstrophyConditionalityRecorded ≡ true

    conditionalL2GlobalBoundRecorded :
      Bool

    conditionalL2GlobalBoundRecordedIsTrue :
      conditionalL2GlobalBoundRecorded ≡ true

    coareaOmegaGradLambda2FormulaText :
      String

    coareaOmegaGradLambda2FormulaTextIsCanonical :
      coareaOmegaGradLambda2FormulaText ≡ coareaOmegaGradLambda2Formula

    broadTubeLambda2SplitFormulaText :
      String

    broadTubeLambda2SplitFormulaTextIsCanonical :
      broadTubeLambda2SplitFormulaText ≡ broadTubeLambda2SplitFormula

    deepInteriorGronwallFormulaText :
      String

    deepInteriorGronwallFormulaTextIsCanonical :
      deepInteriorGronwallFormulaText ≡ deepInteriorGronwallRouteFormula

    exteriorPressureCZL3FormulaText :
      String

    exteriorPressureCZL3FormulaTextIsCanonical :
      exteriorPressureCZL3FormulaText ≡ exteriorPressureCZL3RouteFormula

    conditionalL2GlobalBoundFormulaText :
      String

    conditionalL2GlobalBoundFormulaTextIsCanonical :
      conditionalL2GlobalBoundFormulaText ≡ conditionalL2GlobalBoundFormula

    assumptionDischargeBlocker :
      NSBroadTubeVorticityCoverageBlocker

    assumptionDischargeBlockerIsCanonical :
      assumptionDischargeBlocker ≡ assumptionsNotYetDischarged

    coverageSocketConstructed :
      Bool

    coverageSocketConstructedIsTrue :
      coverageSocketConstructed ≡ true

    unconditionalCoverageTheorem :
      Bool

    unconditionalCoverageTheoremIsFalse :
      unconditionalCoverageTheorem ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    coverageKernelSpecificity :
      String

    coverageKernelSpecificityIsCanonical :
      coverageKernelSpecificity
      ≡ canonicalNSBroadTubeVorticityCoverageKernelStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBroadTubeVorticityCoverageStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsBroadTubeVorticityCoverageBoundary

    promotionFlags :
      List NSBroadTubeVorticityCoverageNoPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSBroadTubeVorticityCoverageORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSBroadTubeVorticityCoverageORCSLPGF

open NSBroadTubeVorticityCoverageReceipt public
open NSBroadTubeVorticityCoverageORCSLPGF public

canonicalNSBroadTubeVorticityCoverageReceipt :
  NSBroadTubeVorticityCoverageReceipt
canonicalNSBroadTubeVorticityCoverageReceipt =
  record
    { status =
        broadTubeVorticityCoverageSocketRecorded
    ; statusIsCanonical =
        refl
    ; dependencies =
        canonicalNSBroadTubeVorticityCoverageDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyLabels =
        canonicalNSBroadTubeVorticityCoverageDependencyLabels
    ; dependencyLabelsAreCanonical =
        refl
    ; hypotheses =
        canonicalNSBroadTubeVorticityCoverageHypotheses
    ; hypothesesAreCanonical =
        refl
    ; hypothesisLabels =
        canonicalNSBroadTubeVorticityCoverageHypothesisLabels
    ; hypothesisLabelsAreCanonical =
        refl
    ; steps =
        canonicalNSBroadTubeVorticityCoverageSteps
    ; stepsAreCanonical =
        refl
    ; coverageConclusion =
        broadTubeVorticityCoverageSocket
          canonicalNSBroadTubeVorticityCoverageHypotheses
          canonicalNSBroadTubeVorticityCoverageSteps
    ; coverageConclusionIsCanonical =
        refl
    ; kernelWitnesses =
        canonicalNSBroadTubeVorticityCoverageKernelWitnesses
    ; kernelWitnessesAreCanonical =
        refl
    ; coverageBlockers =
        canonicalNSBroadTubeVorticityCoverageBlockers
    ; coverageBlockersAreCanonical =
        refl
    ; strictCarrierInsufficient =
        true
    ; strictCarrierInsufficientIsTrue =
        refl
    ; broadTubeRequired =
        true
    ; broadTubeRequiredIsTrue =
        refl
    ; broadLayerFractionTelemetryRecorded =
        true
    ; broadLayerFractionTelemetryRecordedIsTrue =
        refl
    ; coareaPartitionTelemetry =
        true
    ; coareaPartitionTelemetryIsTrue =
        refl
    ; deepInteriorControlRecorded =
        true
    ; deepInteriorControlRecordedIsTrue =
        refl
    ; assumptionsDischarged =
        false
    ; assumptionsDischargedIsFalse =
        refl
    ; coareaOmegaGradLambda2Recorded =
        true
    ; coareaOmegaGradLambda2RecordedIsTrue =
        refl
    ; broadTubeLambda2SplitRecorded =
        true
    ; broadTubeLambda2SplitRecordedIsTrue =
        refl
    ; deepInteriorGronwallRecorded =
        true
    ; deepInteriorGronwallRecordedIsTrue =
        refl
    ; exteriorPressureCZL3Recorded =
        true
    ; exteriorPressureCZL3RecordedIsTrue =
        refl
    ; l3EnstrophyConditionalityRecorded =
        true
    ; l3EnstrophyConditionalityRecordedIsTrue =
        refl
    ; conditionalL2GlobalBoundRecorded =
        true
    ; conditionalL2GlobalBoundRecordedIsTrue =
        refl
    ; coareaOmegaGradLambda2FormulaText =
        coareaOmegaGradLambda2Formula
    ; coareaOmegaGradLambda2FormulaTextIsCanonical =
        refl
    ; broadTubeLambda2SplitFormulaText =
        broadTubeLambda2SplitFormula
    ; broadTubeLambda2SplitFormulaTextIsCanonical =
        refl
    ; deepInteriorGronwallFormulaText =
        deepInteriorGronwallRouteFormula
    ; deepInteriorGronwallFormulaTextIsCanonical =
        refl
    ; exteriorPressureCZL3FormulaText =
        exteriorPressureCZL3RouteFormula
    ; exteriorPressureCZL3FormulaTextIsCanonical =
        refl
    ; conditionalL2GlobalBoundFormulaText =
        conditionalL2GlobalBoundFormula
    ; conditionalL2GlobalBoundFormulaTextIsCanonical =
        refl
    ; assumptionDischargeBlocker =
        assumptionsNotYetDischarged
    ; assumptionDischargeBlockerIsCanonical =
        refl
    ; coverageSocketConstructed =
        true
    ; coverageSocketConstructedIsTrue =
        refl
    ; unconditionalCoverageTheorem =
        false
    ; unconditionalCoverageTheoremIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; coverageKernelSpecificity =
        canonicalNSBroadTubeVorticityCoverageKernelStatement
    ; coverageKernelSpecificityIsCanonical =
        refl
    ; statement =
        nsBroadTubeVorticityCoverageStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        nsBroadTubeVorticityCoverageBoundary
    ; boundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; orcslpgf =
        canonicalNSBroadTubeVorticityCoverageORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    }
