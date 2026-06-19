module DASHI.Physics.Closure.NSGD1Q2ContradictionGateAuditReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.NSTheoremGQ2GD1ContradictionChannelReceipt as Channel
import DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt as ConditionalQ
import DASHI.Physics.Closure.NSGD1MinPrincipleNoLambda3CollapseReceipt as GD1
import DASHI.Physics.Closure.NSTheoremGCancellationUpgradeReceipt as Cancellation
import DASHI.Physics.Closure.NSLayerL2VorticityFractionReceipt as Layer
import DASHI.Physics.Closure.NSCollapseConditionalGronwallBridgeReceipt as Bridge
import DASHI.Physics.Closure.NSKatoHessianConfinementReceipt as Kato
import DASHI.Physics.Closure.NSBroadTubeVorticityCoverageReceipt as BroadTube
import DASHI.Physics.Closure.NSBroadTubeLayerFractionContinuityReceipt as LayerContinuity
import DASHI.Physics.Closure.NSQ2BlowupLowerImplicationReceipt as Lower
import DASHI.Physics.Closure.NSQ2UniformUpperBoundFromGD1TheoremGReceipt as Upper

------------------------------------------------------------------------
-- Composite NS contradiction-gate audit for the GD1/Q2/theorem-G route.
--
-- This receipt records the ordered contradiction channel as a fail-closed gate
-- audit surface. The ordered gate surface is:
--
-- 1. blowup assumption
-- 2. GD1 δ1
-- 3. biaxial cancellation
-- 4. TheoremG Q2 inequality
-- 5. finite-subinterval upper bound
-- 6. Miller/enstrophy lower route
-- 7. layer fraction
-- 8. coarea trace
-- 9. Q2 divergence
-- 10. contradiction
--
-- Clay promotion remains false.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSGD1Q2ContradictionGateAuditStatus : Set where
  gateAuditRecorded : NSGD1Q2ContradictionGateAuditStatus

data NSGD1Q2ContradictionGateAuditStep : Set where
  blowupAssumptionStep : NSGD1Q2ContradictionGateAuditStep
  gd1Delta1Step : NSGD1Q2ContradictionGateAuditStep
  biaxialCancellationStep : NSGD1Q2ContradictionGateAuditStep
  theoremGQ2InequalityStep : NSGD1Q2ContradictionGateAuditStep
  finiteSubintervalUpperBoundStep : NSGD1Q2ContradictionGateAuditStep
  millerEnstrophyLowerRouteStep : NSGD1Q2ContradictionGateAuditStep
  layerFractionStep : NSGD1Q2ContradictionGateAuditStep
  coareaTraceStep : NSGD1Q2ContradictionGateAuditStep
  q2DivergenceStep : NSGD1Q2ContradictionGateAuditStep
  contradictionStep : NSGD1Q2ContradictionGateAuditStep

canonicalNSGD1Q2ContradictionGateAuditSteps : List NSGD1Q2ContradictionGateAuditStep
canonicalNSGD1Q2ContradictionGateAuditSteps =
  blowupAssumptionStep
  ∷ gd1Delta1Step
  ∷ biaxialCancellationStep
  ∷ theoremGQ2InequalityStep
  ∷ finiteSubintervalUpperBoundStep
  ∷ millerEnstrophyLowerRouteStep
  ∷ layerFractionStep
  ∷ coareaTraceStep
  ∷ q2DivergenceStep
  ∷ contradictionStep
  ∷ []

stepName : NSGD1Q2ContradictionGateAuditStep → String
stepName blowupAssumptionStep = "blowup assumption"
stepName gd1Delta1Step = "GD1 δ1"
stepName biaxialCancellationStep = "biaxial cancellation"
stepName theoremGQ2InequalityStep = "TheoremG Q2 inequality"
stepName finiteSubintervalUpperBoundStep = "finite-subinterval upper bound"
stepName millerEnstrophyLowerRouteStep = "Miller/enstrophy lower route"
stepName layerFractionStep = "layer fraction"
stepName coareaTraceStep = "coarea trace"
stepName q2DivergenceStep = "Q2 divergence"
stepName contradictionStep = "contradiction"

canonicalNSGD1Q2ContradictionGateAuditStepNames : List String
canonicalNSGD1Q2ContradictionGateAuditStepNames =
  stepName blowupAssumptionStep
  ∷ stepName gd1Delta1Step
  ∷ stepName biaxialCancellationStep
  ∷ stepName theoremGQ2InequalityStep
  ∷ stepName finiteSubintervalUpperBoundStep
  ∷ stepName millerEnstrophyLowerRouteStep
  ∷ stepName layerFractionStep
  ∷ stepName coareaTraceStep
  ∷ stepName q2DivergenceStep
  ∷ stepName contradictionStep
  ∷ []

canonicalNSGD1Q2ContradictionGateAuditDependencyNames : List String
canonicalNSGD1Q2ContradictionGateAuditDependencyNames =
  "DASHI.Physics.Closure.NSTheoremGQ2GD1ContradictionChannelReceipt"
  ∷ "DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt"
  ∷ "DASHI.Physics.Closure.NSGD1MinPrincipleNoLambda3CollapseReceipt"
  ∷ "DASHI.Physics.Closure.NSTheoremGCancellationUpgradeReceipt"
  ∷ "DASHI.Physics.Closure.NSLayerL2VorticityFractionReceipt"
  ∷ "DASHI.Physics.Closure.NSCollapseConditionalGronwallBridgeReceipt"
  ∷ "DASHI.Physics.Closure.NSKatoHessianConfinementReceipt"
  ∷ "DASHI.Physics.Closure.NSBroadTubeVorticityCoverageReceipt"
  ∷ "DASHI.Physics.Closure.NSBroadTubeLayerFractionContinuityReceipt"
  ∷ "DASHI.Physics.Closure.NSQ2UniformUpperBoundFromGD1TheoremGReceipt"
  ∷ "DASHI.Physics.Closure.NSQ2BlowupLowerImplicationReceipt"
  ∷ []

auditContractText : List String
auditContractText =
  "This receipt encodes a composite contradiction gate audit surface for the GD1 / Q2 / Theorem-G chain."
  ∷ "The ordered steps are: finite-time blow-up assumption -> GD1 δ1 -> biaxial cancellation -> Theorem-G/Q2 inequality -> finite-subinterval upper bound -> Miller/enstrophy lower route -> layer fraction -> coarea trace -> Q2 divergence -> contradiction."
  ∷ "Each step is explicitly recorded, currently not discharged, and now linked to the fail-closed upper-bound, lower-implication, and layer-continuity module witnesses."
  ∷ "Clay Navier-Stokes promotion remains false."
  ∷ []

O-organization : String
O-organization =
  "Record the full contradiction gate route for GD1 + Theorem-G + Q2 as a gate-audit surface, not a promotion witness."

R-requirement : String
R-requirement =
  "Keep ordered-step gating explicit, retain existing module linkage, and mark unrepaired implication gaps as fail-closed."

C-artifact : String
C-artifact =
  "DASHI.Physics.Closure.NSGD1Q2ContradictionGateAuditReceipt"

S-state : String
S-state =
  "This surface records all route gates and does not discharge any of the ten contradiction-gate implications."

L-lattice : String
L-lattice =
  "ConditionalQ -> GD1 -> cancellation upgrade -> layer and coarea/trace -> divergence/cross-check -> contradiction assembly."

P-proposal : String
P-proposal =
  "Use this gate audit as a composite routing record until the finite-subinterval and Miller/enstrophy bridge modules are supplied."

G-governance : String
G-governance =
  "Governance is fail-closed: no Clay promotion and no contradiction closure in this receipt."

F-gap : String
F-gap =
  "Pending gaps are the actual analytic discharges inside the finite-subinterval upper bound, Miller/enstrophy lower-route, layer-continuity, and contradiction-closure gates."

record NSGD1Q2ContradictionGateAuditReceipt : Setω where
  field
    status : NSGD1Q2ContradictionGateAuditStatus
    statusIsCanonical : status ≡ gateAuditRecorded

    stepLedger : List NSGD1Q2ContradictionGateAuditStep
    stepLedgerIsCanonical : stepLedger ≡ canonicalNSGD1Q2ContradictionGateAuditSteps
    stepLedgerCount : Nat
    stepLedgerCountIsCanonical : stepLedgerCount ≡ listLength canonicalNSGD1Q2ContradictionGateAuditSteps

    stepNames : List String
    stepNamesIsCanonical : stepNames ≡ canonicalNSGD1Q2ContradictionGateAuditStepNames

    dependencyNames : List String
    dependencyNamesIsCanonical : dependencyNames ≡ canonicalNSGD1Q2ContradictionGateAuditDependencyNames
    dependencyNameCount : Nat
    dependencyNameCountIsCanonical :
      dependencyNameCount ≡ listLength canonicalNSGD1Q2ContradictionGateAuditDependencyNames

    channelReceipt : Channel.NSTheoremGQ2GD1ContradictionChannelReceipt
    conditionalQReceipt : ConditionalQ.NSConditionalQGronwallTheoremGReceipt
    gd1Receipt : GD1.NSGD1MinPrincipleNoLambda3CollapseReceipt
    cancellationReceipt : Cancellation.NSTheoremGCancellationUpgradeReceipt
    layerReceipt : Layer.NSLayerL2VorticityFractionReceipt
    bridgeReceipt : Bridge.NSCollapseConditionalGronwallBridgeReceipt
    millerReceipt : Kato.NSKatoHessianConfinementReceipt
    coareaReceipt : BroadTube.NSBroadTubeVorticityCoverageReceipt
    layerContinuityReceipt :
      LayerContinuity.NSBroadTubeLayerFractionContinuityReceipt
    upperBoundReceipt :
      Upper.NSQ2UniformUpperBoundFromGD1TheoremGReceipt
    lowerImplicationReceipt :
      Lower.NSQ2BlowupLowerImplicationReceipt

    blowupAssumptionGateRecorded : Bool
    blowupAssumptionGateRecordedIsTrue : blowupAssumptionGateRecorded ≡ true
    blowupAssumptionGateDischarged : Bool
    blowupAssumptionGateDischargedIsFalse : blowupAssumptionGateDischarged ≡ false
    blowupAssumptionDependsOnNewModule : Bool
    blowupAssumptionDependsOnNewModuleIsFalse :
      blowupAssumptionDependsOnNewModule ≡ false

    gd1Delta1GateRecorded : Bool
    gd1Delta1GateRecordedIsTrue : gd1Delta1GateRecorded ≡ true
    gd1Delta1GateDischarged : Bool
    gd1Delta1GateDischargedIsFalse : gd1Delta1GateDischarged ≡ false
    gd1Delta1DependsOnNewModule : Bool
    gd1Delta1DependsOnNewModuleIsFalse : gd1Delta1DependsOnNewModule ≡ false

    biaxialCancellationGateRecorded : Bool
    biaxialCancellationGateRecordedIsTrue : biaxialCancellationGateRecorded ≡ true
    biaxialCancellationGateDischarged : Bool
    biaxialCancellationGateDischargedIsFalse : biaxialCancellationGateDischarged ≡ false
    biaxialCancellationDependsOnNewModule : Bool
    biaxialCancellationDependsOnNewModuleIsFalse :
      biaxialCancellationDependsOnNewModule ≡ false

    theoremGQ2InequalityGateRecorded : Bool
    theoremGQ2InequalityGateRecordedIsTrue :
      theoremGQ2InequalityGateRecorded ≡ true
    theoremGQ2InequalityGateDischarged : Bool
    theoremGQ2InequalityGateDischargedIsFalse :
      theoremGQ2InequalityGateDischarged ≡ false
    theoremGQ2InequalityDependsOnNewModule : Bool
    theoremGQ2InequalityDependsOnNewModuleIsFalse :
      theoremGQ2InequalityDependsOnNewModule ≡ false

    finiteSubintervalUpperBoundGateRecorded : Bool
    finiteSubintervalUpperBoundGateRecordedIsTrue :
      finiteSubintervalUpperBoundGateRecorded ≡ true
    finiteSubintervalUpperBoundGateDischarged : Bool
    finiteSubintervalUpperBoundGateDischargedIsFalse :
      finiteSubintervalUpperBoundGateDischarged ≡ false
    finiteSubintervalUpperBoundDependsOnNewModule : Bool
    finiteSubintervalUpperBoundDependsOnNewModuleIsFalse :
      finiteSubintervalUpperBoundDependsOnNewModule ≡ false

    millerEnstrophyLowerRouteGateRecorded : Bool
    millerEnstrophyLowerRouteGateRecordedIsTrue :
      millerEnstrophyLowerRouteGateRecorded ≡ true
    millerEnstrophyLowerRouteGateDischarged : Bool
    millerEnstrophyLowerRouteGateDischargedIsFalse :
      millerEnstrophyLowerRouteGateDischarged ≡ false
    millerEnstrophyLowerRouteDependsOnNewModule : Bool
    millerEnstrophyLowerRouteDependsOnNewModuleIsFalse :
      millerEnstrophyLowerRouteDependsOnNewModule ≡ false

    layerFractionGateRecorded : Bool
    layerFractionGateRecordedIsTrue : layerFractionGateRecorded ≡ true
    layerFractionGateDischarged : Bool
    layerFractionGateDischargedIsFalse : layerFractionGateDischarged ≡ false
    layerFractionDependsOnNewModule : Bool
    layerFractionDependsOnNewModuleIsFalse : layerFractionDependsOnNewModule ≡ false

    coareaTraceGateRecorded : Bool
    coareaTraceGateRecordedIsTrue : coareaTraceGateRecorded ≡ true
    coareaTraceGateDischarged : Bool
    coareaTraceGateDischargedIsFalse : coareaTraceGateDischarged ≡ false
    coareaTraceDependsOnNewModule : Bool
    coareaTraceDependsOnNewModuleIsFalse : coareaTraceDependsOnNewModule ≡ false

    q2DivergenceGateRecorded : Bool
    q2DivergenceGateRecordedIsTrue : q2DivergenceGateRecorded ≡ true
    q2DivergenceGateDischarged : Bool
    q2DivergenceGateDischargedIsFalse : q2DivergenceGateDischarged ≡ false
    q2DivergenceDependsOnNewModule : Bool
    q2DivergenceDependsOnNewModuleIsFalse : q2DivergenceDependsOnNewModule ≡ false

    contradictionGateRecorded : Bool
    contradictionGateRecordedIsTrue : contradictionGateRecorded ≡ true
    contradictionGateDischarged : Bool
    contradictionGateDischargedIsFalse : contradictionGateDischarged ≡ false
    contradictionGateDependsOnNewModule : Bool
    contradictionGateDependsOnNewModuleIsFalse :
      contradictionGateDependsOnNewModule ≡ false

    clayNavierStokesPromoted : Bool
    clayNavierStokesPromotedIsFalse : clayNavierStokesPromoted ≡ false

    O-R-C-S-L-P-G-F-boundary :
      List String
    O-R-C-S-L-P-G-F-boundaryIsCanonical :
      O-R-C-S-L-P-G-F-boundary ≡
        auditContractText

    organization : String
    organizationIsCanonical : organization ≡ O-organization
    requirement : String
    requirementIsCanonical : requirement ≡ R-requirement
    artifact : String
    artifactIsCanonical : artifact ≡ C-artifact
    state : String
    stateIsCanonical : state ≡ S-state
    lattice : String
    latticeIsCanonical : lattice ≡ L-lattice
    proposal : String
    proposalIsCanonical : proposal ≡ P-proposal
    governance : String
    governanceIsCanonical : governance ≡ G-governance
    gap : String
    gapIsCanonical : gap ≡ F-gap

canonicalNSGD1Q2ContradictionGateAuditReceipt :
  NSGD1Q2ContradictionGateAuditReceipt
canonicalNSGD1Q2ContradictionGateAuditReceipt =
  record
    { status =
        gateAuditRecorded
    ; statusIsCanonical =
        refl
    ; stepLedger =
        canonicalNSGD1Q2ContradictionGateAuditSteps
    ; stepLedgerIsCanonical =
        refl
    ; stepLedgerCount =
        listLength canonicalNSGD1Q2ContradictionGateAuditSteps
    ; stepLedgerCountIsCanonical =
        refl
    ; stepNames =
        canonicalNSGD1Q2ContradictionGateAuditStepNames
    ; stepNamesIsCanonical =
        refl
    ; dependencyNames =
        canonicalNSGD1Q2ContradictionGateAuditDependencyNames
    ; dependencyNamesIsCanonical =
        refl
    ; dependencyNameCount =
        listLength canonicalNSGD1Q2ContradictionGateAuditDependencyNames
    ; dependencyNameCountIsCanonical =
        refl
    ; channelReceipt =
        Channel.canonicalNSTheoremGQ2GD1ContradictionChannelReceipt
    ; conditionalQReceipt =
        ConditionalQ.canonicalNSConditionalQGronwallTheoremGReceipt
    ; gd1Receipt =
        GD1.canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt
    ; cancellationReceipt =
        Cancellation.canonicalNSTheoremGCancellationUpgradeReceipt
    ; layerReceipt =
        Layer.canonicalNSLayerL2VorticityFractionReceipt
    ; bridgeReceipt =
        Bridge.canonicalNSCollapseConditionalGronwallBridgeReceipt
    ; millerReceipt =
        Kato.canonicalNSKatoHessianConfinementReceipt
    ; coareaReceipt =
        BroadTube.canonicalNSBroadTubeVorticityCoverageReceipt
    ; layerContinuityReceipt =
        LayerContinuity.canonicalNSBroadTubeLayerFractionContinuityReceipt
    ; upperBoundReceipt =
        Upper.canonicalNSQ2UniformUpperBoundFromGD1TheoremGReceipt
    ; lowerImplicationReceipt =
        Lower.canonicalNSQ2BlowupLowerImplicationReceipt
    ; blowupAssumptionGateRecorded =
        true
    ; blowupAssumptionGateRecordedIsTrue =
        refl
    ; blowupAssumptionGateDischarged =
        false
    ; blowupAssumptionGateDischargedIsFalse =
        refl
    ; blowupAssumptionDependsOnNewModule =
        false
    ; blowupAssumptionDependsOnNewModuleIsFalse =
        refl
    ; gd1Delta1GateRecorded =
        true
    ; gd1Delta1GateRecordedIsTrue =
        refl
    ; gd1Delta1GateDischarged =
        false
    ; gd1Delta1GateDischargedIsFalse =
        refl
    ; gd1Delta1DependsOnNewModule =
        false
    ; gd1Delta1DependsOnNewModuleIsFalse =
        refl
    ; biaxialCancellationGateRecorded =
        true
    ; biaxialCancellationGateRecordedIsTrue =
        refl
    ; biaxialCancellationGateDischarged =
        false
    ; biaxialCancellationGateDischargedIsFalse =
        refl
    ; biaxialCancellationDependsOnNewModule =
        false
    ; biaxialCancellationDependsOnNewModuleIsFalse =
        refl
    ; theoremGQ2InequalityGateRecorded =
        true
    ; theoremGQ2InequalityGateRecordedIsTrue =
        refl
    ; theoremGQ2InequalityGateDischarged =
        false
    ; theoremGQ2InequalityGateDischargedIsFalse =
        refl
    ; theoremGQ2InequalityDependsOnNewModule =
        false
    ; theoremGQ2InequalityDependsOnNewModuleIsFalse =
        refl
    ; finiteSubintervalUpperBoundGateRecorded =
        true
    ; finiteSubintervalUpperBoundGateRecordedIsTrue =
        refl
    ; finiteSubintervalUpperBoundGateDischarged =
        false
    ; finiteSubintervalUpperBoundGateDischargedIsFalse =
        refl
    ; finiteSubintervalUpperBoundDependsOnNewModule =
        false
    ; finiteSubintervalUpperBoundDependsOnNewModuleIsFalse =
        refl
    ; millerEnstrophyLowerRouteGateRecorded =
        true
    ; millerEnstrophyLowerRouteGateRecordedIsTrue =
        refl
    ; millerEnstrophyLowerRouteGateDischarged =
        false
    ; millerEnstrophyLowerRouteGateDischargedIsFalse =
        refl
    ; millerEnstrophyLowerRouteDependsOnNewModule =
        false
    ; millerEnstrophyLowerRouteDependsOnNewModuleIsFalse =
        refl
    ; layerFractionGateRecorded =
        true
    ; layerFractionGateRecordedIsTrue =
        refl
    ; layerFractionGateDischarged =
        false
    ; layerFractionGateDischargedIsFalse =
        refl
    ; layerFractionDependsOnNewModule =
        false
    ; layerFractionDependsOnNewModuleIsFalse =
        refl
    ; coareaTraceGateRecorded =
        true
    ; coareaTraceGateRecordedIsTrue =
        refl
    ; coareaTraceGateDischarged =
        false
    ; coareaTraceGateDischargedIsFalse =
        refl
    ; coareaTraceDependsOnNewModule =
        false
    ; coareaTraceDependsOnNewModuleIsFalse =
        refl
    ; q2DivergenceGateRecorded =
        true
    ; q2DivergenceGateRecordedIsTrue =
        refl
    ; q2DivergenceGateDischarged =
        false
    ; q2DivergenceGateDischargedIsFalse =
        refl
    ; q2DivergenceDependsOnNewModule =
        false
    ; q2DivergenceDependsOnNewModuleIsFalse =
        refl
    ; contradictionGateRecorded =
        true
    ; contradictionGateRecordedIsTrue =
        refl
    ; contradictionGateDischarged =
        false
    ; contradictionGateDischargedIsFalse =
        refl
    ; contradictionGateDependsOnNewModule =
        false
    ; contradictionGateDependsOnNewModuleIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; O-R-C-S-L-P-G-F-boundary =
        auditContractText
    ; O-R-C-S-L-P-G-F-boundaryIsCanonical =
        refl
    ; organization =
        O-organization
    ; organizationIsCanonical =
        refl
    ; requirement =
        R-requirement
    ; requirementIsCanonical =
        refl
    ; artifact =
        C-artifact
    ; artifactIsCanonical =
        refl
    ; state =
        S-state
    ; stateIsCanonical =
        refl
    ; lattice =
        L-lattice
    ; latticeIsCanonical =
        refl
    ; proposal =
        P-proposal
    ; proposalIsCanonical =
        refl
    ; governance =
        G-governance
    ; governanceIsCanonical =
        refl
    ; gap =
        F-gap
    ; gapIsCanonical =
        refl
    }

open NSGD1Q2ContradictionGateAuditReceipt public

-- Compact route gates.
blowupAssumptionGateRecordedTrue :
  blowupAssumptionGateRecorded
    canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
blowupAssumptionGateRecordedTrue =
  refl

gd1Delta1GateRecordedTrue :
  gd1Delta1GateRecorded canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
gd1Delta1GateRecordedTrue =
  refl

theoremGQ2InequalityGateRecordedTrue :
  theoremGQ2InequalityGateRecorded
    canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
theoremGQ2InequalityGateRecordedTrue =
  refl

finiteSubintervalUpperBoundGateRecordedTrue :
  finiteSubintervalUpperBoundGateRecorded
    canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
finiteSubintervalUpperBoundGateRecordedTrue =
  refl

millerEnstrophyLowerRouteGateRecordedTrue :
  millerEnstrophyLowerRouteGateRecorded
    canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
millerEnstrophyLowerRouteGateRecordedTrue =
  refl

layerFractionGateRecordedTrue :
  layerFractionGateRecorded canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
layerFractionGateRecordedTrue =
  refl

coareaTraceGateRecordedTrue :
  coareaTraceGateRecorded canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
coareaTraceGateRecordedTrue =
  refl

q2DivergenceGateRecordedTrue :
  q2DivergenceGateRecorded canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
q2DivergenceGateRecordedTrue =
  refl

contradictionGateRecordedTrue :
  contradictionGateRecorded
    canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ true
contradictionGateRecordedTrue =
  refl

routeNotDischarged :
  blowupAssumptionGateDischarged canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ false
routeNotDischarged =
  refl

clayNavierStokesPromotionStillFalse :
  clayNavierStokesPromoted canonicalNSGD1Q2ContradictionGateAuditReceipt ≡ false
clayNavierStokesPromotionStillFalse =
  refl
