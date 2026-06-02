module DASHI.Physics.Closure.ScaleGraphBarrierTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierMoscoConvergenceFromPhysicsReceipt
  as Gate3Mosco
import DASHI.Physics.Closure.DangerScaleEdgeConservationReceipt as Edge
import DASHI.Physics.Closure.DashiCFDThetaRuntimeDiagnosticReceipt
  as RuntimeTheta
import DASHI.Physics.Closure.FullUnificationPublicationRoadmapReceipt
  as Roadmap
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as NSMargin
import DASHI.Physics.Closure.NSTailFluxIdentityAnalyticTargetReceipt
  as NSIdentity
import DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt as L0
import DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt
  as YMActual
import DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt
  as YMRG
import DASHI.Physics.Closure.YMKPActivityRatioMarginReceipt as YMRho

------------------------------------------------------------------------
-- Scale graph barrier target receipt.
--
-- This receipt records the central theorem shape identified by the current
-- programme:
--
--   Theta(t) = sup_v q_v(t)
--
-- cannot cross 1 if the current danger node has strict absorption and all
-- edge transfer into that node is accounted for by a controlled leakage
-- term below the absorber slope.
--
-- The receipt is a target and a join surface.  It consumes the existing L0
-- margin grammar, fixed-K NS theta surface, YM rho/KP frontier, and Gate 3
-- Mosco boundary.  It does not prove the comparison principle, does not
-- supply the NS/YM/Gate3 analytic inhabitants, and does not promote Clay.

data ScaleGraphBarrierStatus : Set where
  scaleGraphBarrierTargetRecorded_failClosed :
    ScaleGraphBarrierStatus

data ScaleGraphQuantity : Set where
  nodeResidual :
    ScaleGraphQuantity

  nodeProduction :
    ScaleGraphQuantity

  nodeAbsorption :
    ScaleGraphQuantity

  nodeRatio :
    ScaleGraphQuantity

  thetaSupremum :
    ScaleGraphQuantity

  dangerNode :
    ScaleGraphQuantity

canonicalScaleGraphQuantities : List ScaleGraphQuantity
canonicalScaleGraphQuantities =
  nodeResidual
  ∷ nodeProduction
  ∷ nodeAbsorption
  ∷ nodeRatio
  ∷ thetaSupremum
  ∷ dangerNode
  ∷ []

data BarrierPremise : Set where
  nodeDynamicsBound :
    BarrierPremise

  actualNodeRatio :
    BarrierPremise

  positiveNodeAbsorption :
    BarrierPremise

  dangerNodeRealizesSupremum :
    BarrierPremise

  edgeTransferConservativeOrDissipative :
    BarrierPremise

  edgeLeakageBelowAbsorberSlope :
    BarrierPremise

  strictInitialThetaBelowOne :
    BarrierPremise

canonicalBarrierPremises : List BarrierPremise
canonicalBarrierPremises =
  nodeDynamicsBound
  ∷ actualNodeRatio
  ∷ positiveNodeAbsorption
  ∷ dangerNodeRealizesSupremum
  ∷ edgeTransferConservativeOrDissipative
  ∷ edgeLeakageBelowAbsorberSlope
  ∷ strictInitialThetaBelowOne
  ∷ []

data BarrierConclusionTarget : Set where
  thetaCannotCrossOne :
    BarrierConclusionTarget

  residualEnvelopeDecreasesAtDangerNode :
    BarrierConclusionTarget

  dangerScaleComparisonPrinciple :
    BarrierConclusionTarget

canonicalBarrierConclusionTargets : List BarrierConclusionTarget
canonicalBarrierConclusionTargets =
  thetaCannotCrossOne
  ∷ residualEnvelopeDecreasesAtDangerNode
  ∷ dangerScaleComparisonPrinciple
  ∷ []

data BarrierLane : Set where
  barrierLaneNS :
    BarrierLane

  barrierLaneYM :
    BarrierLane

  barrierLaneGate3 :
    BarrierLane

canonicalBarrierLanes : List BarrierLane
canonicalBarrierLanes =
  barrierLaneNS
  ∷ barrierLaneYM
  ∷ barrierLaneGate3
  ∷ []

data BarrierLaneDangerNode : Set where
  nsDangerShellArgmaxTheta :
    BarrierLaneDangerNode

  ymP7BottleneckRhoScale :
    BarrierLaneDangerNode

  gate3CutoffDefectLevel :
    BarrierLaneDangerNode

canonicalDangerNode : BarrierLane → BarrierLaneDangerNode
canonicalDangerNode barrierLaneNS =
  nsDangerShellArgmaxTheta
canonicalDangerNode barrierLaneYM =
  ymP7BottleneckRhoScale
canonicalDangerNode barrierLaneGate3 =
  gate3CutoffDefectLevel

data BarrierLaneHardObligation : Set where
  nsDangerShellFluxCannotOutrunViscosity :
    BarrierLaneHardObligation

  ymBalabanRGContractsActualRhoBelowOne :
    BarrierLaneHardObligation

  gate3MoscoRecoveryControlsProjectionDefect :
    BarrierLaneHardObligation

canonicalHardObligation : BarrierLane → BarrierLaneHardObligation
canonicalHardObligation barrierLaneNS =
  nsDangerShellFluxCannotOutrunViscosity
canonicalHardObligation barrierLaneYM =
  ymBalabanRGContractsActualRhoBelowOne
canonicalHardObligation barrierLaneGate3 =
  gate3MoscoRecoveryControlsProjectionDefect

record BarrierLaneRow : Set where
  field
    lane :
      BarrierLane

    danger :
      BarrierLaneDangerNode

    dangerIsCanonical :
      danger ≡ canonicalDangerNode lane

    obligation :
      BarrierLaneHardObligation

    obligationIsCanonical :
      obligation ≡ canonicalHardObligation lane

    obligationInhabited :
      Bool

    obligationInhabitedIsFalse :
      obligationInhabited ≡ false

open BarrierLaneRow public

rowFor : BarrierLane → BarrierLaneRow
rowFor lane =
  record
    { lane =
        lane
    ; danger =
        canonicalDangerNode lane
    ; dangerIsCanonical =
        refl
    ; obligation =
        canonicalHardObligation lane
    ; obligationIsCanonical =
        refl
    ; obligationInhabited =
        false
    ; obligationInhabitedIsFalse =
        refl
    }

canonicalBarrierLaneRows : List BarrierLaneRow
canonicalBarrierLaneRows =
  rowFor barrierLaneNS
  ∷ rowFor barrierLaneYM
  ∷ rowFor barrierLaneGate3
  ∷ []

data BarrierNonClaim : Set where
  noComparisonPrincipleProofHere :
    BarrierNonClaim

  noEdgeConservationProofHere :
    BarrierNonClaim

  noNSRegularityPromotion :
    BarrierNonClaim

  noYMMassGapPromotion :
    BarrierNonClaim

  noGate3ContinuumLiftPromotion :
    BarrierNonClaim

  noClayPromotion :
    BarrierNonClaim

canonicalBarrierNonClaims : List BarrierNonClaim
canonicalBarrierNonClaims =
  noComparisonPrincipleProofHere
  ∷ noEdgeConservationProofHere
  ∷ noNSRegularityPromotion
  ∷ noYMMassGapPromotion
  ∷ noGate3ContinuumLiftPromotion
  ∷ noClayPromotion
  ∷ []

data ScaleGraphBarrierPromotion : Set where

scaleGraphBarrierPromotionImpossibleHere :
  ScaleGraphBarrierPromotion →
  ⊥
scaleGraphBarrierPromotionImpossibleHere ()

barrierTargetStatement : String
barrierTargetStatement =
  "ScaleGraphBarrier target: if the danger-node ratio is the scale supremum, strict absorption holds there, and edge leakage is controlled below the absorber slope, then Theta cannot cross 1."

barrierBoundaryStatement : String
barrierBoundaryStatement =
  "The barrier is the central theorem shape, not an inhabited theorem here; NS, YM, and Gate3 must each supply their analytic danger-scale inequality."

record ScaleGraphBarrierTargetReceipt : Setω where
  field
    status :
      ScaleGraphBarrierStatus

    statusIsFailClosed :
      status ≡ scaleGraphBarrierTargetRecorded_failClosed

    l0Receipt :
      L0.StrictMarginImpliesAbsorptionReceipt

    l0NoClay :
      L0.StrictMarginImpliesAbsorptionReceipt.clayPromotion l0Receipt
      ≡
      false

    roadmapReceipt :
      Roadmap.FullUnificationPublicationRoadmapReceipt

    roadmapDownstreamNeedsAnalyticInhabitants :
      Roadmap.FullUnificationPublicationRoadmapReceipt.downstreamPapersNeedAnalyticInhabitants
        roadmapReceipt
      ≡
      true

    edgeReceipt :
      Edge.DangerScaleEdgeConservationReceipt

    edgeReceiptDoesNotProveEdgeLaw :
      Edge.edgeConservationProvedHere edgeReceipt ≡ false

    nsMarginReceipt :
      NSMargin.NSTailFluxAbsorptionMarginReceipt

    nsMarginConditional :
      NSMargin.NSTailFluxAbsorptionMarginReceipt.thetaTailAbsorptionConditionalFlag
        nsMarginReceipt
      ≡
      true

    nsIdentityReceipt :
      NSIdentity.NSTailFluxIdentityAnalyticTargetReceipt 0

    nsIdentityStillTarget :
      NSIdentity.lpIdentityProvedHere nsIdentityReceipt ≡ false

    runtimeThetaReceipt :
      RuntimeTheta.DashiCFDThetaRuntimeDiagnosticReceipt

    runtimeThetaNoClay :
      RuntimeTheta.clayNavierStokesPromoted runtimeThetaReceipt ≡ false

    ymRhoReceipt :
      YMRho.YMKPActivityRatioMarginReceipt

    ymToyRhoNotProof :
      YMRho.toyRhoProfilePromotedAsProof ymRhoReceipt ≡ false

    ymActualReceipt :
      YMActual.YMActualPolymerActivityDefinitionReceipt

    ymActualStillMissing :
      YMActual.actualPolymerActivitySupplied ymActualReceipt ≡ false

    ymRGReceipt :
      YMRG.YMBalabanRGScaleTransferFrontierReceipt

    ymRGStillMissing :
      YMRG.balabanRGProofPresent ymRGReceipt ≡ false

    gate3MoscoReceipt :
      Gate3Mosco.CarrierMoscoConvergenceFromPhysicsReceipt

    gate3StillRequiresFormalProof :
      Gate3Mosco.formalProofRequired gate3MoscoReceipt ≡ true

    quantities :
      List ScaleGraphQuantity

    quantitiesAreCanonical :
      quantities ≡ canonicalScaleGraphQuantities

    premises :
      List BarrierPremise

    premisesAreCanonical :
      premises ≡ canonicalBarrierPremises

    conclusionTargets :
      List BarrierConclusionTarget

    conclusionTargetsAreCanonical :
      conclusionTargets ≡ canonicalBarrierConclusionTargets

    lanes :
      List BarrierLane

    lanesAreCanonical :
      lanes ≡ canonicalBarrierLanes

    laneRows :
      List BarrierLaneRow

    laneRowsAreCanonical :
      laneRows ≡ canonicalBarrierLaneRows

    nonClaims :
      List BarrierNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalBarrierNonClaims

    comparisonPrincipleProvedHere :
      Bool

    comparisonPrincipleProvedHereIsFalse :
      comparisonPrincipleProvedHere ≡ false

    nsDangerInequalityProvedHere :
      Bool

    nsDangerInequalityProvedHereIsFalse :
      nsDangerInequalityProvedHere ≡ false

    ymBalabanRhoContractionProvedHere :
      Bool

    ymBalabanRhoContractionProvedHereIsFalse :
      ymBalabanRhoContractionProvedHere ≡ false

    gate3MoscoDefectControlProvedHere :
      Bool

    gate3MoscoDefectControlProvedHereIsFalse :
      gate3MoscoDefectControlProvedHere ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    targetStatement :
      String

    targetStatementIsCanonical :
      targetStatement ≡ barrierTargetStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ barrierBoundaryStatement

    promotions :
      List ScaleGraphBarrierPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ScaleGraphBarrierPromotion →
      ⊥

open ScaleGraphBarrierTargetReceipt public

canonicalScaleGraphBarrierTargetReceipt :
  ScaleGraphBarrierTargetReceipt
canonicalScaleGraphBarrierTargetReceipt =
  record
    { status =
        scaleGraphBarrierTargetRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; l0Receipt =
        L0.canonicalStrictMarginImpliesAbsorptionReceipt
    ; l0NoClay =
        refl
    ; roadmapReceipt =
        Roadmap.canonicalFullUnificationPublicationRoadmapReceipt
    ; roadmapDownstreamNeedsAnalyticInhabitants =
        refl
    ; edgeReceipt =
        Edge.canonicalDangerScaleEdgeConservationReceipt
    ; edgeReceiptDoesNotProveEdgeLaw =
        refl
    ; nsMarginReceipt =
        NSMargin.canonicalNSTailFluxAbsorptionMarginReceipt
    ; nsMarginConditional =
        refl
    ; nsIdentityReceipt =
        NSIdentity.canonicalNSTailFluxIdentityAnalyticTargetReceipt
    ; nsIdentityStillTarget =
        refl
    ; runtimeThetaReceipt =
        RuntimeTheta.canonicalDashiCFDThetaRuntimeDiagnosticReceipt
    ; runtimeThetaNoClay =
        refl
    ; ymRhoReceipt =
        YMRho.canonicalYMKPActivityRatioMarginReceipt
    ; ymToyRhoNotProof =
        refl
    ; ymActualReceipt =
        YMActual.canonicalYMActualPolymerActivityDefinitionReceipt
    ; ymActualStillMissing =
        refl
    ; ymRGReceipt =
        YMRG.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; ymRGStillMissing =
        refl
    ; gate3MoscoReceipt =
        Gate3Mosco.canonicalCarrierMoscoConvergenceFromPhysicsReceipt
    ; gate3StillRequiresFormalProof =
        refl
    ; quantities =
        canonicalScaleGraphQuantities
    ; quantitiesAreCanonical =
        refl
    ; premises =
        canonicalBarrierPremises
    ; premisesAreCanonical =
        refl
    ; conclusionTargets =
        canonicalBarrierConclusionTargets
    ; conclusionTargetsAreCanonical =
        refl
    ; lanes =
        canonicalBarrierLanes
    ; lanesAreCanonical =
        refl
    ; laneRows =
        canonicalBarrierLaneRows
    ; laneRowsAreCanonical =
        refl
    ; nonClaims =
        canonicalBarrierNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; comparisonPrincipleProvedHere =
        false
    ; comparisonPrincipleProvedHereIsFalse =
        refl
    ; nsDangerInequalityProvedHere =
        false
    ; nsDangerInequalityProvedHereIsFalse =
        refl
    ; ymBalabanRhoContractionProvedHere =
        false
    ; ymBalabanRhoContractionProvedHereIsFalse =
        refl
    ; gate3MoscoDefectControlProvedHere =
        false
    ; gate3MoscoDefectControlProvedHereIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; targetStatement =
        barrierTargetStatement
    ; targetStatementIsCanonical =
        refl
    ; boundaryStatement =
        barrierBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        scaleGraphBarrierPromotionImpossibleHere
    }

canonicalScaleGraphBarrierNotProved :
  comparisonPrincipleProvedHere canonicalScaleGraphBarrierTargetReceipt
    ≡ false
canonicalScaleGraphBarrierNotProved =
  refl

canonicalScaleGraphBarrierNoClay :
  clayPromotion canonicalScaleGraphBarrierTargetReceipt ≡ false
canonicalScaleGraphBarrierNoClay =
  refl
