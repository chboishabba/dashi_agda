module DASHI.Physics.Closure.KeyTermCorrespondenceIndexReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AtomExtendedCarrierFrameReceipt as AtomFrame
import DASHI.Physics.Closure.DashiCFDThetaRuntimeDiagnosticReceipt as ThetaRuntime
import DASHI.Physics.Closure.FullUnificationPublicationRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.Gate3NormDictionary as Gate3
import DASHI.Physics.Closure.HeckeCarrierVsCMSplittingReceipt as HeckeCM
import DASHI.Physics.Closure.ITIRPNFPressureUnificationSupportReceipt as ITIRPNF
import DASHI.Physics.Closure.LocalDocs369UnificationSupportReceipt as Local369
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as NSMargin
import DASHI.Physics.Closure.NSTailFluxIdentityAnalyticTargetReceipt as NSIdentity
import DASHI.Physics.Closure.P71HeckeMirrorSignLaneReceipt as P71Sign
import DASHI.Physics.Closure.PublishableFullUnificationStackReceipt as Stack
import DASHI.Physics.Closure.ScaleGraphBarrierTargetReceipt as Barrier
import DASHI.Physics.Closure.SiblingCodecFiningContinuousSupportReceipt as SiblingCodec
import DASHI.Physics.Closure.SSPSevenSevenOneFrameDecompositionReceipt as SSPFrame
import DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt as L0
import DASHI.Physics.Closure.UnifiedMarginInvariantReceipt as Unified
import DASHI.Physics.Closure.YMKPActivityRatioMarginReceipt as YMRho

------------------------------------------------------------------------
-- Key-term correspondence index.
--
-- This receipt is a routing table for Paper 0 and the downstream lane papers.
-- It consolidates the distributed vocabulary into one fail-closed dictionary:
-- every key term has an allowed use, a forbidden use, and a promotion boundary.
--
-- The index is not an analytic theorem.  It does not prove theta preservation,
-- actual YM rho, Gate 3 density, continuum transfer, or Clay closure.  Its job
-- is to keep the prose and receipt surfaces from reusing a support term as a
-- theorem-bearing term.

data KeyTermIndexStatus : Set where
  keyTermCorrespondenceIndexRecorded_failClosed :
    KeyTermIndexStatus

data KeyTerm : Set where
  strictMarginGrammarTerm :
    KeyTerm

  carryMarginTerm :
    KeyTerm

  scaleGraphBarrierTerm :
    KeyTerm

  thetaTerm :
    KeyTerm

  dangerShellTerm :
    KeyTerm

  rhoTerm :
    KeyTerm

  gate3Term :
    KeyTerm

  atomFrameTerm :
    KeyTerm

  phaseTerm :
    KeyTerm

  heckeVsCMTerm :
    KeyTerm

  p71SignLaneTerm :
    KeyTerm

  braidCarryTerm :
    KeyTerm

  support369Term :
    KeyTerm

  pnfPressureTerm :
    KeyTerm

  tetrationScaleTerm :
    KeyTerm

  codecFiningTerm :
    KeyTerm

canonicalKeyTerms : List KeyTerm
canonicalKeyTerms =
  strictMarginGrammarTerm
  ∷ carryMarginTerm
  ∷ scaleGraphBarrierTerm
  ∷ thetaTerm
  ∷ dangerShellTerm
  ∷ rhoTerm
  ∷ gate3Term
  ∷ atomFrameTerm
  ∷ phaseTerm
  ∷ heckeVsCMTerm
  ∷ p71SignLaneTerm
  ∷ braidCarryTerm
  ∷ support369Term
  ∷ pnfPressureTerm
  ∷ tetrationScaleTerm
  ∷ codecFiningTerm
  ∷ []

data AllowedUse : Set where
  paper0DomainIndependentMarginGrammar :
    AllowedUse

  absorberMinusPromotedActivityNotation :
    AllowedUse

  finishShapeTargetTheoremSurface :
    AllowedUse

  nsTailFluxSeamGauge :
    AllowedUse

  nsFiniteRuntimeDangerShellDiagnostic :
    AllowedUse

  ymKPActivityRatioSeamGauge :
    AllowedUse

  carrierContinuumTransferObligationName :
    AllowedUse

  finiteCutoffFrameDiagnostic :
    AllowedUse

  carrierPhaseBookkeeping :
    AllowedUse

  cmHeckePartitionBoundary :
    AllowedUse

  terminalSSPSignCarryReactionOrientation :
    AllowedUse

  carryAndBraidSupportAnalogy :
    AllowedUse

  supportGrammarForTernaryVoxelBookkeeping :
    AllowedUse

  typedResidualPressureSupport :
    AllowedUse

  scaleNotationOnly :
    AllowedUse

  codecResidualSupportEvidence :
    AllowedUse

canonicalAllowedUse : KeyTerm → AllowedUse
canonicalAllowedUse strictMarginGrammarTerm =
  paper0DomainIndependentMarginGrammar
canonicalAllowedUse carryMarginTerm =
  absorberMinusPromotedActivityNotation
canonicalAllowedUse scaleGraphBarrierTerm =
  finishShapeTargetTheoremSurface
canonicalAllowedUse thetaTerm =
  nsTailFluxSeamGauge
canonicalAllowedUse dangerShellTerm =
  nsFiniteRuntimeDangerShellDiagnostic
canonicalAllowedUse rhoTerm =
  ymKPActivityRatioSeamGauge
canonicalAllowedUse gate3Term =
  carrierContinuumTransferObligationName
canonicalAllowedUse atomFrameTerm =
  finiteCutoffFrameDiagnostic
canonicalAllowedUse phaseTerm =
  carrierPhaseBookkeeping
canonicalAllowedUse heckeVsCMTerm =
  cmHeckePartitionBoundary
canonicalAllowedUse p71SignLaneTerm =
  terminalSSPSignCarryReactionOrientation
canonicalAllowedUse braidCarryTerm =
  carryAndBraidSupportAnalogy
canonicalAllowedUse support369Term =
  supportGrammarForTernaryVoxelBookkeeping
canonicalAllowedUse pnfPressureTerm =
  typedResidualPressureSupport
canonicalAllowedUse tetrationScaleTerm =
  scaleNotationOnly
canonicalAllowedUse codecFiningTerm =
  codecResidualSupportEvidence

data ForbiddenUse : Set where
  noLaneSpecificEstimateFromL0Alone :
    ForbiddenUse

  noSignedMarginWithoutActualAbsorberAndProduction :
    ForbiddenUse

  noBarrierNameAsMaximumPrincipleProof :
    ForbiddenUse

  noObservedThetaAsTheorem :
    ForbiddenUse

  noDangerShellAsRegularityProof :
    ForbiddenUse

  noToyRhoAsKPMargin :
    ForbiddenUse

  noGate3NameAsDensityProof :
    ForbiddenUse

  noFiniteFrameAsContinuumFrame :
    ForbiddenUse

  noPhaseBookkeepingAsGaugeOrSobolevClosure :
    ForbiddenUse

  noHeckeSevenSevenOneAsCMSplitting :
    ForbiddenUse

  noP71SignLaneAsInertPrimeOrTimeTheorem :
    ForbiddenUse

  noAnalogyAsAnalyticEstimate :
    ForbiddenUse

  no369AsGate3OrNSTheorem :
    ForbiddenUse

  noPNFPressureAsNavierStokesPressure :
    ForbiddenUse

  noTetrationAsComplexityTheorem :
    ForbiddenUse

  noCodecSupportAsContinuumTheorem :
    ForbiddenUse

canonicalForbiddenUse : KeyTerm → ForbiddenUse
canonicalForbiddenUse strictMarginGrammarTerm =
  noLaneSpecificEstimateFromL0Alone
canonicalForbiddenUse carryMarginTerm =
  noSignedMarginWithoutActualAbsorberAndProduction
canonicalForbiddenUse scaleGraphBarrierTerm =
  noBarrierNameAsMaximumPrincipleProof
canonicalForbiddenUse thetaTerm =
  noObservedThetaAsTheorem
canonicalForbiddenUse dangerShellTerm =
  noDangerShellAsRegularityProof
canonicalForbiddenUse rhoTerm =
  noToyRhoAsKPMargin
canonicalForbiddenUse gate3Term =
  noGate3NameAsDensityProof
canonicalForbiddenUse atomFrameTerm =
  noFiniteFrameAsContinuumFrame
canonicalForbiddenUse phaseTerm =
  noPhaseBookkeepingAsGaugeOrSobolevClosure
canonicalForbiddenUse heckeVsCMTerm =
  noHeckeSevenSevenOneAsCMSplitting
canonicalForbiddenUse p71SignLaneTerm =
  noP71SignLaneAsInertPrimeOrTimeTheorem
canonicalForbiddenUse braidCarryTerm =
  noAnalogyAsAnalyticEstimate
canonicalForbiddenUse support369Term =
  no369AsGate3OrNSTheorem
canonicalForbiddenUse pnfPressureTerm =
  noPNFPressureAsNavierStokesPressure
canonicalForbiddenUse tetrationScaleTerm =
  noTetrationAsComplexityTheorem
canonicalForbiddenUse codecFiningTerm =
  noCodecSupportAsContinuumTheorem

data PromotionBoundary : Set where
  requiresLaneDynamicsBoundAndActualMargin :
    PromotionBoundary

  requiresActualAbsorberMinusProduction :
    PromotionBoundary

  requiresProjectionSimulationEdgeAccountingAndDomainEstimates :
    PromotionBoundary

  requiresThetaAnalyticProofAndPreservation :
    PromotionBoundary

  requiresIndependentContinuationProof :
    PromotionBoundary

  requiresActualWilsonPolymerActivityAndBalabanRG :
    PromotionBoundary

  requiresDensityMoscoNoPollutionMassShell :
    PromotionBoundary

  requiresCutoffBoundsPlusUniformLimitBridge :
    PromotionBoundary

  requiresGaugeAndArchimedeanTransfer :
    PromotionBoundary

  requiresCMAndHeckeReceiptsSeparated :
    PromotionBoundary

  requiresSignLaneUseWithoutTimeOrInertClaim :
    PromotionBoundary

  requiresIndependentAnalyticInvariant :
    PromotionBoundary

  requiresRuntimeOrAnalyticBridgeBeforeConsumption :
    PromotionBoundary

  requiresDomainMatchedPressureConsumer :
    PromotionBoundary

  requiresSeparateOrdinalOrComplexityTheorem :
    PromotionBoundary

  requiresFreshBenchmarkOrContinuumProof :
    PromotionBoundary

canonicalPromotionBoundary : KeyTerm → PromotionBoundary
canonicalPromotionBoundary strictMarginGrammarTerm =
  requiresLaneDynamicsBoundAndActualMargin
canonicalPromotionBoundary carryMarginTerm =
  requiresActualAbsorberMinusProduction
canonicalPromotionBoundary scaleGraphBarrierTerm =
  requiresProjectionSimulationEdgeAccountingAndDomainEstimates
canonicalPromotionBoundary thetaTerm =
  requiresThetaAnalyticProofAndPreservation
canonicalPromotionBoundary dangerShellTerm =
  requiresIndependentContinuationProof
canonicalPromotionBoundary rhoTerm =
  requiresActualWilsonPolymerActivityAndBalabanRG
canonicalPromotionBoundary gate3Term =
  requiresDensityMoscoNoPollutionMassShell
canonicalPromotionBoundary atomFrameTerm =
  requiresCutoffBoundsPlusUniformLimitBridge
canonicalPromotionBoundary phaseTerm =
  requiresGaugeAndArchimedeanTransfer
canonicalPromotionBoundary heckeVsCMTerm =
  requiresCMAndHeckeReceiptsSeparated
canonicalPromotionBoundary p71SignLaneTerm =
  requiresSignLaneUseWithoutTimeOrInertClaim
canonicalPromotionBoundary braidCarryTerm =
  requiresIndependentAnalyticInvariant
canonicalPromotionBoundary support369Term =
  requiresRuntimeOrAnalyticBridgeBeforeConsumption
canonicalPromotionBoundary pnfPressureTerm =
  requiresDomainMatchedPressureConsumer
canonicalPromotionBoundary tetrationScaleTerm =
  requiresSeparateOrdinalOrComplexityTheorem
canonicalPromotionBoundary codecFiningTerm =
  requiresFreshBenchmarkOrContinuumProof

record KeyTermCorrespondenceRow : Set where
  field
    term :
      KeyTerm

    allowedUse :
      AllowedUse

    allowedUseIsCanonical :
      allowedUse ≡ canonicalAllowedUse term

    forbiddenUse :
      ForbiddenUse

    forbiddenUseIsCanonical :
      forbiddenUse ≡ canonicalForbiddenUse term

    promotionBoundary :
      PromotionBoundary

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ canonicalPromotionBoundary term

open KeyTermCorrespondenceRow public

rowFor : KeyTerm → KeyTermCorrespondenceRow
rowFor term =
  record
    { term =
        term
    ; allowedUse =
        canonicalAllowedUse term
    ; allowedUseIsCanonical =
        refl
    ; forbiddenUse =
        canonicalForbiddenUse term
    ; forbiddenUseIsCanonical =
        refl
    ; promotionBoundary =
        canonicalPromotionBoundary term
    ; promotionBoundaryIsCanonical =
        refl
    }

canonicalKeyTermCorrespondenceRows : List KeyTermCorrespondenceRow
canonicalKeyTermCorrespondenceRows =
  rowFor strictMarginGrammarTerm
  ∷ rowFor carryMarginTerm
  ∷ rowFor scaleGraphBarrierTerm
  ∷ rowFor thetaTerm
  ∷ rowFor dangerShellTerm
  ∷ rowFor rhoTerm
  ∷ rowFor gate3Term
  ∷ rowFor atomFrameTerm
  ∷ rowFor phaseTerm
  ∷ rowFor heckeVsCMTerm
  ∷ rowFor p71SignLaneTerm
  ∷ rowFor braidCarryTerm
  ∷ rowFor support369Term
  ∷ rowFor pnfPressureTerm
  ∷ rowFor tetrationScaleTerm
  ∷ rowFor codecFiningTerm
  ∷ []

data KeyTermIndexPromotion : Set where

keyTermIndexPromotionImpossibleHere :
  KeyTermIndexPromotion →
  ⊥
keyTermIndexPromotionImpossibleHere ()

indexStatement : String
indexStatement =
  "Key terms are routing surfaces: each has an allowed use, forbidden use, and promotion boundary. The index does not inhabit NS, YM, Gate3, continuum, or Clay obligations."

paper0UseStatement : String
paper0UseStatement =
  "Paper 0 may cite this index as terminology and promotion discipline for the shared margin grammar."

record KeyTermCorrespondenceIndexReceipt : Setω where
  field
    status :
      KeyTermIndexStatus

    statusIsFailClosed :
      status ≡ keyTermCorrespondenceIndexRecorded_failClosed

    l0Receipt :
      L0.StrictMarginImpliesAbsorptionReceipt

    l0NoClay :
      L0.StrictMarginImpliesAbsorptionReceipt.clayPromotion l0Receipt ≡ false

    roadmapReceipt :
      Roadmap.FullUnificationPublicationRoadmapReceipt

    roadmapNoNSClay :
      Roadmap.FullUnificationPublicationRoadmapReceipt.nsClayPromoted roadmapReceipt
        ≡ false

    roadmapNoYMClay :
      Roadmap.FullUnificationPublicationRoadmapReceipt.ymClayPromoted roadmapReceipt
        ≡ false

    stackReceipt :
      Stack.PublishableFullUnificationStackReceipt

    stackNoClay :
      Stack.PublishableFullUnificationStackReceipt.clayPromotionClaimed stackReceipt
        ≡ false

    scaleGraphBarrierReceipt :
      Barrier.ScaleGraphBarrierTargetReceipt

    scaleGraphBarrierStillTarget :
      Barrier.comparisonPrincipleProvedHere scaleGraphBarrierReceipt
        ≡ false

    scaleGraphBarrierNoClay :
      Barrier.clayPromotion scaleGraphBarrierReceipt ≡ false

    unifiedReceipt :
      Unified.UnifiedMarginInvariantReceipt

    unifiedNoClay :
      Unified.UnifiedMarginInvariantReceipt.clayPromotionMade unifiedReceipt
        ≡ false

    nsMarginReceipt :
      NSMargin.NSTailFluxAbsorptionMarginReceipt

    nsMarginNoClay :
      NSMargin.NSTailFluxAbsorptionMarginReceipt.clayNavierStokesPromoted
        nsMarginReceipt
        ≡ false

    nsIdentityReceipt :
      NSIdentity.NSTailFluxIdentityAnalyticTargetReceipt
        0

    nsIdentityProofOpen :
      NSIdentity.lpIdentityProvedHere nsIdentityReceipt ≡ false

    thetaRuntimeReceipt :
      ThetaRuntime.DashiCFDThetaRuntimeDiagnosticReceipt

    thetaRuntimeNoClay :
      ThetaRuntime.clayNavierStokesPromoted thetaRuntimeReceipt ≡ false

    ymRhoReceipt :
      YMRho.YMKPActivityRatioMarginReceipt

    ymToyRhoNotProof :
      YMRho.toyRhoProfilePromotedAsProof ymRhoReceipt ≡ false

    ymNoClay :
      YMRho.clayYangMillsPromoted ymRhoReceipt ≡ false

    gate3Receipt :
      Gate3.Gate3NormDictionaryReceipt

    gate3NoAnalyticProof :
      Gate3.Gate3NormDictionaryReceipt.analyticProofPromoted gate3Receipt
        ≡ false

    gate3NoClay :
      Gate3.Gate3NormDictionaryReceipt.clayPromotion gate3Receipt ≡ false

    atomFrameReceipt :
      AtomFrame.AtomExtendedCarrierFrameReceipt

    atomFrameNoGate3 :
      AtomFrame.gate3NormComparisonProved atomFrameReceipt ≡ false

    heckeCarrierVsCMReceipt :
      HeckeCM.HeckeCarrierVsCMSplittingReceipt

    heckeCarrierVsCMNotSamePartition :
      HeckeCM.notSamePartitionFlag heckeCarrierVsCMReceipt ≡ true

    heckeCarrierVsCMNoClay :
      HeckeCM.clayPromoted heckeCarrierVsCMReceipt ≡ false

    p71SignLaneReceipt :
      P71Sign.P71HeckeMirrorSignLaneReceipt

    p71SignLaneNotInert :
      P71Sign.p71IsNotInertInQsqrtMinus7 p71SignLaneReceipt ≡ true

    p71SignLaneNoTimeTheorem :
      P71Sign.p71TimeTheoremRejected p71SignLaneReceipt ≡ true

    p71SignLaneNoClay :
      P71Sign.clayPromoted p71SignLaneReceipt ≡ false

    sspFrameReceipt :
      SSPFrame.SSPSevenSevenOneFrameDecompositionReceipt

    sspFrameUniformBoundOpen :
      SSPFrame.uniformLowerBoundProved sspFrameReceipt ≡ false

    sspFrameNoClay :
      SSPFrame.clayPromotion sspFrameReceipt ≡ false

    itirPNFSupportReceipt :
      ITIRPNF.ITIRPNFPressureUnificationSupportReceipt

    itirPNFNoClay :
      ITIRPNF.clayPromotion itirPNFSupportReceipt ≡ false

    local369Receipt :
      Local369.LocalDocs369UnificationSupportReceipt

    local369NoClay :
      Local369.clayPromotion local369Receipt ≡ false

    siblingCodecReceipt :
      SiblingCodec.SiblingCodecFiningContinuousSupportReceipt

    siblingCodecNoClay :
      SiblingCodec.clayPromotion siblingCodecReceipt ≡ false

    terms :
      List KeyTerm

    termsAreCanonical :
      terms ≡ canonicalKeyTerms

    rows :
      List KeyTermCorrespondenceRow

    rowsAreCanonical :
      rows ≡ canonicalKeyTermCorrespondenceRows

    statement :
      String

    statementIsCanonical :
      statement ≡ indexStatement

    paper0Statement :
      String

    paper0StatementIsCanonical :
      paper0Statement ≡ paper0UseStatement

    nsRegularityPromoted :
      Bool

    nsRegularityPromotedIsFalse :
      nsRegularityPromoted ≡ false

    continuumYMPromoted :
      Bool

    continuumYMPromotedIsFalse :
      continuumYMPromoted ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    clayPromotionMade :
      Bool

    clayPromotionMadeIsFalse :
      clayPromotionMade ≡ false

    promotions :
      List KeyTermIndexPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      KeyTermIndexPromotion →
      ⊥

open KeyTermCorrespondenceIndexReceipt public

canonicalKeyTermCorrespondenceIndexReceipt :
  KeyTermCorrespondenceIndexReceipt
canonicalKeyTermCorrespondenceIndexReceipt =
  record
    { status =
        keyTermCorrespondenceIndexRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; l0Receipt =
        L0.canonicalStrictMarginImpliesAbsorptionReceipt
    ; l0NoClay =
        refl
    ; roadmapReceipt =
        Roadmap.canonicalFullUnificationPublicationRoadmapReceipt
    ; roadmapNoNSClay =
        refl
    ; roadmapNoYMClay =
        refl
    ; stackReceipt =
        Stack.canonicalPublishableFullUnificationStackReceipt
    ; stackNoClay =
        refl
    ; scaleGraphBarrierReceipt =
        Barrier.canonicalScaleGraphBarrierTargetReceipt
    ; scaleGraphBarrierStillTarget =
        refl
    ; scaleGraphBarrierNoClay =
        refl
    ; unifiedReceipt =
        Unified.canonicalUnifiedMarginInvariantReceipt
    ; unifiedNoClay =
        refl
    ; nsMarginReceipt =
        NSMargin.canonicalNSTailFluxAbsorptionMarginReceipt
    ; nsMarginNoClay =
        refl
    ; nsIdentityReceipt =
        NSIdentity.canonicalNSTailFluxIdentityAnalyticTargetReceipt
    ; nsIdentityProofOpen =
        refl
    ; thetaRuntimeReceipt =
        ThetaRuntime.canonicalDashiCFDThetaRuntimeDiagnosticReceipt
    ; thetaRuntimeNoClay =
        refl
    ; ymRhoReceipt =
        YMRho.canonicalYMKPActivityRatioMarginReceipt
    ; ymToyRhoNotProof =
        refl
    ; ymNoClay =
        refl
    ; gate3Receipt =
        Gate3.canonicalGate3NormDictionaryReceipt
    ; gate3NoAnalyticProof =
        refl
    ; gate3NoClay =
        refl
    ; atomFrameReceipt =
        AtomFrame.canonicalAtomExtendedCarrierFrameReceipt
    ; atomFrameNoGate3 =
        refl
    ; heckeCarrierVsCMReceipt =
        HeckeCM.canonicalHeckeCarrierVsCMSplittingReceipt
    ; heckeCarrierVsCMNotSamePartition =
        refl
    ; heckeCarrierVsCMNoClay =
        refl
    ; p71SignLaneReceipt =
        P71Sign.canonicalP71HeckeMirrorSignLaneReceipt
    ; p71SignLaneNotInert =
        refl
    ; p71SignLaneNoTimeTheorem =
        refl
    ; p71SignLaneNoClay =
        refl
    ; sspFrameReceipt =
        SSPFrame.canonicalSSPSevenSevenOneFrameDecompositionReceipt
    ; sspFrameUniformBoundOpen =
        refl
    ; sspFrameNoClay =
        refl
    ; itirPNFSupportReceipt =
        ITIRPNF.canonicalITIRPNFPressureUnificationSupportReceipt
    ; itirPNFNoClay =
        refl
    ; local369Receipt =
        Local369.canonicalLocalDocs369UnificationSupportReceipt
    ; local369NoClay =
        refl
    ; siblingCodecReceipt =
        SiblingCodec.canonicalSiblingCodecFiningContinuousSupportReceipt
    ; siblingCodecNoClay =
        refl
    ; terms =
        canonicalKeyTerms
    ; termsAreCanonical =
        refl
    ; rows =
        canonicalKeyTermCorrespondenceRows
    ; rowsAreCanonical =
        refl
    ; statement =
        indexStatement
    ; statementIsCanonical =
        refl
    ; paper0Statement =
        paper0UseStatement
    ; paper0StatementIsCanonical =
        refl
    ; nsRegularityPromoted =
        false
    ; nsRegularityPromotedIsFalse =
        refl
    ; continuumYMPromoted =
        false
    ; continuumYMPromotedIsFalse =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; clayPromotionMade =
        false
    ; clayPromotionMadeIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        keyTermIndexPromotionImpossibleHere
    }

canonicalIndexNoNSRegularity :
  nsRegularityPromoted canonicalKeyTermCorrespondenceIndexReceipt ≡ false
canonicalIndexNoNSRegularity =
  refl

canonicalIndexNoGate3Closure :
  gate3Closed canonicalKeyTermCorrespondenceIndexReceipt ≡ false
canonicalIndexNoGate3Closure =
  refl

canonicalIndexNoClayPromotion :
  clayPromotionMade canonicalKeyTermCorrespondenceIndexReceipt ≡ false
canonicalIndexNoClayPromotion =
  refl
