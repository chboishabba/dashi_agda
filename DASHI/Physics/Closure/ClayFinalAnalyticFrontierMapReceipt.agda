module DASHI.Physics.Closure.ClayFinalAnalyticFrontierMapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierOS3ReflectionPositivityReceipt as OS3
import DASHI.Physics.Closure.BinaryTetralemmaMarginStateReceipt as TetMargin
import DASHI.Physics.Closure.ClayBlockerAsymmetryReceipt as Asymmetry
import DASHI.Physics.Closure.Gate3AtomSamplerPAWOTGQualityReceipt as GateSampler
import DASHI.Physics.Closure.Gate3MoscoConstructiveSequenceReceipt as GateMosco
import DASHI.Physics.Closure.Gate3NoSpectralPollutionConditionalProofReceipt
  as GateNoPollution
import DASHI.Physics.Closure.Gate3NestingTaperConditionReceipt
  as GateNesting
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt
  as GatePAWOTG
import DASHI.Physics.Closure.MonsterMoonshineSSPQuotientControlReceipt
  as Monster
import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt as NSDanger
import DASHI.Physics.Closure.NSHminus1Over2ObstructionReceipt as NSHminus
import DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt as NSNegative
import DASHI.Physics.Closure.NSNonCircularKStarDriftBoundTargetReceipt as NSKStar
import DASHI.Physics.Closure.NSTailRestrictedThetaDiagnosticReceipt as NSTail
import DASHI.Physics.Closure.ScaleGraphBarrierAlgebraProofReceipt as Algebra
import DASHI.Physics.Closure.UniversalScaleGraphBarrierTargetReceipt
  as Universal
import DASHI.Physics.Closure.WightmanReconstructionCandidateReceipt
  as Wightman
import DASHI.Physics.Closure.YMBalabanPhysicalBetaBridgeTargetReceipt
  as YMBeta
import DASHI.Physics.Closure.YMC0EntropyThresholdSensitivityReceipt as YMC0
import DASHI.Physics.Closure.YMMonsterQuotientEvidenceReceipt
  as YMMonsterEvidence
import DASHI.Physics.Closure.YMPhysicalBetaBridgeOpenReceipt as YMOpen

------------------------------------------------------------------------
-- Final analytic frontier map.
--
-- The shared algebra has now been separated from the analytic inhabitants.
-- `ScaleGraphBarrierAlgebraProofReceipt` records the solved algebraic
-- implication:
--
--   R' <= P + I - A
--   P  <= theta A
--   I  <= epsilon A
--   theta + epsilon < 1
--   A > 0
--   ------------------------
--   R' < 0
--
-- This receipt records the current frontier ranking after that algebra is
-- available. The intent is not to advertise many equally-live gaps across
-- every lane. Instead:
--
-- 1. NS is treated here as a candidate-complete internal package pending
--    promotion/acceptance review rather than as the active external-content
--    frontier.
-- 2. Unification/Gate3 is likewise treated as a candidate-complete package
--    pending promotion/acceptance review.
-- 3. YM remains the genuinely open external-content frontier if the program
--    insists on internal closure.
--
-- The receipt is still governance-only and fail-closed: it proves no PAWOTG
-- theorem, no Balaban bridge, no OS/Wightman continuum package, no NS danger
-- shell theorem, and no Clay result.

data ClayFinalAnalyticFrontierStatus : Set where
  clayFinalFrontierRecorded_failClosed :
    ClayFinalAnalyticFrontierStatus

data SolvedSharedComponent : Set where
  universalScaleGraphBarrierAlgebraClosed :
    SolvedSharedComponent

data UpstreamSharedFrontier : Set where
  monsterMultiplicityQuotientControl :
    UpstreamSharedFrontier

data Gate3FinalLemma : Set where
  pawotgUniformSeparation :
    Gate3FinalLemma

  uniformGaussianSpreadBelowP3Threshold :
    Gate3FinalLemma

  moscoNoPollutionMassShellBridge :
    Gate3FinalLemma

data YMFinalLemma : Set where
  actualAllDiameterKPBoundWithEffectiveC0 :
    YMFinalLemma

  balabanPhysicalBetaBridge :
    YMFinalLemma

  continuumOSWightmanMassGapBridge :
    YMFinalLemma

data NSFinalLemma : Set where
  tailRestrictedThetaBarrier :
    NSFinalLemma

  negativeSobolevHighHighDefectBound :
    NSFinalLemma

  nonCircularKStarDriftBound :
    NSFinalLemma

  dangerShellMaximumPrinciple :
    NSFinalLemma

data CandidateCompletePackage : Set where
  navierStokesCandidateCompletePendingAcceptance :
    CandidateCompletePackage

  unificationCandidateCompletePendingAcceptance :
    CandidateCompletePackage

data GenuineExternalContentFrontier : Set where
  yangMillsExternalContentFrontier :
    GenuineExternalContentFrontier

data FrontierRanking : Set where
  candidateCompletePendingPromotionAcceptance :
    FrontierRanking

  genuineExternalContentFrontierIfInternalClosureDemanded :
    FrontierRanking

canonicalCandidateCompletePackages :
  List CandidateCompletePackage
canonicalCandidateCompletePackages =
  navierStokesCandidateCompletePendingAcceptance
  ∷ unificationCandidateCompletePendingAcceptance
  ∷ []

canonicalGenuineExternalContentFrontiers :
  List GenuineExternalContentFrontier
canonicalGenuineExternalContentFrontiers =
  yangMillsExternalContentFrontier
  ∷ []

canonicalFrontierRanking :
  List FrontierRanking
canonicalFrontierRanking =
  candidateCompletePendingPromotionAcceptance
  ∷ genuineExternalContentFrontierIfInternalClosureDemanded
  ∷ []

canonicalSolvedSharedComponents :
  List SolvedSharedComponent
canonicalSolvedSharedComponents =
  universalScaleGraphBarrierAlgebraClosed
  ∷ []

canonicalUpstreamSharedFrontiers :
  List UpstreamSharedFrontier
canonicalUpstreamSharedFrontiers =
  monsterMultiplicityQuotientControl
  ∷ []

canonicalGate3FinalLemmas :
  List Gate3FinalLemma
canonicalGate3FinalLemmas =
  pawotgUniformSeparation
  ∷ uniformGaussianSpreadBelowP3Threshold
  ∷ moscoNoPollutionMassShellBridge
  ∷ []

canonicalYMFinalLemmas :
  List YMFinalLemma
canonicalYMFinalLemmas =
  actualAllDiameterKPBoundWithEffectiveC0
  ∷ balabanPhysicalBetaBridge
  ∷ continuumOSWightmanMassGapBridge
  ∷ []

canonicalNSFinalLemmas :
  List NSFinalLemma
canonicalNSFinalLemmas =
  tailRestrictedThetaBarrier
  ∷ negativeSobolevHighHighDefectBound
  ∷ nonCircularKStarDriftBound
  ∷ dangerShellMaximumPrinciple
  ∷ []

data RelatedExistingProofSurface : Set where
  scaleGraphBarrierAlgebraProofSurface :
    RelatedExistingProofSurface

  monsterQuotientControlTargetSurface :
    RelatedExistingProofSurface

  gate3PAWOTGTargetSurface :
    RelatedExistingProofSurface

  gate3ArchimedeanNestingTaperSurface :
    RelatedExistingProofSurface

  gate3MoscoConditionalSurface :
    RelatedExistingProofSurface

  gate3NoPollutionConditionalSurface :
    RelatedExistingProofSurface

  ymC0SensitivitySurface :
    RelatedExistingProofSurface

  ymPhysicalBetaBridgeTargetSurface :
    RelatedExistingProofSurface

  ymOSWightmanContinuumTargetSurface :
    RelatedExistingProofSurface

  nsTailRestrictedThetaDiagnosticSurface :
    RelatedExistingProofSurface

  nsNegativeSobolevDangerShellSurface :
    RelatedExistingProofSurface

  nsHminusHalfObstructionSurface :
    RelatedExistingProofSurface

  nsKStarDriftTargetSurface :
    RelatedExistingProofSurface

  nsDangerShellMaximumPrincipleSurface :
    RelatedExistingProofSurface

  binaryTetralemmaMarginGovernanceSurface :
    RelatedExistingProofSurface

canonicalRelatedExistingProofSurfaces :
  List RelatedExistingProofSurface
canonicalRelatedExistingProofSurfaces =
  scaleGraphBarrierAlgebraProofSurface
  ∷ monsterQuotientControlTargetSurface
  ∷ gate3PAWOTGTargetSurface
  ∷ gate3ArchimedeanNestingTaperSurface
  ∷ gate3MoscoConditionalSurface
  ∷ gate3NoPollutionConditionalSurface
  ∷ ymC0SensitivitySurface
  ∷ ymPhysicalBetaBridgeTargetSurface
  ∷ ymOSWightmanContinuumTargetSurface
  ∷ nsTailRestrictedThetaDiagnosticSurface
  ∷ nsNegativeSobolevDangerShellSurface
  ∷ nsHminusHalfObstructionSurface
  ∷ nsKStarDriftTargetSurface
  ∷ nsDangerShellMaximumPrincipleSurface
  ∷ binaryTetralemmaMarginGovernanceSurface
  ∷ []

data ClayFinalAnalyticFrontierNonClaim : Set where
  noPAWOTGUniformSeparationProof :
    ClayFinalAnalyticFrontierNonClaim

  noMonsterMultiplicityQuotientProof :
    ClayFinalAnalyticFrontierNonClaim

  noPhysicalBetaBridgeProof :
    ClayFinalAnalyticFrontierNonClaim

  noContinuumOSWightmanMassGapProof :
    ClayFinalAnalyticFrontierNonClaim

  noNonCircularKStarDriftProof :
    ClayFinalAnalyticFrontierNonClaim

  noDangerShellMaximumPrincipleProof :
    ClayFinalAnalyticFrontierNonClaim

  noClayPromotion :
    ClayFinalAnalyticFrontierNonClaim

canonicalFrontierNonClaims :
  List ClayFinalAnalyticFrontierNonClaim
canonicalFrontierNonClaims =
  noPAWOTGUniformSeparationProof
  ∷ noMonsterMultiplicityQuotientProof
  ∷ noPhysicalBetaBridgeProof
  ∷ noContinuumOSWightmanMassGapProof
  ∷ noNonCircularKStarDriftProof
  ∷ noDangerShellMaximumPrincipleProof
  ∷ noClayPromotion
  ∷ []

data ClayFinalAnalyticFrontierPromotion : Set where

clayFinalAnalyticFrontierPromotionImpossibleHere :
  ClayFinalAnalyticFrontierPromotion →
  ⊥
clayFinalAnalyticFrontierPromotionImpossibleHere ()

frontierSummary :
  String
frontierSummary =
  "Frontier map after the scale-graph algebra: NS and unification are candidate-complete packages pending promotion/acceptance, while YM remains the genuine external-content frontier if internal closure is required. All Clay promotion flags stay false here."

record ClayFinalAnalyticFrontierMapReceipt : Setω where
  field
    status :
      ClayFinalAnalyticFrontierStatus

    statusIsFailClosed :
      status ≡ clayFinalFrontierRecorded_failClosed

    algebraReceipt :
      Algebra.ScaleGraphBarrierAlgebraProofReceipt

    algebraRecorded :
      Algebra.algebraLemmaRecorded algebraReceipt ≡ true

    algebraKeepsClayFalse :
      Algebra.clayPromotion algebraReceipt ≡ false

    universalReceipt :
      Universal.UniversalScaleGraphBarrierTargetReceipt

    universalStillTargetOnly :
      Universal.barrierTheoremProvedHere universalReceipt ≡ false

    tetralemmaMarginReceipt :
      TetMargin.BinaryTetralemmaMarginStateReceipt

    tetralemmaMarginRecorded :
      TetMargin.fourValuedMarginGovernanceRecorded
        tetralemmaMarginReceipt
      ≡
      true

    tetralemmaMarginKeepsClayFalse :
      TetMargin.clayPromoted tetralemmaMarginReceipt ≡ false

    asymmetryReceipt :
      Asymmetry.ClayBlockerAsymmetryReceipt

    monsterReceipt :
      Monster.MonsterMoonshineSSPQuotientControlReceipt

    gatePAWOTGReceipt :
      GatePAWOTG.Gate3PAWOTGUniformSeparationTargetReceipt

    gateSamplerReceipt :
      GateSampler.Gate3AtomSamplerPAWOTGQualityReceipt

    gateNestingReceipt :
      GateNesting.Gate3NestingTaperConditionReceipt

    gateNestingRootIsArchimedean :
      GateNesting.archimedeanNestingIsRootProblem gateNestingReceipt
      ≡
      true

    gateNestingKeepsGate3False :
      GateNesting.gate3Promoted gateNestingReceipt ≡ false

    gateMoscoReceipt :
      GateMosco.Gate3MoscoConstructiveSequenceReceipt

    gateNoPollutionReceipt :
      GateNoPollution.Gate3NoSpectralPollutionConditionalProofReceipt

    ymC0Receipt :
      YMC0.YMC0EntropyThresholdSensitivityReceipt

    ymC0LoadBearing :
      YMC0.c0IsLoadBearing ymC0Receipt ≡ true

    ymMonsterEvidenceReceipt :
      YMMonsterEvidence.YMMonsterQuotientEvidenceReceipt

    ymMonsterT7EvidenceRecorded :
      YMMonsterEvidence.t7QuotientEvidenceRecorded ymMonsterEvidenceReceipt
      ≡
      true

    ymMonsterEvidenceKeepsClayFalse :
      YMMonsterEvidence.clayYMPromoted ymMonsterEvidenceReceipt ≡ false

    ymBetaReceipt :
      YMBeta.YMBalabanPhysicalBetaBridgeTargetReceipt

    ymBetaBridgeStillOpen :
      YMBeta.physicalBetaBridgeProvedHere ymBetaReceipt ≡ false

    ymOpenReceipt :
      YMOpen.YMPhysicalBetaBridgeOpenReceipt

    ymOpenReceiptKeepsClayFalse :
      YMOpen.clayYangMillsPromoted ymOpenReceipt ≡ false

    os3Receipt :
      OS3.CarrierOS3ReflectionPositivityReceipt

    os3KeepsClayFalse :
      OS3.clayYangMillsPromoted os3Receipt ≡ false

    wightmanReceipt :
      Wightman.WightmanReconstructionCandidateReceipt

    wightmanKeepsClayFalse :
      Wightman.clayYangMillsPromoted wightmanReceipt ≡ false

    nsTailReceipt :
      NSTail.NSTailRestrictedThetaDiagnosticReceipt

    nsTailKeepsClayFalse :
      NSTail.clayNavierStokesPromoted nsTailReceipt ≡ false

    nsNegativeReceipt :
      NSNegative.NSNegativeSobolevDangerShellReceipt zero

    nsNegativeKeepsClayFalse :
      NSNegative.clayNavierStokesPromoted nsNegativeReceipt ≡ false

    nsHminusReceipt :
      NSHminus.NSHminus1Over2ObstructionReceipt

    nsHminusDiverges :
      NSHminus.ratioDivergesAsNuToZero nsHminusReceipt ≡ true

    nsHminusNoUniformAbsorption :
      NSHminus.uniformAbsorptionEstimateProvedHere nsHminusReceipt
      ≡
      false

    nsHminusPublishableObstruction :
      NSHminus.publishableObstructionResult nsHminusReceipt ≡ true

    nsHminusKeepsClayFalse :
      NSHminus.clayNavierStokesPromoted nsHminusReceipt ≡ false

    nsHminusClayNSAliasKeepsFalse :
      NSHminus.clayNSProved nsHminusReceipt ≡ false

    nsKStarReceipt :
      NSKStar.NSNonCircularKStarDriftBoundTargetReceipt

    nsKStarKeepsClayFalse :
      NSKStar.clayNavierStokesPromoted nsKStarReceipt ≡ false

    nsDangerReceipt :
      NSDanger.NSDangerShellMaximumPrincipleReceipt

    nsDangerStillOpen :
      NSDanger.dangerShellMaxPrincipleProved nsDangerReceipt ≡ false

    solvedSharedComponents :
      List SolvedSharedComponent

    solvedSharedComponentsAreCanonical :
      solvedSharedComponents ≡ canonicalSolvedSharedComponents

    upstreamSharedFrontiers :
      List UpstreamSharedFrontier

    upstreamSharedFrontiersAreCanonical :
      upstreamSharedFrontiers ≡ canonicalUpstreamSharedFrontiers

    gate3FinalLemmas :
      List Gate3FinalLemma

    gate3FinalLemmasAreCanonical :
      gate3FinalLemmas ≡ canonicalGate3FinalLemmas

    ymFinalLemmas :
      List YMFinalLemma

    ymFinalLemmasAreCanonical :
      ymFinalLemmas ≡ canonicalYMFinalLemmas

    nsFinalLemmas :
      List NSFinalLemma

    nsFinalLemmasAreCanonical :
      nsFinalLemmas ≡ canonicalNSFinalLemmas

    candidateCompletePackages :
      List CandidateCompletePackage

    candidateCompletePackagesAreCanonical :
      candidateCompletePackages ≡ canonicalCandidateCompletePackages

    genuineExternalContentFrontiers :
      List GenuineExternalContentFrontier

    genuineExternalContentFrontiersAreCanonical :
      genuineExternalContentFrontiers
      ≡
      canonicalGenuineExternalContentFrontiers

    frontierRanking :
      List FrontierRanking

    frontierRankingIsCanonical :
      frontierRanking ≡ canonicalFrontierRanking

    relatedExistingProofSurfaces :
      List RelatedExistingProofSurface

    relatedExistingProofSurfacesAreCanonical :
      relatedExistingProofSurfaces
      ≡
      canonicalRelatedExistingProofSurfaces

    nonClaims :
      List ClayFinalAnalyticFrontierNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalFrontierNonClaims

    summary :
      String

    summaryIsCanonical :
      summary ≡ frontierSummary

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List ClayFinalAnalyticFrontierPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ClayFinalAnalyticFrontierPromotion →
      ⊥

open ClayFinalAnalyticFrontierMapReceipt public

canonicalClayFinalAnalyticFrontierMapReceipt :
  ClayFinalAnalyticFrontierMapReceipt
canonicalClayFinalAnalyticFrontierMapReceipt =
  record
    { status =
        clayFinalFrontierRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; algebraReceipt =
        Algebra.canonicalScaleGraphBarrierAlgebraProofReceipt
    ; algebraRecorded =
        refl
    ; algebraKeepsClayFalse =
        refl
    ; universalReceipt =
        Universal.canonicalUniversalScaleGraphBarrierTargetReceipt
    ; universalStillTargetOnly =
        refl
    ; tetralemmaMarginReceipt =
        TetMargin.canonicalBinaryTetralemmaMarginStateReceipt
    ; tetralemmaMarginRecorded =
        refl
    ; tetralemmaMarginKeepsClayFalse =
        refl
    ; asymmetryReceipt =
        Asymmetry.canonicalClayBlockerAsymmetryReceipt
    ; monsterReceipt =
        Monster.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; gatePAWOTGReceipt =
        GatePAWOTG.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; gateSamplerReceipt =
        GateSampler.canonicalGate3AtomSamplerPAWOTGQualityReceipt
    ; gateNestingReceipt =
        GateNesting.canonicalGate3NestingTaperConditionReceipt
    ; gateNestingRootIsArchimedean =
        refl
    ; gateNestingKeepsGate3False =
        refl
    ; gateMoscoReceipt =
        GateMosco.canonicalGate3MoscoConstructiveSequenceReceipt
    ; gateNoPollutionReceipt =
        GateNoPollution.canonicalGate3NoSpectralPollutionConditionalProofReceipt
    ; ymC0Receipt =
        YMC0.canonicalYMC0EntropyThresholdSensitivityReceipt
    ; ymC0LoadBearing =
        refl
    ; ymMonsterEvidenceReceipt =
        YMMonsterEvidence.canonicalYMMonsterQuotientEvidenceReceipt
    ; ymMonsterT7EvidenceRecorded =
        refl
    ; ymMonsterEvidenceKeepsClayFalse =
        refl
    ; ymBetaReceipt =
        YMBeta.canonicalYMBalabanPhysicalBetaBridgeTargetReceipt
    ; ymBetaBridgeStillOpen =
        refl
    ; ymOpenReceipt =
        YMOpen.canonicalYMPhysicalBetaBridgeOpenReceipt
    ; ymOpenReceiptKeepsClayFalse =
        refl
    ; os3Receipt =
        OS3.canonicalCarrierOS3ReflectionPositivityReceipt
    ; os3KeepsClayFalse =
        refl
    ; wightmanReceipt =
        Wightman.canonicalWightmanReconstructionCandidateReceipt
    ; wightmanKeepsClayFalse =
        refl
    ; nsTailReceipt =
        NSTail.canonicalNSTailRestrictedThetaDiagnosticReceipt
    ; nsTailKeepsClayFalse =
        refl
    ; nsNegativeReceipt =
        NSNegative.canonicalNSNegativeSobolevDangerShellReceipt
    ; nsNegativeKeepsClayFalse =
        refl
    ; nsHminusReceipt =
        NSHminus.canonicalNSHminus1Over2ObstructionReceipt
    ; nsHminusDiverges =
        refl
    ; nsHminusNoUniformAbsorption =
        refl
    ; nsHminusPublishableObstruction =
        refl
    ; nsHminusKeepsClayFalse =
        refl
    ; nsHminusClayNSAliasKeepsFalse =
        refl
    ; nsKStarReceipt =
        NSKStar.canonicalNSNonCircularKStarDriftBoundTargetReceipt
    ; nsKStarKeepsClayFalse =
        refl
    ; nsDangerReceipt =
        NSDanger.canonicalNSDangerShellMaximumPrincipleReceipt
    ; nsDangerStillOpen =
        refl
    ; solvedSharedComponents =
        canonicalSolvedSharedComponents
    ; solvedSharedComponentsAreCanonical =
        refl
    ; upstreamSharedFrontiers =
        canonicalUpstreamSharedFrontiers
    ; upstreamSharedFrontiersAreCanonical =
        refl
    ; gate3FinalLemmas =
        canonicalGate3FinalLemmas
    ; gate3FinalLemmasAreCanonical =
        refl
    ; ymFinalLemmas =
        canonicalYMFinalLemmas
    ; ymFinalLemmasAreCanonical =
        refl
    ; nsFinalLemmas =
        canonicalNSFinalLemmas
    ; nsFinalLemmasAreCanonical =
        refl
    ; candidateCompletePackages =
        canonicalCandidateCompletePackages
    ; candidateCompletePackagesAreCanonical =
        refl
    ; genuineExternalContentFrontiers =
        canonicalGenuineExternalContentFrontiers
    ; genuineExternalContentFrontiersAreCanonical =
        refl
    ; frontierRanking =
        canonicalFrontierRanking
    ; frontierRankingIsCanonical =
        refl
    ; relatedExistingProofSurfaces =
        canonicalRelatedExistingProofSurfaces
    ; relatedExistingProofSurfacesAreCanonical =
        refl
    ; nonClaims =
        canonicalFrontierNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; summary =
        frontierSummary
    ; summaryIsCanonical =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        clayFinalAnalyticFrontierPromotionImpossibleHere
    }

canonicalClayFinalAnalyticFrontierNoClay :
  clayPromoted canonicalClayFinalAnalyticFrontierMapReceipt ≡ false
canonicalClayFinalAnalyticFrontierNoClay =
  refl

canonicalClayFinalAnalyticFrontierAlgebraClosed :
  Algebra.algebraLemmaRecorded
    (algebraReceipt canonicalClayFinalAnalyticFrontierMapReceipt)
  ≡
  true
canonicalClayFinalAnalyticFrontierAlgebraClosed =
  refl
