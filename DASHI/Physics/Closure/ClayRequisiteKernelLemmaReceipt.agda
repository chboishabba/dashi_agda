module DASHI.Physics.Closure.ClayRequisiteKernelLemmaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayKernelReductionReceipt as Kernel
import DASHI.Physics.Closure.ClayOptimalKernelLemmaReceipt as Optimal
import DASHI.Physics.Closure.ClayProofCampaignDependencyDAGReceipt as DAG

------------------------------------------------------------------------
-- Clay requisite kernel lemma receipt.
--
-- This receipt records the shortest current list of theorem targets required
-- for Clay-facing promotion.  It consumes the broader kernel/DAG receipts but
-- does not strengthen them.  Constructorless MissingRequisiteTarget fields
-- keep all open theorem targets uninhabited.

data ClayRequisiteKernelStatus : Set where
  clayRequisiteKernelLemmaSurfaceRecorded_failClosed :
    ClayRequisiteKernelStatus

data RequisiteYMLemma : Set where
  connectedAnimalKPBound :
    RequisiteYMLemma

  t7APerPolymerActivitySuppression :
    RequisiteYMLemma

  analyticContinuumKP :
    RequisiteYMLemma

  balabanConnectedAnimalBridge :
    RequisiteYMLemma

  dimensionfulMassGapConvergence :
    RequisiteYMLemma

  hyperbolicShimuraToEuclideanUniversality :
    RequisiteYMLemma

  gaugeFixedOSPositivity :
    RequisiteYMLemma

  osWightmanReconstruction :
    RequisiteYMLemma

  uniformContinuumMassGapSurvival :
    RequisiteYMLemma

  nontrivial4DSU3YangMills :
    RequisiteYMLemma

canonicalRequisiteYMLemmas : List RequisiteYMLemma
canonicalRequisiteYMLemmas =
  connectedAnimalKPBound
  ∷ t7APerPolymerActivitySuppression
  ∷ analyticContinuumKP
  ∷ balabanConnectedAnimalBridge
  ∷ dimensionfulMassGapConvergence
  ∷ hyperbolicShimuraToEuclideanUniversality
  ∷ gaugeFixedOSPositivity
  ∷ osWightmanReconstruction
  ∷ uniformContinuumMassGapSurvival
  ∷ nontrivial4DSU3YangMills
  ∷ []

data RequisiteNSLemma : Set where
  carrierToStandardH118NormComparison :
    RequisiteNSLemma

  nsFlowProjectionTransport :
    RequisiteNSLemma

  cumulativeTailDissipationDominance :
    RequisiteNSLemma

  dangerShellMaximumPrinciple :
    RequisiteNSLemma

  kStarNoInertialDrift :
    RequisiteNSLemma

  bernoulliBandGlobalH118Bound :
    RequisiteNSLemma

  h118ContinuationCriterion :
    RequisiteNSLemma

  carrierStructuredDenseInSmoothDivergenceFree :
    RequisiteNSLemma

  approximationStability :
    RequisiteNSLemma

canonicalRequisiteNSLemmas : List RequisiteNSLemma
canonicalRequisiteNSLemmas =
  carrierToStandardH118NormComparison
  ∷ nsFlowProjectionTransport
  ∷ cumulativeTailDissipationDominance
  ∷ dangerShellMaximumPrinciple
  ∷ kStarNoInertialDrift
  ∷ bernoulliBandGlobalH118Bound
  ∷ h118ContinuationCriterion
  ∷ carrierStructuredDenseInSmoothDivergenceFree
  ∷ approximationStability
  ∷ []

data RequisiteGate3Lemma : Set where
  atomGrammarCMSplittingSeparation :
    RequisiteGate3Lemma

  physicalSSPEmbedding3D :
    RequisiteGate3Lemma

  physicalSSPSpreadBound :
    RequisiteGate3Lemma

  uniformFrameLowerBound :
    RequisiteGate3Lemma

  gate3MoscoNoPollutionTransfer :
    RequisiteGate3Lemma

canonicalRequisiteGate3Lemmas : List RequisiteGate3Lemma
canonicalRequisiteGate3Lemmas =
  atomGrammarCMSplittingSeparation
  ∷ physicalSSPEmbedding3D
  ∷ physicalSSPSpreadBound
  ∷ uniformFrameLowerBound
  ∷ gate3MoscoNoPollutionTransfer
  ∷ []

data RequisiteWorkerLane : Set where
  worker1YMKPActivity :
    RequisiteWorkerLane

  worker2YMBalabanRG :
    RequisiteWorkerLane

  worker3YMFlatOSGap :
    RequisiteWorkerLane

  worker4NSTail :
    RequisiteWorkerLane

  worker5Gate3Support :
    RequisiteWorkerLane

  worker6Governance :
    RequisiteWorkerLane

canonicalRequisiteWorkers : List RequisiteWorkerLane
canonicalRequisiteWorkers =
  worker1YMKPActivity
  ∷ worker2YMBalabanRG
  ∷ worker3YMFlatOSGap
  ∷ worker4NSTail
  ∷ worker5Gate3Support
  ∷ worker6Governance
  ∷ []

data MissingYMLemma : RequisiteYMLemma → Set where
data MissingNSLemma : RequisiteNSLemma → Set where
data MissingGate3Lemma : RequisiteGate3Lemma → Set where

data ClayRequisiteKernelPromotion : Set where

clayRequisiteKernelPromotionImpossibleHere :
  ClayRequisiteKernelPromotion →
  ⊥
clayRequisiteKernelPromotionImpossibleHere ()

connectedAnimalThresholdHundredths : Nat
connectedAnimalThresholdHundredths =
  959

connectedAnimalGapHundredths : Nat
connectedAnimalGapHundredths =
  359

directT7AThresholdHundredths : Nat
directT7AThresholdHundredths =
  1656

directT7AGapHundredths : Nat
directT7AGapHundredths =
  1056

physicalBetaHundredths : Nat
physicalBetaHundredths =
  600

ymRouteStatement : String
ymRouteStatement =
  "YM requisite route: connected-animal KP is the counting route at beta* ~= 9.593637 with gap 3.593637 from beta_phys ~= 6, but that is KP convergence only. Strict Balaban seeding must be stated as beta*c_min-a>log(2p), with robust sample beta_eff>=13.7. Direct T7A counting is proved at beta* ~= 16.56 but is worse for counting. T7A can help only through per-polymer activity suppression |z(Gamma)| <= (T7A(d)/(d*p^(d-1))) * exp(-beta*c_min*d)."

nsRouteStatement : String
nsRouteStatement =
  "NS requisite route: numerical shell-flux and synthetic dissipation checks are support only. Clay needs NSFlowProjectionTransport, CumulativeTailDissipationDominance, DangerShellMaximumPrinciple, KStarNoInertialDrift, H118 continuation, and all-smooth-data stability."

gate3RouteStatement : String
gate3RouteStatement =
  "Gate3 requisite support: keep 7+7+1 semantic and the literal Q(sqrt(-7)) table 5+9+1 with p71 split-not-inert; prove PhysicalSSPEmbedding3D, PhysicalSSPSpreadBound, UniformFrameLowerBound, and Mosco/no-pollution transfer."

receiptBoundaryStatement : String
receiptBoundaryStatement =
  "This receipt records the required Clay kernel lemmas and worker lanes only. It proves no Clay, Gate3, W4, gravity, Schwarzschild, Yang-Mills, Navier-Stokes, or terminal promotion."

record ClayRequisiteKernelLemmaReceipt : Setω where
  field
    status :
      ClayRequisiteKernelStatus

    statusIsCanonical :
      status ≡ clayRequisiteKernelLemmaSurfaceRecorded_failClosed

    kernelReceipt :
      Kernel.ClayKernelReductionReceipt

    kernelYMStillFalse :
      Kernel.ymPromotion kernelReceipt ≡ false

    kernelNSStillFalse :
      Kernel.nsPromotion kernelReceipt ≡ false

    kernelGate3StillFalse :
      Kernel.gate3Promotion kernelReceipt ≡ false

    optimalReceipt :
      Optimal.ClayOptimalKernelLemmaReceipt

    optimalYMStillFalse :
      Optimal.clayYangMillsPromoted optimalReceipt ≡ false

    optimalNSStillFalse :
      Optimal.clayNavierStokesPromoted optimalReceipt ≡ false

    optimalGate3StillFalse :
      Optimal.gate3Closed optimalReceipt ≡ false

    dagReceipt :
      DAG.ClayProofCampaignDependencyDAGReceipt

    dagYMStillFalse :
      DAG.clayYangMillsPromoted dagReceipt ≡ false

    dagNSStillFalse :
      DAG.clayNavierStokesPromoted dagReceipt ≡ false

    dagGravityStillFalse :
      DAG.gravityPredictionPromoted dagReceipt ≡ false

    dagKeepsP71Split :
      DAG.cmClassOf DAG.p71 ≡ DAG.cmSplit

    ymLemmas :
      List RequisiteYMLemma

    ymLemmasAreCanonical :
      ymLemmas ≡ canonicalRequisiteYMLemmas

    nsLemmas :
      List RequisiteNSLemma

    nsLemmasAreCanonical :
      nsLemmas ≡ canonicalRequisiteNSLemmas

    gate3Lemmas :
      List RequisiteGate3Lemma

    gate3LemmasAreCanonical :
      gate3Lemmas ≡ canonicalRequisiteGate3Lemmas

    workers :
      List RequisiteWorkerLane

    workersAreCanonical :
      workers ≡ canonicalRequisiteWorkers

    ymT7CoefficientPositive :
      Bool

    ymT7CoefficientPositiveIsTrue :
      ymT7CoefficientPositive ≡ true

    ymConnectedAnimalBoundProved :
      Bool

    ymConnectedAnimalBoundProvedIsTrue :
      ymConnectedAnimalBoundProved ≡ true

    ymConnectedAnimalThreshold :
      Nat

    ymConnectedAnimalThresholdIs959 :
      ymConnectedAnimalThreshold ≡ connectedAnimalThresholdHundredths

    ymConnectedAnimalGap :
      Nat

    ymConnectedAnimalGapIs359 :
      ymConnectedAnimalGap ≡ connectedAnimalGapHundredths

    ymT7ADirectThreshold :
      Nat

    ymT7ADirectThresholdIs1656 :
      ymT7ADirectThreshold ≡ directT7AThresholdHundredths

    ymT7ADirectGap :
      Nat

    ymT7ADirectGapIs1056 :
      ymT7ADirectGap ≡ directT7AGapHundredths

    ymPhysicalBeta :
      Nat

    ymPhysicalBetaIs600 :
      ymPhysicalBeta ≡ physicalBetaHundredths

    ymT7ADirectCountingDemoted :
      Bool

    ymT7ADirectCountingDemotedIsTrue :
      ymT7ADirectCountingDemoted ≡ true

    ymConnectedAnimalRoutePreferred :
      Bool

    ymConnectedAnimalRoutePreferredIsTrue :
      ymConnectedAnimalRoutePreferred ≡ true

    ymT7AActivitySuppressionOnly :
      Bool

    ymT7AActivitySuppressionOnlyIsTrue :
      ymT7AActivitySuppressionOnly ≡ true

    nsShellFluxIdentityNumericalVerified :
      Bool

    nsShellFluxIdentityNumericalVerifiedIsTrue :
      nsShellFluxIdentityNumericalVerified ≡ true

    nsSyntheticDissipationDominatesFlux :
      Bool

    nsSyntheticDissipationDominatesFluxIsTrue :
      nsSyntheticDissipationDominatesFlux ≡ true

    ymT7APerPolymerActivitySuppressionTarget :
      Set

    ymT7APerPolymerActivitySuppressionTargetIsMissing :
      ymT7APerPolymerActivitySuppressionTarget ≡
        MissingYMLemma t7APerPolymerActivitySuppression

    ymBalabanConnectedAnimalBridgeTarget :
      Set

    ymBalabanConnectedAnimalBridgeTargetIsMissing :
      ymBalabanConnectedAnimalBridgeTarget ≡
        MissingYMLemma balabanConnectedAnimalBridge

    ymHyperbolicShimuraToEuclideanUniversalityTarget :
      Set

    ymHyperbolicShimuraToEuclideanUniversalityTargetIsMissing :
      ymHyperbolicShimuraToEuclideanUniversalityTarget ≡
        MissingYMLemma hyperbolicShimuraToEuclideanUniversality

    ymOSWightmanReconstructionTarget :
      Set

    ymOSWightmanReconstructionTargetIsMissing :
      ymOSWightmanReconstructionTarget ≡
        MissingYMLemma osWightmanReconstruction

    ymUniformContinuumMassGapSurvivalTarget :
      Set

    ymUniformContinuumMassGapSurvivalTargetIsMissing :
      ymUniformContinuumMassGapSurvivalTarget ≡
        MissingYMLemma uniformContinuumMassGapSurvival

    nsCumulativeTailDissipationDominanceTarget :
      Set

    nsCumulativeTailDissipationDominanceTargetIsMissing :
      nsCumulativeTailDissipationDominanceTarget ≡
        MissingNSLemma cumulativeTailDissipationDominance

    nsDangerShellMaximumPrincipleTarget :
      Set

    nsDangerShellMaximumPrincipleTargetIsMissing :
      nsDangerShellMaximumPrincipleTarget ≡
        MissingNSLemma dangerShellMaximumPrinciple

    nsKStarNoInertialDriftTarget :
      Set

    nsKStarNoInertialDriftTargetIsMissing :
      nsKStarNoInertialDriftTarget ≡
        MissingNSLemma kStarNoInertialDrift

    gate3PhysicalSSPSpreadBoundTarget :
      Set

    gate3PhysicalSSPSpreadBoundTargetIsMissing :
      gate3PhysicalSSPSpreadBoundTarget ≡
        MissingGate3Lemma physicalSSPSpreadBound

    gate3UniformFrameLowerBoundTarget :
      Set

    gate3UniformFrameLowerBoundTargetIsMissing :
      gate3UniformFrameLowerBoundTarget ≡
        MissingGate3Lemma uniformFrameLowerBound

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    promotions :
      List ClayRequisiteKernelPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ClayRequisiteKernelPromotion →
      ⊥

    ymText :
      String

    ymTextIsCanonical :
      ymText ≡ ymRouteStatement

    nsText :
      String

    nsTextIsCanonical :
      nsText ≡ nsRouteStatement

    gate3Text :
      String

    gate3TextIsCanonical :
      gate3Text ≡ gate3RouteStatement

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryStatement

open ClayRequisiteKernelLemmaReceipt public

canonicalClayRequisiteKernelLemmaReceipt :
  ClayRequisiteKernelLemmaReceipt
canonicalClayRequisiteKernelLemmaReceipt =
  record
    { status =
        clayRequisiteKernelLemmaSurfaceRecorded_failClosed
    ; statusIsCanonical =
        refl
    ; kernelReceipt =
        Kernel.canonicalClayKernelReductionReceipt
    ; kernelYMStillFalse =
        refl
    ; kernelNSStillFalse =
        refl
    ; kernelGate3StillFalse =
        refl
    ; optimalReceipt =
        Optimal.canonicalClayOptimalKernelLemmaReceipt
    ; optimalYMStillFalse =
        refl
    ; optimalNSStillFalse =
        refl
    ; optimalGate3StillFalse =
        refl
    ; dagReceipt =
        DAG.canonicalClayProofCampaignDependencyDAGReceipt
    ; dagYMStillFalse =
        refl
    ; dagNSStillFalse =
        refl
    ; dagGravityStillFalse =
        refl
    ; dagKeepsP71Split =
        refl
    ; ymLemmas =
        canonicalRequisiteYMLemmas
    ; ymLemmasAreCanonical =
        refl
    ; nsLemmas =
        canonicalRequisiteNSLemmas
    ; nsLemmasAreCanonical =
        refl
    ; gate3Lemmas =
        canonicalRequisiteGate3Lemmas
    ; gate3LemmasAreCanonical =
        refl
    ; workers =
        canonicalRequisiteWorkers
    ; workersAreCanonical =
        refl
    ; ymT7CoefficientPositive =
        true
    ; ymT7CoefficientPositiveIsTrue =
        refl
    ; ymConnectedAnimalBoundProved =
        true
    ; ymConnectedAnimalBoundProvedIsTrue =
        refl
    ; ymConnectedAnimalThreshold =
        connectedAnimalThresholdHundredths
    ; ymConnectedAnimalThresholdIs959 =
        refl
    ; ymConnectedAnimalGap =
        connectedAnimalGapHundredths
    ; ymConnectedAnimalGapIs359 =
        refl
    ; ymT7ADirectThreshold =
        directT7AThresholdHundredths
    ; ymT7ADirectThresholdIs1656 =
        refl
    ; ymT7ADirectGap =
        directT7AGapHundredths
    ; ymT7ADirectGapIs1056 =
        refl
    ; ymPhysicalBeta =
        physicalBetaHundredths
    ; ymPhysicalBetaIs600 =
        refl
    ; ymT7ADirectCountingDemoted =
        true
    ; ymT7ADirectCountingDemotedIsTrue =
        refl
    ; ymConnectedAnimalRoutePreferred =
        true
    ; ymConnectedAnimalRoutePreferredIsTrue =
        refl
    ; ymT7AActivitySuppressionOnly =
        true
    ; ymT7AActivitySuppressionOnlyIsTrue =
        refl
    ; nsShellFluxIdentityNumericalVerified =
        true
    ; nsShellFluxIdentityNumericalVerifiedIsTrue =
        refl
    ; nsSyntheticDissipationDominatesFlux =
        true
    ; nsSyntheticDissipationDominatesFluxIsTrue =
        refl
    ; ymT7APerPolymerActivitySuppressionTarget =
        MissingYMLemma t7APerPolymerActivitySuppression
    ; ymT7APerPolymerActivitySuppressionTargetIsMissing =
        refl
    ; ymBalabanConnectedAnimalBridgeTarget =
        MissingYMLemma balabanConnectedAnimalBridge
    ; ymBalabanConnectedAnimalBridgeTargetIsMissing =
        refl
    ; ymHyperbolicShimuraToEuclideanUniversalityTarget =
        MissingYMLemma hyperbolicShimuraToEuclideanUniversality
    ; ymHyperbolicShimuraToEuclideanUniversalityTargetIsMissing =
        refl
    ; ymOSWightmanReconstructionTarget =
        MissingYMLemma osWightmanReconstruction
    ; ymOSWightmanReconstructionTargetIsMissing =
        refl
    ; ymUniformContinuumMassGapSurvivalTarget =
        MissingYMLemma uniformContinuumMassGapSurvival
    ; ymUniformContinuumMassGapSurvivalTargetIsMissing =
        refl
    ; nsCumulativeTailDissipationDominanceTarget =
        MissingNSLemma cumulativeTailDissipationDominance
    ; nsCumulativeTailDissipationDominanceTargetIsMissing =
        refl
    ; nsDangerShellMaximumPrincipleTarget =
        MissingNSLemma dangerShellMaximumPrinciple
    ; nsDangerShellMaximumPrincipleTargetIsMissing =
        refl
    ; nsKStarNoInertialDriftTarget =
        MissingNSLemma kStarNoInertialDrift
    ; nsKStarNoInertialDriftTargetIsMissing =
        refl
    ; gate3PhysicalSSPSpreadBoundTarget =
        MissingGate3Lemma physicalSSPSpreadBound
    ; gate3PhysicalSSPSpreadBoundTargetIsMissing =
        refl
    ; gate3UniformFrameLowerBoundTarget =
        MissingGate3Lemma uniformFrameLowerBound
    ; gate3UniformFrameLowerBoundTargetIsMissing =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        clayRequisiteKernelPromotionImpossibleHere
    ; ymText =
        ymRouteStatement
    ; ymTextIsCanonical =
        refl
    ; nsText =
        nsRouteStatement
    ; nsTextIsCanonical =
        refl
    ; gate3Text =
        gate3RouteStatement
    ; gate3TextIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    }

requisiteKeepsYMFalse :
  clayYangMillsPromoted canonicalClayRequisiteKernelLemmaReceipt ≡ false
requisiteKeepsYMFalse =
  refl

requisiteKeepsNSFalse :
  clayNavierStokesPromoted canonicalClayRequisiteKernelLemmaReceipt ≡ false
requisiteKeepsNSFalse =
  refl

requisiteKeepsGate3False :
  gate3Closed canonicalClayRequisiteKernelLemmaReceipt ≡ false
requisiteKeepsGate3False =
  refl

requisiteKeepsP71Split :
  DAG.cmClassOf DAG.p71 ≡ DAG.cmSplit
requisiteKeepsP71Split =
  refl
