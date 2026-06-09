module DASHI.Physics.Closure.DashiCFDThetaRuntimeDiagnosticReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)

import DASHI.Physics.Closure.NSToEV5DashiCFDExperimentPlanReceipt
  as ExperimentPlan

------------------------------------------------------------------------
-- dashiCFD theta runtime diagnostic receipt.
--
-- This receipt records the runtime diagnostic requested after the
-- dashiCFD experiment plan: compute
--
--   theta(k,t) = |Flux_tail(k,t)| / Diss_tail(k,t)
--
-- from Fourier/shell data.  The runtime computes the whole profile over
-- k >= K*(nu), records the danger shell argmax, and records Theta(t) as the
-- profile supremum.  It deliberately does not assume theta(k) monotone and
-- does not claim theta<1 is equivalent to BKM.  Stress tests are evidence
-- controls: they can support or falsify the diagnostic, but they do not prove
-- NS, EV5 transfer, BKM continuation, or Clay regularity.

data DashiCFDThetaRuntimeStatus : Set where
  thetaRuntimeDiagnosticRecorded_noNSProof_noClayPromotion :
    DashiCFDThetaRuntimeStatus

data FourierShellRuntimeInput : Set where
  fourierModeK :
    FourierShellRuntimeInput

  runtimeIndexT :
    FourierShellRuntimeInput

  shellFluxObservable :
    FourierShellRuntimeInput

  shellDissipationObservable :
    FourierShellRuntimeInput

  shellOrFourierBinMetadata :
    FourierShellRuntimeInput

canonicalFourierShellRuntimeInputs :
  List FourierShellRuntimeInput
canonicalFourierShellRuntimeInputs =
  fourierModeK
  ∷ runtimeIndexT
  ∷ shellFluxObservable
  ∷ shellDissipationObservable
  ∷ shellOrFourierBinMetadata
  ∷ []

data ThetaRuntimeObservable : Set where
  absoluteFluxMagnitude :
    ThetaRuntimeObservable

  positiveDissipationDenominator :
    ThetaRuntimeObservable

  thetaFluxOverDissipationRatio :
    ThetaRuntimeObservable

  thetaLessThanOneGate :
    ThetaRuntimeObservable

  thetaWholeProfileOverKStar :
    ThetaRuntimeObservable

  thetaDangerShellArgmax :
    ThetaRuntimeObservable

  thetaSupremumOverProfile :
    ThetaRuntimeObservable

  thetaMonotonicityNotAssumed :
    ThetaRuntimeObservable

  thetaBKMEquivalenceNotClaimed :
    ThetaRuntimeObservable

canonicalThetaRuntimeObservables :
  List ThetaRuntimeObservable
canonicalThetaRuntimeObservables =
  absoluteFluxMagnitude
  ∷ positiveDissipationDenominator
  ∷ thetaFluxOverDissipationRatio
  ∷ thetaLessThanOneGate
  ∷ thetaWholeProfileOverKStar
  ∷ thetaDangerShellArgmax
  ∷ thetaSupremumOverProfile
  ∷ thetaMonotonicityNotAssumed
  ∷ thetaBKMEquivalenceNotClaimed
  ∷ []

data ThetaRuntimeProfileScope : Set where
  thetaProfileComputable :
    ThetaRuntimeProfileScope

  thetaDangerShellCriticalArgmaxOverKStar :
    ThetaRuntimeProfileScope

  thetaHighShellDecayOpenConditional :
    ThetaRuntimeProfileScope

  thetaNotMonotone :
    ThetaRuntimeProfileScope

  thetaLessThanOneContinuationConditional :
    ThetaRuntimeProfileScope

  thetaBKMEquivalenceNotProved :
    ThetaRuntimeProfileScope

canonicalThetaRuntimeProfileScope :
  List ThetaRuntimeProfileScope
canonicalThetaRuntimeProfileScope =
  thetaProfileComputable
  ∷ thetaDangerShellCriticalArgmaxOverKStar
  ∷ thetaHighShellDecayOpenConditional
  ∷ thetaNotMonotone
  ∷ thetaLessThanOneContinuationConditional
  ∷ thetaBKMEquivalenceNotProved
  ∷ []

record FourierShellDataPoint : Set where
  field
    k :
      Nat

    t :
      Nat

    fluxMagnitude :
      Nat

    dissipation :
      Nat

    dissipationPositive :
      zero < dissipation

open FourierShellDataPoint public

record ThetaRatio : Set where
  field
    numerator :
      Nat

    denominator :
      Nat

    denominatorPositive :
      zero < denominator

open ThetaRatio public

thetaFromFourierShellData :
  FourierShellDataPoint →
  ThetaRatio
thetaFromFourierShellData point =
  record
    { numerator =
        fluxMagnitude point
    ; denominator =
        dissipation point
    ; denominatorPositive =
        dissipationPositive point
    }

data EmpiricalEV5RuntimeCheckComponent : Set where
  lane7NonIncreasingRuntimeGate :
    EmpiricalEV5RuntimeCheckComponent

  lane2BoundedRuntimeGate :
    EmpiricalEV5RuntimeCheckComponent

  thetaProfileRuntimeDiagnostic :
    EmpiricalEV5RuntimeCheckComponent

  thetaDangerShellRuntimeDiagnostic :
    EmpiricalEV5RuntimeCheckComponent

  thetaStrictlyBelowOneRuntimeSeamGauge :
    EmpiricalEV5RuntimeCheckComponent

  noThetaMonotonicityAssumption :
    EmpiricalEV5RuntimeCheckComponent

  noThetaBKMEquivalenceClaim :
    EmpiricalEV5RuntimeCheckComponent

canonicalEmpiricalEV5RuntimeCheckComponents :
  List EmpiricalEV5RuntimeCheckComponent
canonicalEmpiricalEV5RuntimeCheckComponents =
  lane7NonIncreasingRuntimeGate
  ∷ lane2BoundedRuntimeGate
  ∷ thetaProfileRuntimeDiagnostic
  ∷ thetaDangerShellRuntimeDiagnostic
  ∷ thetaStrictlyBelowOneRuntimeSeamGauge
  ∷ noThetaMonotonicityAssumption
  ∷ noThetaBKMEquivalenceClaim
  ∷ []

record RuntimeEV5ThetaGate : Set where
  field
    lane7Before :
      Nat

    lane7After :
      Nat

    lane7NonIncreasing :
      lane7After ≤ lane7Before

    lane2RuntimeDepth :
      Nat

    lane2RuntimeCutoff :
      Nat

    lane2Bounded :
      lane2RuntimeDepth ≤ lane2RuntimeCutoff

    theta :
      ThetaRatio

    thetaLessThanOne :
      numerator theta < denominator theta

open RuntimeEV5ThetaGate public

data RuntimeStressTestRole : Set where
  supportDiagnosticWhenStableAcrossSeedsGridsBackends :
    RuntimeStressTestRole

  falsifyDiagnosticOnLaneOrThetaViolation :
    RuntimeStressTestRole

  neverPromoteToProof :
    RuntimeStressTestRole

canonicalRuntimeStressTestRoles :
  List RuntimeStressTestRole
canonicalRuntimeStressTestRoles =
  supportDiagnosticWhenStableAcrossSeedsGridsBackends
  ∷ falsifyDiagnosticOnLaneOrThetaViolation
  ∷ neverPromoteToProof
  ∷ []

data RuntimeStressTest : Set where
  seedSweep :
    RuntimeStressTest

  gridRefinementSweep :
    RuntimeStressTest

  backendComparisonCPUAndGPU :
    RuntimeStressTest

  forcedCascadeBurst :
    RuntimeStressTest

  longTailDissipationWindow :
    RuntimeStressTest

canonicalRuntimeStressTests :
  List RuntimeStressTest
canonicalRuntimeStressTests =
  seedSweep
  ∷ gridRefinementSweep
  ∷ backendComparisonCPUAndGPU
  ∷ forcedCascadeBurst
  ∷ longTailDissipationWindow
  ∷ []

data RuntimeProofPromotionToken : Set where

runtimeProofPromotionImpossibleHere :
  RuntimeProofPromotionToken →
  ⊥
runtimeProofPromotionImpossibleHere ()

thetaFormulaText :
  String
thetaFormulaText =
  "theta(k,t)=|Flux_tail(k,t)|/Diss_tail(k,t), computed over every cutoff k>=K*(nu) from Fourier/shell runtime data with Diss(k,t)>0"

ev5RuntimeUpgradeText :
  String
ev5RuntimeUpgradeText =
  "Empirical EV5 runtime check records lane7 non-increasing, lane2 bounded, and the full theta profile with danger shell argmax; theta<1 is a seam gauge, not a theorem."

stressTestBoundaryText :
  String
stressTestBoundaryText =
  "Stress tests can support or falsify the dashiCFD runtime diagnostic, but they do not prove NS-to-EV5 transfer, theta-BKM equivalence, 3D Navier-Stokes regularity, or any Clay claim."

thetaRuntimeProfileText :
  String
thetaRuntimeProfileText =
  "thetaProfileComputable records a runtime seam gauge/profile; thetaDangerShell is the critical-shell argmax over k>=K*, and thetaHighShellDecay remains open/conditional."

thetaRuntimeNonTheoremText :
  String
thetaRuntimeNonTheoremText =
  "Runtime theta is not monotone; theta<1=>continuation is conditional; theta<=>BKM is not proved."

canonicalFourierShellDataPoint :
  FourierShellDataPoint
canonicalFourierShellDataPoint =
  record
    { k =
        zero
    ; t =
        zero
    ; fluxMagnitude =
        zero
    ; dissipation =
        suc zero
    ; dissipationPositive =
        s≤s z≤n
    }

canonicalThetaRatio :
  ThetaRatio
canonicalThetaRatio =
  thetaFromFourierShellData canonicalFourierShellDataPoint

canonicalRuntimeEV5ThetaGate :
  RuntimeEV5ThetaGate
canonicalRuntimeEV5ThetaGate =
  record
    { lane7Before =
        zero
    ; lane7After =
        zero
    ; lane7NonIncreasing =
        z≤n
    ; lane2RuntimeDepth =
        zero
    ; lane2RuntimeCutoff =
        zero
    ; lane2Bounded =
        z≤n
    ; theta =
        canonicalThetaRatio
    ; thetaLessThanOne =
        s≤s z≤n
    }

record DashiCFDThetaRuntimeDiagnosticReceipt : Setω where
  field
    status :
      DashiCFDThetaRuntimeStatus

    statusIsRuntimeDiagnosticOnly :
      status
      ≡
      thetaRuntimeDiagnosticRecorded_noNSProof_noClayPromotion

    importedExperimentPlan :
      ExperimentPlan.NSToEV5DashiCFDExperimentPlanReceipt

    importedExperimentPlanIsCanonical :
      importedExperimentPlan
      ≡
      ExperimentPlan.canonicalNSToEV5DashiCFDExperimentPlanReceipt

    experimentPlanRemainsEvidenceOnly :
      ExperimentPlan.evidenceOnly importedExperimentPlan ≡ true

    experimentPlanDoesNotPromoteClay :
      ExperimentPlan.clayNavierStokesPromoted importedExperimentPlan ≡ false

    runtimeInputs :
      List FourierShellRuntimeInput

    runtimeInputsAreCanonical :
      runtimeInputs ≡ canonicalFourierShellRuntimeInputs

    thetaObservables :
      List ThetaRuntimeObservable

    thetaObservablesAreCanonical :
      thetaObservables ≡ canonicalThetaRuntimeObservables

    thetaFormula :
      String

    thetaFormulaIsCanonical :
      thetaFormula ≡ thetaFormulaText

    sampleFourierShellPoint :
      FourierShellDataPoint

    sampleFourierShellPointIsCanonical :
      sampleFourierShellPoint ≡ canonicalFourierShellDataPoint

    computedTheta :
      ThetaRatio

    computedThetaIsFromFourierShellData :
      computedTheta ≡ thetaFromFourierShellData sampleFourierShellPoint

    thetaProfileComputableFlag :
      Bool

    thetaProfileComputableFlagIsTrue :
      thetaProfileComputableFlag ≡ true

    thetaProfileScope :
      List ThetaRuntimeProfileScope

    thetaProfileScopeIsCanonical :
      thetaProfileScope ≡ canonicalThetaRuntimeProfileScope

    thetaDangerShell :
      Nat

    thetaDangerShellIsCriticalArgmaxOverKStar :
      Bool

    thetaDangerShellIsCriticalArgmaxOverKStarIsTrue :
      thetaDangerShellIsCriticalArgmaxOverKStar ≡ true

    thetaHighShellDecayOpenConditionalFlag :
      Bool

    thetaHighShellDecayOpenConditionalFlagIsTrue :
      thetaHighShellDecayOpenConditionalFlag ≡ true

    empiricalEV5CheckComponents :
      List EmpiricalEV5RuntimeCheckComponent

    empiricalEV5CheckComponentsAreCanonical :
      empiricalEV5CheckComponents
      ≡
      canonicalEmpiricalEV5RuntimeCheckComponents

    runtimeEV5Gate :
      RuntimeEV5ThetaGate

    runtimeEV5GateIsCanonical :
      runtimeEV5Gate ≡ canonicalRuntimeEV5ThetaGate

    lane7RuntimeNonIncreasing :
      lane7After runtimeEV5Gate ≤ lane7Before runtimeEV5Gate

    lane7RuntimeNonIncreasingMatchesGate :
      lane7RuntimeNonIncreasing
      ≡
      RuntimeEV5ThetaGate.lane7NonIncreasing runtimeEV5Gate

    lane2RuntimeBounded :
      lane2RuntimeDepth runtimeEV5Gate ≤ lane2RuntimeCutoff runtimeEV5Gate

    lane2RuntimeBoundedMatchesGate :
      lane2RuntimeBounded
      ≡
      RuntimeEV5ThetaGate.lane2Bounded runtimeEV5Gate

    thetaRuntimeLessThanOne :
      numerator (theta runtimeEV5Gate)
      <
      denominator (theta runtimeEV5Gate)

    thetaRuntimeLessThanOneMatchesGate :
      thetaRuntimeLessThanOne
      ≡
      RuntimeEV5ThetaGate.thetaLessThanOne runtimeEV5Gate

    thetaMonotoneClaimed :
      Bool

    thetaMonotoneClaimedIsFalse :
      thetaMonotoneClaimed ≡ false

    thetaLessThanOneContinuationConditionalFlag :
      Bool

    thetaLessThanOneContinuationConditionalFlagIsTrue :
      thetaLessThanOneContinuationConditionalFlag ≡ true

    thetaBKMEquivalenceProved :
      Bool

    thetaBKMEquivalenceProvedIsFalse :
      thetaBKMEquivalenceProved ≡ false

    ev5RuntimeUpgrade :
      String

    ev5RuntimeUpgradeIsCanonical :
      ev5RuntimeUpgrade ≡ ev5RuntimeUpgradeText

    stressTests :
      List RuntimeStressTest

    stressTestsAreCanonical :
      stressTests ≡ canonicalRuntimeStressTests

    stressTestRoles :
      List RuntimeStressTestRole

    stressTestRolesAreCanonical :
      stressTestRoles ≡ canonicalRuntimeStressTestRoles

    stressTestsCanSupport :
      Bool

    stressTestsCanSupportIsTrue :
      stressTestsCanSupport ≡ true

    stressTestsCanFalsify :
      Bool

    stressTestsCanFalsifyIsTrue :
      stressTestsCanFalsify ≡ true

    stressTestsCanProve :
      Bool

    stressTestsCanProveIsFalse :
      stressTestsCanProve ≡ false

    nsToEV5ProjectionProvedHere :
      Bool

    nsToEV5ProjectionProvedHereIsFalse :
      nsToEV5ProjectionProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    noNSClayPromotion :
      Bool

    noNSClayPromotionIsTrue :
      noNSClayPromotion ≡ true

    proofPromotionTokens :
      List RuntimeProofPromotionToken

    proofPromotionTokensAreEmpty :
      proofPromotionTokens ≡ []

    stressTestBoundary :
      String

    stressTestBoundaryIsCanonical :
      stressTestBoundary ≡ stressTestBoundaryText

    thetaRuntimeProfileBoundary :
      String

    thetaRuntimeProfileBoundaryIsCanonical :
      thetaRuntimeProfileBoundary ≡ thetaRuntimeProfileText

    thetaRuntimeNonTheoremBoundary :
      String

    thetaRuntimeNonTheoremBoundaryIsCanonical :
      thetaRuntimeNonTheoremBoundary ≡ thetaRuntimeNonTheoremText

open DashiCFDThetaRuntimeDiagnosticReceipt public

canonicalDashiCFDThetaRuntimeDiagnosticReceipt :
  DashiCFDThetaRuntimeDiagnosticReceipt
canonicalDashiCFDThetaRuntimeDiagnosticReceipt =
  record
    { status =
        thetaRuntimeDiagnosticRecorded_noNSProof_noClayPromotion
    ; statusIsRuntimeDiagnosticOnly =
        refl
    ; importedExperimentPlan =
        ExperimentPlan.canonicalNSToEV5DashiCFDExperimentPlanReceipt
    ; importedExperimentPlanIsCanonical =
        refl
    ; experimentPlanRemainsEvidenceOnly =
        refl
    ; experimentPlanDoesNotPromoteClay =
        refl
    ; runtimeInputs =
        canonicalFourierShellRuntimeInputs
    ; runtimeInputsAreCanonical =
        refl
    ; thetaObservables =
        canonicalThetaRuntimeObservables
    ; thetaObservablesAreCanonical =
        refl
    ; thetaFormula =
        thetaFormulaText
    ; thetaFormulaIsCanonical =
        refl
    ; sampleFourierShellPoint =
        canonicalFourierShellDataPoint
    ; sampleFourierShellPointIsCanonical =
        refl
    ; computedTheta =
        canonicalThetaRatio
    ; computedThetaIsFromFourierShellData =
        refl
    ; thetaProfileComputableFlag =
        true
    ; thetaProfileComputableFlagIsTrue =
        refl
    ; thetaProfileScope =
        canonicalThetaRuntimeProfileScope
    ; thetaProfileScopeIsCanonical =
        refl
    ; thetaDangerShell =
        zero
    ; thetaDangerShellIsCriticalArgmaxOverKStar =
        true
    ; thetaDangerShellIsCriticalArgmaxOverKStarIsTrue =
        refl
    ; thetaHighShellDecayOpenConditionalFlag =
        true
    ; thetaHighShellDecayOpenConditionalFlagIsTrue =
        refl
    ; empiricalEV5CheckComponents =
        canonicalEmpiricalEV5RuntimeCheckComponents
    ; empiricalEV5CheckComponentsAreCanonical =
        refl
    ; runtimeEV5Gate =
        canonicalRuntimeEV5ThetaGate
    ; runtimeEV5GateIsCanonical =
        refl
    ; lane7RuntimeNonIncreasing =
        z≤n
    ; lane7RuntimeNonIncreasingMatchesGate =
        refl
    ; lane2RuntimeBounded =
        z≤n
    ; lane2RuntimeBoundedMatchesGate =
        refl
    ; thetaRuntimeLessThanOne =
        s≤s z≤n
    ; thetaRuntimeLessThanOneMatchesGate =
        refl
    ; thetaMonotoneClaimed =
        false
    ; thetaMonotoneClaimedIsFalse =
        refl
    ; thetaLessThanOneContinuationConditionalFlag =
        true
    ; thetaLessThanOneContinuationConditionalFlagIsTrue =
        refl
    ; thetaBKMEquivalenceProved =
        false
    ; thetaBKMEquivalenceProvedIsFalse =
        refl
    ; ev5RuntimeUpgrade =
        ev5RuntimeUpgradeText
    ; ev5RuntimeUpgradeIsCanonical =
        refl
    ; stressTests =
        canonicalRuntimeStressTests
    ; stressTestsAreCanonical =
        refl
    ; stressTestRoles =
        canonicalRuntimeStressTestRoles
    ; stressTestRolesAreCanonical =
        refl
    ; stressTestsCanSupport =
        true
    ; stressTestsCanSupportIsTrue =
        refl
    ; stressTestsCanFalsify =
        true
    ; stressTestsCanFalsifyIsTrue =
        refl
    ; stressTestsCanProve =
        false
    ; stressTestsCanProveIsFalse =
        refl
    ; nsToEV5ProjectionProvedHere =
        false
    ; nsToEV5ProjectionProvedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; noNSClayPromotion =
        true
    ; noNSClayPromotionIsTrue =
        refl
    ; proofPromotionTokens =
        []
    ; proofPromotionTokensAreEmpty =
        refl
    ; stressTestBoundary =
        stressTestBoundaryText
    ; stressTestBoundaryIsCanonical =
        refl
    ; thetaRuntimeProfileBoundary =
        thetaRuntimeProfileText
    ; thetaRuntimeProfileBoundaryIsCanonical =
        refl
    ; thetaRuntimeNonTheoremBoundary =
        thetaRuntimeNonTheoremText
    ; thetaRuntimeNonTheoremBoundaryIsCanonical =
        refl
    }

canonicalThetaRuntimeComputesFluxOverDiss :
  computedTheta canonicalDashiCFDThetaRuntimeDiagnosticReceipt
  ≡
  thetaFromFourierShellData
    (sampleFourierShellPoint canonicalDashiCFDThetaRuntimeDiagnosticReceipt)
canonicalThetaRuntimeComputesFluxOverDiss =
  refl

canonicalThetaRuntimeUpgradesEV5Check :
  empiricalEV5CheckComponents canonicalDashiCFDThetaRuntimeDiagnosticReceipt
  ≡
  canonicalEmpiricalEV5RuntimeCheckComponents
canonicalThetaRuntimeUpgradesEV5Check =
  refl

canonicalThetaRuntimeStressTestsDoNotProve :
  stressTestsCanProve canonicalDashiCFDThetaRuntimeDiagnosticReceipt ≡ false
canonicalThetaRuntimeStressTestsDoNotProve =
  refl

canonicalThetaRuntimeNoClayPromotion :
  clayNavierStokesPromoted canonicalDashiCFDThetaRuntimeDiagnosticReceipt
  ≡
  false
canonicalThetaRuntimeNoClayPromotion =
  refl
