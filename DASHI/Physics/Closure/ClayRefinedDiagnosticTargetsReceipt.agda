module DASHI.Physics.Closure.ClayRefinedDiagnosticTargetsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayComputedVisualizationSynthesisReceipt
  as Sprint
import DASHI.Physics.Closure.Gate3NestingTaperConditionReceipt as Nesting

------------------------------------------------------------------------
-- Refined diagnostics after re-reading the sprint CSVs.
--
-- The refined calculations separate three hidden issues:
--
--   NS:
--     theta_global is low-shell dominated.  The tail theorem must use
--     theta_tail = sup_{k >= K_diss(nu)} theta(k), plus a low-shell warning.
--
--   YM:
--     beta_abs(C0) = (a + log(2 p C0)) / c_min.  Entropy C0 is load-bearing:
--     any C0 > 1 raises the Balaban beta bridge target.
--
--   Gate 3:
--     the p-adic Kozyrev atom Gram is identity.  The apparent sampler failure
--     is the Archimedean digit-image nesting cross-term.  The target is the
--     Gaussian taper condition that damps parent-child nesting leakage.
--
-- This is a diagnostics/target receipt only.  It does not prove PAWOTG,
-- Balaban transfer, NS danger-shell preservation, Gate 3 closure, YM mass
-- gap, NS regularity, or Clay.

data ClayRefinedDiagnosticStatus : Set where
  refinedDiagnosticsRecorded_failClosed :
    ClayRefinedDiagnosticStatus

data RefinedDiagnosticArtifact : Set where
  nsThetaTailRestrictedCSV :
    RefinedDiagnosticArtifact

  ymC0ThresholdSensitivityCSV :
    RefinedDiagnosticArtifact

  gate3SamplerQualityCSV :
    RefinedDiagnosticArtifact

canonicalRefinedDiagnosticArtifacts :
  List RefinedDiagnosticArtifact
canonicalRefinedDiagnosticArtifacts =
  nsThetaTailRestrictedCSV
  ∷ ymC0ThresholdSensitivityCSV
  ∷ gate3SamplerQualityCSV
  ∷ []

data RefinedDiagnosticTarget : Set where
  tailRestrictedThetaBarrier :
    RefinedDiagnosticTarget

  lowShellWarningSeparatesGlobalFromTailTheta :
    RefinedDiagnosticTarget

  ymEntropyConstantSensitivity :
    RefinedDiagnosticTarget

  archimedeanNestingTaperPAWOTGQuality :
    RefinedDiagnosticTarget

canonicalRefinedDiagnosticTargets :
  List RefinedDiagnosticTarget
canonicalRefinedDiagnosticTargets =
  tailRestrictedThetaBarrier
  ∷ lowShellWarningSeparatesGlobalFromTailTheta
  ∷ ymEntropyConstantSensitivity
  ∷ archimedeanNestingTaperPAWOTGQuality
  ∷ []

data RefinedDiagnosticNonClaim : Set where
  thetaTailPassOnSampleDoesNotProveNS :
    RefinedDiagnosticNonClaim

  c0SweepDoesNotProveBalabanBridge :
    RefinedDiagnosticNonClaim

  archimedeanNestingDiagnosticDoesNotProveGate3Impossible :
    RefinedDiagnosticNonClaim

  refinedDiagnosticsDoNotPromoteClay :
    RefinedDiagnosticNonClaim

canonicalRefinedDiagnosticNonClaims :
  List RefinedDiagnosticNonClaim
canonicalRefinedDiagnosticNonClaims =
  thetaTailPassOnSampleDoesNotProveNS
  ∷ c0SweepDoesNotProveBalabanBridge
  ∷ archimedeanNestingDiagnosticDoesNotProveGate3Impossible
  ∷ refinedDiagnosticsDoNotPromoteClay
  ∷ []

data ClayRefinedDiagnosticPromotion : Set where

clayRefinedDiagnosticPromotionImpossibleHere :
  ClayRefinedDiagnosticPromotion →
  ⊥
clayRefinedDiagnosticPromotionImpossibleHere ()

-- Fixed-point numerical readings.

nsTailRestrictedKdiss :
  Nat
nsTailRestrictedKdiss =
  32

nsSmoothThetaTailMillion :
  Nat
nsSmoothThetaTailMillion =
  3994

nsKolmogorovThetaTailMillion :
  Nat
nsKolmogorovThetaTailMillion =
  318838

nsNearCriticalThetaTailMillion :
  Nat
nsNearCriticalThetaTailMillion =
  2015855

nsRoughThetaTailMillion :
  Nat
nsRoughThetaTailMillion =
  2763042

ymC0OneStrictBetaHundredThousand :
  Nat
ymC0OneStrictBetaHundredThousand =
  1297131

ymC0HalfStrictBetaHundredThousand :
  Nat
ymC0HalfStrictBetaHundredThousand =
  1010707

ymC0ThreeQuarterStrictBetaHundredThousand :
  Nat
ymC0ThreeQuarterStrictBetaHundredThousand =
  1178254

ymC0OnePointTwoFiveStrictBetaHundredThousand :
  Nat
ymC0OnePointTwoFiveStrictBetaHundredThousand =
  1389339

gate3GershgorinPassCount :
  Nat
gate3GershgorinPassCount =
  zero

nsTailRestrictedStatement :
  String
nsTailRestrictedStatement =
  "NS refined diagnostic: theta_global is low-k dominated at danger shell k=2, so the tail theorem must use theta_tail = sup_{k >= K_diss(nu)} theta(k).  In the current sweep, smooth and Kolmogorov pass theta_tail<1, near-critical and rough fail, and inviscid has no sampled k>=K_diss row."

ymC0SensitivityStatement :
  String
ymC0SensitivityStatement =
  "YM refined diagnostic: beta_abs(C0) = (a + log(2 p C0)) / c_min, so the entropy constant C0 is load-bearing.  C0=0.5 gives beta_abs=10.1071, C0=0.75 gives 11.7825, C0=1 gives 12.9713, and C0=1.25 gives 13.8934."

gate3SamplerQualityStatement :
  String
gate3SamplerQualityStatement =
  "Gate3 refined diagnostic: Kozyrev atoms are orthogonal in L2(Q_p), so the p-adic Gram has A_N=B_N=1 and mu_N=0.  The current Archimedean sweep reports parent-child nesting leakage; PAWOTG is the Gaussian taper condition that must damp it."

record ClayRefinedDiagnosticTargetsReceipt : Setω where
  field
    status :
      ClayRefinedDiagnosticStatus

    statusIsFailClosed :
      status ≡ refinedDiagnosticsRecorded_failClosed

    sprintReceipt :
      Sprint.ClayComputedVisualizationSynthesisReceipt

    sprintKeepsClayFalse :
      Sprint.clayPromoted sprintReceipt ≡ false

    nestingReceipt :
      Nesting.Gate3NestingTaperConditionReceipt

    nestingRootIsArchimedean :
      Nesting.archimedeanNestingIsRootProblem nestingReceipt ≡ true

    nestingNoGate3Promotion :
      Nesting.gate3Promoted nestingReceipt ≡ false

    artifacts :
      List RefinedDiagnosticArtifact

    artifactsAreCanonical :
      artifacts ≡ canonicalRefinedDiagnosticArtifacts

    targets :
      List RefinedDiagnosticTarget

    targetsAreCanonical :
      targets ≡ canonicalRefinedDiagnosticTargets

    nsKdiss :
      Nat

    nsKdissIs32 :
      nsKdiss ≡ nsTailRestrictedKdiss

    nsSmoothTailTheta :
      Nat

    nsSmoothTailThetaIs3994Million :
      nsSmoothTailTheta ≡ nsSmoothThetaTailMillion

    nsKolmogorovTailTheta :
      Nat

    nsKolmogorovTailThetaIs318838Million :
      nsKolmogorovTailTheta ≡ nsKolmogorovThetaTailMillion

    nsNearCriticalTailTheta :
      Nat

    nsNearCriticalTailThetaIs2015855Million :
      nsNearCriticalTailTheta ≡ nsNearCriticalThetaTailMillion

    nsRoughTailTheta :
      Nat

    nsRoughTailThetaIs2763042Million :
      nsRoughTailTheta ≡ nsRoughThetaTailMillion

    nsSmoothTailPass :
      Bool

    nsSmoothTailPassIsTrue :
      nsSmoothTailPass ≡ true

    nsKolmogorovTailPass :
      Bool

    nsKolmogorovTailPassIsTrue :
      nsKolmogorovTailPass ≡ true

    nsNearCriticalTailPass :
      Bool

    nsNearCriticalTailPassIsFalse :
      nsNearCriticalTailPass ≡ false

    nsRoughTailPass :
      Bool

    nsRoughTailPassIsFalse :
      nsRoughTailPass ≡ false

    lowShellWarningRequired :
      Bool

    lowShellWarningRequiredIsTrue :
      lowShellWarningRequired ≡ true

    ymC0OneStrictBeta :
      Nat

    ymC0OneStrictBetaIs1297131HundredThousand :
      ymC0OneStrictBeta ≡ ymC0OneStrictBetaHundredThousand

    ymC0HalfStrictBeta :
      Nat

    ymC0HalfStrictBetaIs1010707HundredThousand :
      ymC0HalfStrictBeta ≡ ymC0HalfStrictBetaHundredThousand

    ymC0ThreeQuarterStrictBeta :
      Nat

    ymC0ThreeQuarterStrictBetaIs1178254HundredThousand :
      ymC0ThreeQuarterStrictBeta
      ≡
      ymC0ThreeQuarterStrictBetaHundredThousand

    ymC0OnePointTwoFiveStrictBeta :
      Nat

    ymC0OnePointTwoFiveStrictBetaIs1389339HundredThousand :
      ymC0OnePointTwoFiveStrictBeta
      ≡
      ymC0OnePointTwoFiveStrictBetaHundredThousand

    ymC0IsLoadBearing :
      Bool

    ymC0IsLoadBearingIsTrue :
      ymC0IsLoadBearing ≡ true

    gate3GershgorinPassingRows :
      Nat

    gate3GershgorinPassingRowsIsZero :
      gate3GershgorinPassingRows ≡ gate3GershgorinPassCount

    gate3CurrentSamplerClustered :
      Bool

    gate3CurrentSamplerClusteredIsTrue :
      gate3CurrentSamplerClustered ≡ true

    gate3PAdicAtomFailure :
      Bool

    gate3PAdicAtomFailureIsFalse :
      gate3PAdicAtomFailure ≡ false

    gate3ArchimedeanNestingRoot :
      Bool

    gate3ArchimedeanNestingRootIsTrue :
      gate3ArchimedeanNestingRoot ≡ true

    nsStatement :
      String

    nsStatementIsCanonical :
      nsStatement ≡ nsTailRestrictedStatement

    ymStatement :
      String

    ymStatementIsCanonical :
      ymStatement ≡ ymC0SensitivityStatement

    gate3Statement :
      String

    gate3StatementIsCanonical :
      gate3Statement ≡ gate3SamplerQualityStatement

    nonClaims :
      List RefinedDiagnosticNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalRefinedDiagnosticNonClaims

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List ClayRefinedDiagnosticPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ClayRefinedDiagnosticPromotion →
      ⊥

open ClayRefinedDiagnosticTargetsReceipt public

canonicalClayRefinedDiagnosticTargetsReceipt :
  ClayRefinedDiagnosticTargetsReceipt
canonicalClayRefinedDiagnosticTargetsReceipt =
  record
    { status =
        refinedDiagnosticsRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; sprintReceipt =
        Sprint.canonicalClayComputedVisualizationSynthesisReceipt
    ; sprintKeepsClayFalse =
        refl
    ; nestingReceipt =
        Nesting.canonicalGate3NestingTaperConditionReceipt
    ; nestingRootIsArchimedean =
        refl
    ; nestingNoGate3Promotion =
        refl
    ; artifacts =
        canonicalRefinedDiagnosticArtifacts
    ; artifactsAreCanonical =
        refl
    ; targets =
        canonicalRefinedDiagnosticTargets
    ; targetsAreCanonical =
        refl
    ; nsKdiss =
        nsTailRestrictedKdiss
    ; nsKdissIs32 =
        refl
    ; nsSmoothTailTheta =
        nsSmoothThetaTailMillion
    ; nsSmoothTailThetaIs3994Million =
        refl
    ; nsKolmogorovTailTheta =
        nsKolmogorovThetaTailMillion
    ; nsKolmogorovTailThetaIs318838Million =
        refl
    ; nsNearCriticalTailTheta =
        nsNearCriticalThetaTailMillion
    ; nsNearCriticalTailThetaIs2015855Million =
        refl
    ; nsRoughTailTheta =
        nsRoughThetaTailMillion
    ; nsRoughTailThetaIs2763042Million =
        refl
    ; nsSmoothTailPass =
        true
    ; nsSmoothTailPassIsTrue =
        refl
    ; nsKolmogorovTailPass =
        true
    ; nsKolmogorovTailPassIsTrue =
        refl
    ; nsNearCriticalTailPass =
        false
    ; nsNearCriticalTailPassIsFalse =
        refl
    ; nsRoughTailPass =
        false
    ; nsRoughTailPassIsFalse =
        refl
    ; lowShellWarningRequired =
        true
    ; lowShellWarningRequiredIsTrue =
        refl
    ; ymC0OneStrictBeta =
        ymC0OneStrictBetaHundredThousand
    ; ymC0OneStrictBetaIs1297131HundredThousand =
        refl
    ; ymC0HalfStrictBeta =
        ymC0HalfStrictBetaHundredThousand
    ; ymC0HalfStrictBetaIs1010707HundredThousand =
        refl
    ; ymC0ThreeQuarterStrictBeta =
        ymC0ThreeQuarterStrictBetaHundredThousand
    ; ymC0ThreeQuarterStrictBetaIs1178254HundredThousand =
        refl
    ; ymC0OnePointTwoFiveStrictBeta =
        ymC0OnePointTwoFiveStrictBetaHundredThousand
    ; ymC0OnePointTwoFiveStrictBetaIs1389339HundredThousand =
        refl
    ; ymC0IsLoadBearing =
        true
    ; ymC0IsLoadBearingIsTrue =
        refl
    ; gate3GershgorinPassingRows =
        gate3GershgorinPassCount
    ; gate3GershgorinPassingRowsIsZero =
        refl
    ; gate3CurrentSamplerClustered =
        true
    ; gate3CurrentSamplerClusteredIsTrue =
        refl
    ; gate3PAdicAtomFailure =
        false
    ; gate3PAdicAtomFailureIsFalse =
        refl
    ; gate3ArchimedeanNestingRoot =
        true
    ; gate3ArchimedeanNestingRootIsTrue =
        refl
    ; nsStatement =
        nsTailRestrictedStatement
    ; nsStatementIsCanonical =
        refl
    ; ymStatement =
        ymC0SensitivityStatement
    ; ymStatementIsCanonical =
        refl
    ; gate3Statement =
        gate3SamplerQualityStatement
    ; gate3StatementIsCanonical =
        refl
    ; nonClaims =
        canonicalRefinedDiagnosticNonClaims
    ; nonClaimsAreCanonical =
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
        clayRefinedDiagnosticPromotionImpossibleHere
    }

canonicalClayRefinedDiagnosticTargetsNoClay :
  clayPromoted canonicalClayRefinedDiagnosticTargetsReceipt ≡ false
canonicalClayRefinedDiagnosticTargetsNoClay =
  refl
