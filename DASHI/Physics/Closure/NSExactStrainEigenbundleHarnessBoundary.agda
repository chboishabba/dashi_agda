module DASHI.Physics.Closure.NSExactStrainEigenbundleHarnessBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact-strain eigenbundle harness boundary.
--
-- This receipt records the next local falsification lane for
-- CascadeClosedZeroModeOutputWidth.  The previous tangent-frame probes are
-- diagnostic only: they falsify weak proxy assumptions, but they do not
-- compute the exact Navier-Stokes strain eigenbundle and therefore cannot
-- prove or refute the cascade-closed zero-mode output-width theorem.
--
-- The exact finite-symbol harness must use:
--
--   * Biot-Savart input velocities from divergence-free vorticity data;
--   * the true Leray-projected triadic output;
--   * the strain eigenbundle of the exact finite NS symbol.
--
-- This file is a fail-closed Agda receipt only.  It does not import the
-- heavier exact-symbol modules, does not assert the analytic transfer from
-- finite harness evidence to Navier-Stokes blowup profiles, and keeps every
-- promotion flag false.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Proxy-harness evidence status.

data ProxyHarnessEvidenceRow : Set where
  proxyTangentFrameFalsificationOnly :
    ProxyHarnessEvidenceRow
  triadicWidthProbeDiagnosticOnly :
    ProxyHarnessEvidenceRow
  depthTwoClosureProbeDiagnosticOnly :
    ProxyHarnessEvidenceRow
  leakagePlancherelToyBookkeepingOnly :
    ProxyHarnessEvidenceRow
  proxyFramesNotExactStrainEigenbundle :
    ProxyHarnessEvidenceRow
  noCascadeClosedWidthProofFromProxyEvidence :
    ProxyHarnessEvidenceRow

canonicalProxyHarnessEvidenceRows :
  List ProxyHarnessEvidenceRow
canonicalProxyHarnessEvidenceRows =
  proxyTangentFrameFalsificationOnly
  ∷ triadicWidthProbeDiagnosticOnly
  ∷ depthTwoClosureProbeDiagnosticOnly
  ∷ leakagePlancherelToyBookkeepingOnly
  ∷ proxyFramesNotExactStrainEigenbundle
  ∷ noCascadeClosedWidthProofFromProxyEvidence
  ∷ []

proxyHarnessEvidenceRowCount : Nat
proxyHarnessEvidenceRowCount =
  listLength canonicalProxyHarnessEvidenceRows

proxyHarnessEvidenceRowCountIs6 :
  proxyHarnessEvidenceRowCount ≡ 6
proxyHarnessEvidenceRowCountIs6 =
  refl

------------------------------------------------------------------------
-- Exact finite-symbol harness ingredients.

data ExactStrainHarnessIngredient : Set where
  biotSavartInputVelocityFromVorticity :
    ExactStrainHarnessIngredient
  divergenceFreeInputPolarizations :
    ExactStrainHarnessIngredient
  trueTriadicFrequencyResonance :
    ExactStrainHarnessIngredient
  lerayProjectedTriadicOutput :
    ExactStrainHarnessIngredient
  exactFiniteStrainSymbol :
    ExactStrainHarnessIngredient
  strainEigenbundleOfExactSymbol :
    ExactStrainHarnessIngredient
  zeroModeWidthMeasuredAgainstExactEigenbundle :
    ExactStrainHarnessIngredient

canonicalExactStrainHarnessIngredients :
  List ExactStrainHarnessIngredient
canonicalExactStrainHarnessIngredients =
  biotSavartInputVelocityFromVorticity
  ∷ divergenceFreeInputPolarizations
  ∷ trueTriadicFrequencyResonance
  ∷ lerayProjectedTriadicOutput
  ∷ exactFiniteStrainSymbol
  ∷ strainEigenbundleOfExactSymbol
  ∷ zeroModeWidthMeasuredAgainstExactEigenbundle
  ∷ []

exactStrainHarnessIngredientCount : Nat
exactStrainHarnessIngredientCount =
  listLength canonicalExactStrainHarnessIngredients

exactStrainHarnessIngredientCountIs7 :
  exactStrainHarnessIngredientCount ≡ 7
exactStrainHarnessIngredientCountIs7 =
  refl

data ExactFiniteSymbolComponent : Set where
  inputVorticityHatA :
    ExactFiniteSymbolComponent
  inputVorticityHatB :
    ExactFiniteSymbolComponent
  biotSavartVelocityHatA :
    ExactFiniteSymbolComponent
  biotSavartVelocityHatB :
    ExactFiniteSymbolComponent
  lerayProjectorAtOutput :
    ExactFiniteSymbolComponent
  strainMatrixFromProjectedOutput :
    ExactFiniteSymbolComponent
  maximalStrainEigenline :
    ExactFiniteSymbolComponent

canonicalExactFiniteSymbolComponents :
  List ExactFiniteSymbolComponent
canonicalExactFiniteSymbolComponents =
  inputVorticityHatA
  ∷ inputVorticityHatB
  ∷ biotSavartVelocityHatA
  ∷ biotSavartVelocityHatB
  ∷ lerayProjectorAtOutput
  ∷ strainMatrixFromProjectedOutput
  ∷ maximalStrainEigenline
  ∷ []

exactFiniteSymbolComponentCount : Nat
exactFiniteSymbolComponentCount =
  listLength canonicalExactFiniteSymbolComponents

exactFiniteSymbolComponentCountIs7 :
  exactFiniteSymbolComponentCount ≡ 7
exactFiniteSymbolComponentCountIs7 =
  refl

------------------------------------------------------------------------
-- Harness objective and theorem boundary.

data ExactStrainHarnessObjective : Set where
  replaceProxyTangentFrameWithExactNSStrainEigenbundle :
    ExactStrainHarnessObjective
  computeSingleDepthExactZeroOutputWidth :
    ExactStrainHarnessObjective
  computeDepthTwoExactCascadeContinuation :
    ExactStrainHarnessObjective
  compareProxyWidthAgainstExactEigenbundleWidth :
    ExactStrainHarnessObjective
  recordFalsificationWithoutPromotion :
    ExactStrainHarnessObjective

canonicalExactStrainHarnessObjectives :
  List ExactStrainHarnessObjective
canonicalExactStrainHarnessObjectives =
  replaceProxyTangentFrameWithExactNSStrainEigenbundle
  ∷ computeSingleDepthExactZeroOutputWidth
  ∷ computeDepthTwoExactCascadeContinuation
  ∷ compareProxyWidthAgainstExactEigenbundleWidth
  ∷ recordFalsificationWithoutPromotion
  ∷ []

exactStrainHarnessObjectiveCount : Nat
exactStrainHarnessObjectiveCount =
  listLength canonicalExactStrainHarnessObjectives

exactStrainHarnessObjectiveCountIs5 :
  exactStrainHarnessObjectiveCount ≡ 5
exactStrainHarnessObjectiveCountIs5 =
  refl

data CascadeClosedZeroModeOutputWidthStatus : Set where
  theoremNotProvedByHarnessEvidence :
    CascadeClosedZeroModeOutputWidthStatus
  exactFiniteHarnessStillDiagnostic :
    CascadeClosedZeroModeOutputWidthStatus
  analyticTransferStillRequired :
    CascadeClosedZeroModeOutputWidthStatus
  microlocalDefectMeasureTransferStillRequired :
    CascadeClosedZeroModeOutputWidthStatus
  clayNavierStokesPromotionBlocked :
    CascadeClosedZeroModeOutputWidthStatus

canonicalCascadeClosedWidthStatuses :
  List CascadeClosedZeroModeOutputWidthStatus
canonicalCascadeClosedWidthStatuses =
  theoremNotProvedByHarnessEvidence
  ∷ exactFiniteHarnessStillDiagnostic
  ∷ analyticTransferStillRequired
  ∷ microlocalDefectMeasureTransferStillRequired
  ∷ clayNavierStokesPromotionBlocked
  ∷ []

cascadeClosedWidthStatusCount : Nat
cascadeClosedWidthStatusCount =
  listLength canonicalCascadeClosedWidthStatuses

cascadeClosedWidthStatusCountIs5 :
  cascadeClosedWidthStatusCount ≡ 5
cascadeClosedWidthStatusCountIs5 =
  refl

data ExactStrainHarnessBlocker : Set where
  exactBiotSavartStrainHarnessIsOnlyDiagnostic :
    ExactStrainHarnessBlocker
  missingExactDepthTwoCascadeClosureClassification :
    ExactStrainHarnessBlocker
  missingPositiveOutputWidthTheorem :
    ExactStrainHarnessBlocker
  missingHarnessToFiniteSymbolProofReceipt :
    ExactStrainHarnessBlocker
  missingFiniteSymbolToMicrolocalDefectTransfer :
    ExactStrainHarnessBlocker
  missingAncientProfileAnalyticTransfer :
    ExactStrainHarnessBlocker
  missingNSCriticalResidualNonPositive :
    ExactStrainHarnessBlocker
  missingFullLocalDefectMonotonicity :
    ExactStrainHarnessBlocker
  missingClayNSAuthority :
    ExactStrainHarnessBlocker

canonicalExactStrainHarnessBlockers :
  List ExactStrainHarnessBlocker
canonicalExactStrainHarnessBlockers =
  exactBiotSavartStrainHarnessIsOnlyDiagnostic
  ∷ missingExactDepthTwoCascadeClosureClassification
  ∷ missingPositiveOutputWidthTheorem
  ∷ missingHarnessToFiniteSymbolProofReceipt
  ∷ missingFiniteSymbolToMicrolocalDefectTransfer
  ∷ missingAncientProfileAnalyticTransfer
  ∷ missingNSCriticalResidualNonPositive
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingClayNSAuthority
  ∷ []

exactStrainHarnessBlockerCount : Nat
exactStrainHarnessBlockerCount =
  listLength canonicalExactStrainHarnessBlockers

exactStrainHarnessBlockerCountIs9 :
  exactStrainHarnessBlockerCount ≡ 9
exactStrainHarnessBlockerCountIs9 =
  refl

------------------------------------------------------------------------
-- Promotion guards.

data ExactStrainHarnessPromotion : Set where

exactStrainHarnessPromotionImpossibleHere :
  ExactStrainHarnessPromotion →
  ⊥
exactStrainHarnessPromotionImpossibleHere ()

proxyHarnessProvesCascadeClosedOutputWidth : Bool
proxyHarnessProvesCascadeClosedOutputWidth =
  false

exactHarnessProvesCascadeClosedOutputWidth : Bool
exactHarnessProvesCascadeClosedOutputWidth =
  false

finiteHarnessProvesAnalyticTransfer : Bool
finiteHarnessProvesAnalyticTransfer =
  false

nsCriticalResidualPromoted : Bool
nsCriticalResidualPromoted =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data ExactStrainHarnessBoundaryStatus : Set where
  exactStrainEigenbundleHarnessBoundaryRecorded_noPromotion :
    ExactStrainHarnessBoundaryStatus

exactStrainHarnessSummary : String
exactStrainHarnessSummary =
  "Proxy tangent-frame harnesses are diagnostic/falsification evidence only; the exact NS finite-symbol harness now computes Biot-Savart velocities, Leray-projected triadic output, and the exact strain eigenbundle, but remains diagnostic."

exactStrainHarnessBoundaryText : String
exactStrainHarnessBoundaryText =
  "Harness evidence does not prove CascadeClosedZeroModeOutputWidth.  Exact-strain sampled runs currently expose a near-tautological Family-I zero residual for the recorded criterion, so the positive-width theorem target must be sharpened before finite-symbol proof receipts, microlocal transfer, ancient-profile analytic transfer, residual monotonicity, or external Clay authority can promote."

record NSExactStrainEigenbundleHarnessBoundary : Set where
  field
    status :
      ExactStrainHarnessBoundaryStatus
    statusIsCanonical :
      status
        ≡ exactStrainEigenbundleHarnessBoundaryRecorded_noPromotion
    proxyEvidenceRows :
      List ProxyHarnessEvidenceRow
    proxyEvidenceRowsAreCanonical :
      proxyEvidenceRows ≡ canonicalProxyHarnessEvidenceRows
    proxyEvidenceRowsAreSix :
      proxyHarnessEvidenceRowCount ≡ 6
    exactIngredients :
      List ExactStrainHarnessIngredient
    exactIngredientsAreCanonical :
      exactIngredients ≡ canonicalExactStrainHarnessIngredients
    exactIngredientsAreSeven :
      exactStrainHarnessIngredientCount ≡ 7
    exactFiniteSymbolComponents :
      List ExactFiniteSymbolComponent
    exactFiniteSymbolComponentsAreCanonical :
      exactFiniteSymbolComponents ≡ canonicalExactFiniteSymbolComponents
    exactFiniteSymbolComponentsAreSeven :
      exactFiniteSymbolComponentCount ≡ 7
    objectives :
      List ExactStrainHarnessObjective
    objectivesAreCanonical :
      objectives ≡ canonicalExactStrainHarnessObjectives
    objectivesAreFive :
      exactStrainHarnessObjectiveCount ≡ 5
    statuses :
      List CascadeClosedZeroModeOutputWidthStatus
    statusesAreCanonical :
      statuses ≡ canonicalCascadeClosedWidthStatuses
    statusesAreFive :
      cascadeClosedWidthStatusCount ≡ 5
    blockers :
      List ExactStrainHarnessBlocker
    blockersAreCanonical :
      blockers ≡ canonicalExactStrainHarnessBlockers
    blockersAreNine :
      exactStrainHarnessBlockerCount ≡ 9
    proxyHarnessProvesCascadeClosedOutputWidthIsFalse :
      proxyHarnessProvesCascadeClosedOutputWidth ≡ false
    exactHarnessProvesCascadeClosedOutputWidthIsFalse :
      exactHarnessProvesCascadeClosedOutputWidth ≡ false
    finiteHarnessProvesAnalyticTransferIsFalse :
      finiteHarnessProvesAnalyticTransfer ≡ false
    nsCriticalResidualPromotedIsFalse :
      nsCriticalResidualPromoted ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ exactStrainHarnessSummary
    boundaryText :
      String
    boundaryTextIsCanonical :
      boundaryText ≡ exactStrainHarnessBoundaryText

canonicalNSExactStrainEigenbundleHarnessBoundary :
  NSExactStrainEigenbundleHarnessBoundary
canonicalNSExactStrainEigenbundleHarnessBoundary =
  record
    { status =
        exactStrainEigenbundleHarnessBoundaryRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; proxyEvidenceRows =
        canonicalProxyHarnessEvidenceRows
    ; proxyEvidenceRowsAreCanonical =
        refl
    ; proxyEvidenceRowsAreSix =
        refl
    ; exactIngredients =
        canonicalExactStrainHarnessIngredients
    ; exactIngredientsAreCanonical =
        refl
    ; exactIngredientsAreSeven =
        refl
    ; exactFiniteSymbolComponents =
        canonicalExactFiniteSymbolComponents
    ; exactFiniteSymbolComponentsAreCanonical =
        refl
    ; exactFiniteSymbolComponentsAreSeven =
        refl
    ; objectives =
        canonicalExactStrainHarnessObjectives
    ; objectivesAreCanonical =
        refl
    ; objectivesAreFive =
        refl
    ; statuses =
        canonicalCascadeClosedWidthStatuses
    ; statusesAreCanonical =
        refl
    ; statusesAreFive =
        refl
    ; blockers =
        canonicalExactStrainHarnessBlockers
    ; blockersAreCanonical =
        refl
    ; blockersAreNine =
        refl
    ; proxyHarnessProvesCascadeClosedOutputWidthIsFalse =
        refl
    ; exactHarnessProvesCascadeClosedOutputWidthIsFalse =
        refl
    ; finiteHarnessProvesAnalyticTransferIsFalse =
        refl
    ; nsCriticalResidualPromotedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        exactStrainHarnessSummary
    ; summaryIsCanonical =
        refl
    ; boundaryText =
        exactStrainHarnessBoundaryText
    ; boundaryTextIsCanonical =
        refl
    }
