module DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ym_killing_boundary_self_adjointness_proxy_harness.py
--
-- The harness is a deterministic finite-matrix diagnostic for the
-- Killing/full-degree Bruhat-Tits boundary convention.  It checks synthetic
-- good regimes against synthetic bad regimes for finite-form symmetry,
-- orthogonal quotient projection, gauge-null leakage, quotient-domain
-- stability, and positive quotient spectral margin.
--
-- This module is a receipt only.  It does not prove YM-1/Killing boundary
-- self-adjointness, Hamiltonian domination, reflection positivity, OS
-- transfer, continuum no-spectral-pollution, YM Clay, or terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract
  as DomainContract
import DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary
  as SpectralBudget

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Harness identity and run configuration.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ym_killing_boundary_self_adjointness_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ym_killing_boundary_self_adjointness_proxy_harness.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ym_killing_boundary_self_adjointness_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_killing_boundary_self_adjointness_proxy_diagnostic_only"

runCommandText : String
runCommandText =
  "python scripts/ym_killing_boundary_self_adjointness_proxy_harness.py --dimension 6 --quotient-dimension 4 --sweeps 8 --json-output outputs/ym_killing_boundary_self_adjointness_proxy_harness.json --json"

manifestCommandText : String
manifestCommandText =
  "python scripts/ym_killing_boundary_self_adjointness_proxy_harness.py --dimension 6 --quotient-dimension 4 --sweeps 8 --json-output outputs/local_clay_harness_manifest_children/ym_killing_boundary_self_adjointness_proxy_smoke.json --json"

defaultParameterText : String
defaultParameterText =
  "dimension=6, quotient_dimension=4, sweeps=8, tolerance=1e-9, spectral_margin_floor=0.18, leakage_floor=1e-9"

claimScopeText : String
claimScopeText =
  "finite Killing-boundary self-adjointness diagnostic proxy only"

------------------------------------------------------------------------
-- Imported support surfaces.

domainContractReference : String
domainContractReference =
  "DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract"

spectralBudgetReference : String
spectralBudgetReference =
  "DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary"

importsObserved : Bool
importsObserved =
  true

importsObservedIsTrue :
  importsObserved ≡ true
importsObservedIsTrue =
  refl

importedDomainContractTheoremStillOpen :
  DomainContract.status
    DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  DomainContract.domainContractRecordedTheoremStillOpen
importedDomainContractTheoremStillOpen =
  refl

importedDomainContractSelfAdjointnessStillFalse :
  DomainContract.selfAdjointQuotientHamiltonianProvedField
    DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
importedDomainContractSelfAdjointnessStillFalse =
  DomainContract.canonicalKillingBoundaryDomainSelfAdjointStillFalse

importedDomainContractDominationStillFalse :
  DomainContract.hamiltonianDominationProvedField
    DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
importedDomainContractDominationStillFalse =
  DomainContract.canonicalKillingBoundaryDomainDominationStillFalse

importedDomainContractOSTransferStillFalse :
  DomainContract.osContinuumTransferProvedField
    DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
importedDomainContractOSTransferStillFalse =
  refl

importedDomainContractYMClayStillFalse :
  DomainContract.ymClayPromotedField
    DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
importedDomainContractYMClayStillFalse =
  DomainContract.canonicalKillingBoundaryDomainYMClayStillFalse

importedDomainContractTerminalStillFalse :
  DomainContract.terminalPromotionField
    DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
importedDomainContractTerminalStillFalse =
  DomainContract.canonicalKillingBoundaryDomainTerminalStillFalse

importedSpectralBudgetDominationStillFalse :
  SpectralBudget.hamiltonianDominationProved
    SpectralBudget.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedSpectralBudgetDominationStillFalse =
  SpectralBudget.hamiltonianDominationProvedIsFalse

importedSpectralBudgetOSStillFalse :
  SpectralBudget.osContinuumTransferProved
    SpectralBudget.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedSpectralBudgetOSStillFalse =
  SpectralBudget.osContinuumTransferProvedIsFalse

importedSpectralBudgetNoPollutionStillFalse :
  SpectralBudget.noSpectralPollutionProved
    SpectralBudget.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedSpectralBudgetNoPollutionStillFalse =
  SpectralBudget.noSpectralPollutionProvedIsFalse

importedSpectralBudgetYMClayStillFalse :
  SpectralBudget.ymClayPromoted
    SpectralBudget.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedSpectralBudgetYMClayStillFalse =
  SpectralBudget.ymClayPromotedIsFalse

------------------------------------------------------------------------
-- Harness fields and checked regimes.

data YMKillingBoundarySelfAdjointnessHarnessField : Set where
  harnessIdentityField :
    YMKillingBoundarySelfAdjointnessHarnessField

  outputPathField :
    YMKillingBoundarySelfAdjointnessHarnessField

  manifestChildPathField :
    YMKillingBoundarySelfAdjointnessHarnessField

  parameterField :
    YMKillingBoundarySelfAdjointnessHarnessField

  importedDomainContractField :
    YMKillingBoundarySelfAdjointnessHarnessField

  importedSpectralBudgetField :
    YMKillingBoundarySelfAdjointnessHarnessField

  finiteFormSymmetryCheckField :
    YMKillingBoundarySelfAdjointnessHarnessField

  quotientProjectionCheckField :
    YMKillingBoundarySelfAdjointnessHarnessField

  gaugeNullLeakageCheckField :
    YMKillingBoundarySelfAdjointnessHarnessField

  quotientDomainStabilityCheckField :
    YMKillingBoundarySelfAdjointnessHarnessField

  spectralMarginCheckField :
    YMKillingBoundarySelfAdjointnessHarnessField

  goodRegimeField :
    YMKillingBoundarySelfAdjointnessHarnessField

  badRegimeField :
    YMKillingBoundarySelfAdjointnessHarnessField

  theoremFlagField :
    YMKillingBoundarySelfAdjointnessHarnessField

  promotionFlagField :
    YMKillingBoundarySelfAdjointnessHarnessField

canonicalHarnessFields :
  List YMKillingBoundarySelfAdjointnessHarnessField
canonicalHarnessFields =
  harnessIdentityField
  ∷ outputPathField
  ∷ manifestChildPathField
  ∷ parameterField
  ∷ importedDomainContractField
  ∷ importedSpectralBudgetField
  ∷ finiteFormSymmetryCheckField
  ∷ quotientProjectionCheckField
  ∷ gaugeNullLeakageCheckField
  ∷ quotientDomainStabilityCheckField
  ∷ spectralMarginCheckField
  ∷ goodRegimeField
  ∷ badRegimeField
  ∷ theoremFlagField
  ∷ promotionFlagField
  ∷ []

harnessFieldCount : Nat
harnessFieldCount =
  listCount canonicalHarnessFields

harnessFieldCountIs15 :
  harnessFieldCount ≡ 15
harnessFieldCountIs15 =
  refl

data YMKillingBoundaryRegimeKind : Set where
  goodExpectedPassRegime :
    YMKillingBoundaryRegimeKind

  badExpectedFailRegime :
    YMKillingBoundaryRegimeKind

expectedPassForKind :
  YMKillingBoundaryRegimeKind →
  Bool
expectedPassForKind goodExpectedPassRegime =
  true
expectedPassForKind badExpectedFailRegime =
  false

record YMKillingBoundaryRegimeReceipt : Set where
  field
    regimeName :
      String

    kind :
      YMKillingBoundaryRegimeKind

    expectedPass :
      Bool

    expectedPassMatchesKind :
      expectedPass ≡ expectedPassForKind kind

    diagnosticMeaning :
      String

open YMKillingBoundaryRegimeReceipt public

killingFullDegreeBoundaryRegime :
  YMKillingBoundaryRegimeReceipt
killingFullDegreeBoundaryRegime =
  record
    { regimeName =
        "killing_full_degree_boundary"
    ; kind =
        goodExpectedPassRegime
    ; expectedPass =
        true
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "symmetric full-degree Killing boundary form with stable orthogonal gauge quotient"
    }

killingHolonomyBufferedBoundaryRegime :
  YMKillingBoundaryRegimeReceipt
killingHolonomyBufferedBoundaryRegime =
  record
    { regimeName =
        "killing_holonomy_buffered_boundary"
    ; kind =
        goodExpectedPassRegime
    ; expectedPass =
        true
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "Killing boundary form with holonomy buffer and positive quotient spectral margin"
    }

asymmetricBoundaryFormRegime :
  YMKillingBoundaryRegimeReceipt
asymmetricBoundaryFormRegime =
  record
    { regimeName =
        "asymmetric_boundary_form"
    ; kind =
        badExpectedFailRegime
    ; expectedPass =
        false
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "boundary form loses finite-form and quotient-block symmetry"
    }

gaugeNullLeakingBoundaryRegime :
  YMKillingBoundaryRegimeReceipt
gaugeNullLeakingBoundaryRegime =
  record
    { regimeName =
        "gauge_null_leaking_boundary"
    ; kind =
        badExpectedFailRegime
    ; expectedPass =
        false
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "boundary form leaks into gauge-null directions and breaks quotient-domain stability"
    }

inducedBallSpectralCollapseBoundaryRegime :
  YMKillingBoundaryRegimeReceipt
inducedBallSpectralCollapseBoundaryRegime =
  record
    { regimeName =
        "induced_ball_spectral_collapse_boundary"
    ; kind =
        badExpectedFailRegime
    ; expectedPass =
        false
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "induced-ball truncation collapses the quotient spectral margin"
    }

nonorthogonalGaugeProjectionBoundaryRegime :
  YMKillingBoundaryRegimeReceipt
nonorthogonalGaugeProjectionBoundaryRegime =
  record
    { regimeName =
        "nonorthogonal_gauge_projection_boundary"
    ; kind =
        badExpectedFailRegime
    ; expectedPass =
        false
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "nonorthogonal projection violates the gauge quotient domain contract"
    }

canonicalGoodRegimes :
  List YMKillingBoundaryRegimeReceipt
canonicalGoodRegimes =
  killingFullDegreeBoundaryRegime
  ∷ killingHolonomyBufferedBoundaryRegime
  ∷ []

canonicalBadRegimes :
  List YMKillingBoundaryRegimeReceipt
canonicalBadRegimes =
  asymmetricBoundaryFormRegime
  ∷ gaugeNullLeakingBoundaryRegime
  ∷ inducedBallSpectralCollapseBoundaryRegime
  ∷ nonorthogonalGaugeProjectionBoundaryRegime
  ∷ []

goodRegimeCount : Nat
goodRegimeCount =
  listCount canonicalGoodRegimes

badRegimeCount : Nat
badRegimeCount =
  listCount canonicalBadRegimes

goodRegimeCountIs2 :
  goodRegimeCount ≡ 2
goodRegimeCountIs2 =
  refl

badRegimeCountIs4 :
  badRegimeCount ≡ 4
badRegimeCountIs4 =
  refl

------------------------------------------------------------------------
-- Deterministic smoke values observed in the JSON receipt.

ok_observed : Bool
ok_observed =
  true

diagnostic_only : Bool
diagnostic_only =
  true

promotion : Bool
promotion =
  false

row_count : Nat
row_count =
  48

good_row_count : Nat
good_row_count =
  16

good_rows_passed : Nat
good_rows_passed =
  16

bad_row_count : Nat
bad_row_count =
  32

bad_rows_failed : Nat
bad_rows_failed =
  32

classification_accuracy_text : String
classification_accuracy_text =
  "1.0"

min_good_spectral_margin_text : String
min_good_spectral_margin_text =
  "0.9567817387135332"

min_bad_spectral_margin_text : String
min_bad_spectral_margin_text =
  "0.0"

max_good_gauge_null_leakage_text : String
max_good_gauge_null_leakage_text =
  "0.0"

max_bad_gauge_null_leakage_text : String
max_bad_gauge_null_leakage_text =
  "0.109"

max_good_symmetry_defect_text : String
max_good_symmetry_defect_text =
  "0.0"

max_bad_symmetry_defect_text : String
max_bad_symmetry_defect_text =
  "0.21000000000000002"

ok_observed_is_true :
  ok_observed ≡ true
ok_observed_is_true =
  refl

diagnostic_only_is_true :
  diagnostic_only ≡ true
diagnostic_only_is_true =
  refl

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

rowCountIsFortyEight :
  row_count ≡ 48
rowCountIsFortyEight =
  refl

goodRowCountIsSixteen :
  good_row_count ≡ 16
goodRowCountIsSixteen =
  refl

goodRowsPassedIsSixteen :
  good_rows_passed ≡ 16
goodRowsPassedIsSixteen =
  refl

badRowCountIsThirtyTwo :
  bad_row_count ≡ 32
badRowCountIsThirtyTwo =
  refl

badRowsFailedIsThirtyTwo :
  bad_rows_failed ≡ 32
badRowsFailedIsThirtyTwo =
  refl

------------------------------------------------------------------------
-- Non-claim gates.

ym1KillingBoundarySelfAdjointnessProved : Bool
ym1KillingBoundarySelfAdjointnessProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

reflectionPositiveTransferProved : Bool
reflectionPositiveTransferProved =
  false

osTransferProved : Bool
osTransferProved =
  false

continuumGapProved : Bool
continuumGapProved =
  false

continuumNoSpectralPollutionProved : Bool
continuumNoSpectralPollutionProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

ym1KillingBoundarySelfAdjointnessProvedIsFalse :
  ym1KillingBoundarySelfAdjointnessProved ≡ false
ym1KillingBoundarySelfAdjointnessProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

reflectionPositiveTransferProvedIsFalse :
  reflectionPositiveTransferProved ≡ false
reflectionPositiveTransferProvedIsFalse =
  refl

osTransferProvedIsFalse :
  osTransferProved ≡ false
osTransferProvedIsFalse =
  refl

continuumGapProvedIsFalse :
  continuumGapProved ≡ false
continuumGapProvedIsFalse =
  refl

continuumNoSpectralPollutionProvedIsFalse :
  continuumNoSpectralPollutionProved ≡ false
continuumNoSpectralPollutionProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

data YMKillingBoundaryProxyNonClaimBoundary : Set where
  diagnosticOnlyNotYM1SelfAdjointnessProof :
    YMKillingBoundaryProxyNonClaimBoundary

  diagnosticOnlyNotHamiltonianDominationProof :
    YMKillingBoundaryProxyNonClaimBoundary

  diagnosticOnlyNotReflectionPositiveTransferProof :
    YMKillingBoundaryProxyNonClaimBoundary

  diagnosticOnlyNotOSTransferProof :
    YMKillingBoundaryProxyNonClaimBoundary

  diagnosticOnlyNotContinuumGapProof :
    YMKillingBoundaryProxyNonClaimBoundary

  diagnosticOnlyNotYMClayPromotion :
    YMKillingBoundaryProxyNonClaimBoundary

canonicalNonClaims :
  List YMKillingBoundaryProxyNonClaimBoundary
canonicalNonClaims =
  diagnosticOnlyNotYM1SelfAdjointnessProof
  ∷ diagnosticOnlyNotHamiltonianDominationProof
  ∷ diagnosticOnlyNotReflectionPositiveTransferProof
  ∷ diagnosticOnlyNotOSTransferProof
  ∷ diagnosticOnlyNotContinuumGapProof
  ∷ diagnosticOnlyNotYMClayPromotion
  ∷ []

nonClaimCount : Nat
nonClaimCount =
  listCount canonicalNonClaims

nonClaimCountIs6 :
  nonClaimCount ≡ 6
nonClaimCountIs6 =
  refl

------------------------------------------------------------------------
-- Canonical receipt record.

record YMKillingBoundarySelfAdjointnessProxyHarnessResult : Set where
  field
    sourceHarness :
      String

    directJsonReceipt :
      String

    manifestJsonReceipt :
      String

    scope :
      String

    parameterSummary :
      String

    fields :
      List YMKillingBoundarySelfAdjointnessHarnessField

    goodRegimes :
      List YMKillingBoundaryRegimeReceipt

    badRegimes :
      List YMKillingBoundaryRegimeReceipt

    okObserved :
      Bool

    diagnosticOnly :
      Bool

    promotionFlag :
      Bool

    rowsObserved :
      Nat

    goodRowsObserved :
      Nat

    goodRowsPassing :
      Nat

    badRowsObserved :
      Nat

    badRowsFailing :
      Nat

    classificationAccuracy :
      String

    minGoodSpectralMargin :
      String

    maxBadGaugeNullLeakage :
      String

    nonClaims :
      List YMKillingBoundaryProxyNonClaimBoundary

    okObservedIsTrue :
      okObserved ≡ true

    diagnosticOnlyIsTrue :
      diagnosticOnly ≡ true

    promotionFlagIsFalse :
      promotionFlag ≡ false

    rowsObservedIsFortyEight :
      rowsObserved ≡ 48

    goodRowsObservedIsSixteen :
      goodRowsObserved ≡ 16

    goodRowsPassingIsSixteen :
      goodRowsPassing ≡ 16

    badRowsObservedIsThirtyTwo :
      badRowsObserved ≡ 32

    badRowsFailingIsThirtyTwo :
      badRowsFailing ≡ 32

    ym1StillOpen :
      ym1KillingBoundarySelfAdjointnessProved ≡ false

    dominationStillOpen :
      hamiltonianDominationProved ≡ false

    osTransferStillOpen :
      osTransferProved ≡ false

    continuumGapStillOpen :
      continuumGapProved ≡ false

    ymClayStillFalse :
      ymClayPromoted ≡ false

open YMKillingBoundarySelfAdjointnessProxyHarnessResult public

canonicalYMKillingBoundarySelfAdjointnessProxyHarnessResult :
  YMKillingBoundarySelfAdjointnessProxyHarnessResult
canonicalYMKillingBoundarySelfAdjointnessProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; directJsonReceipt =
        jsonReceiptPath
    ; manifestJsonReceipt =
        manifestChildReceiptPath
    ; scope =
        receiptScope
    ; parameterSummary =
        defaultParameterText
    ; fields =
        canonicalHarnessFields
    ; goodRegimes =
        canonicalGoodRegimes
    ; badRegimes =
        canonicalBadRegimes
    ; okObserved =
        ok_observed
    ; diagnosticOnly =
        diagnostic_only
    ; promotionFlag =
        promotion
    ; rowsObserved =
        row_count
    ; goodRowsObserved =
        good_row_count
    ; goodRowsPassing =
        good_rows_passed
    ; badRowsObserved =
        bad_row_count
    ; badRowsFailing =
        bad_rows_failed
    ; classificationAccuracy =
        classification_accuracy_text
    ; minGoodSpectralMargin =
        min_good_spectral_margin_text
    ; maxBadGaugeNullLeakage =
        max_bad_gauge_null_leakage_text
    ; nonClaims =
        canonicalNonClaims
    ; okObservedIsTrue =
        refl
    ; diagnosticOnlyIsTrue =
        refl
    ; promotionFlagIsFalse =
        refl
    ; rowsObservedIsFortyEight =
        refl
    ; goodRowsObservedIsSixteen =
        refl
    ; goodRowsPassingIsSixteen =
        refl
    ; badRowsObservedIsThirtyTwo =
        refl
    ; badRowsFailingIsThirtyTwo =
        refl
    ; ym1StillOpen =
        refl
    ; dominationStillOpen =
        refl
    ; osTransferStillOpen =
        refl
    ; continuumGapStillOpen =
        refl
    ; ymClayStillFalse =
        refl
    }

canonicalKillingBoundaryProxyPromotionFalse :
  promotionFlag canonicalYMKillingBoundarySelfAdjointnessProxyHarnessResult
  ≡
  false
canonicalKillingBoundaryProxyPromotionFalse =
  refl

canonicalKillingBoundaryProxyDiagnosticOnlyTrue :
  diagnosticOnly canonicalYMKillingBoundarySelfAdjointnessProxyHarnessResult
  ≡
  true
canonicalKillingBoundaryProxyDiagnosticOnlyTrue =
  refl

canonicalKillingBoundaryProxyYM1StillFalse :
  ym1KillingBoundarySelfAdjointnessProved ≡ false
canonicalKillingBoundaryProxyYM1StillFalse =
  refl

canonicalKillingBoundaryProxyDominationStillFalse :
  hamiltonianDominationProved ≡ false
canonicalKillingBoundaryProxyDominationStillFalse =
  refl

canonicalKillingBoundaryProxyOSStillFalse :
  osTransferProved ≡ false
canonicalKillingBoundaryProxyOSStillFalse =
  refl

canonicalKillingBoundaryProxyContinuumGapStillFalse :
  continuumGapProved ≡ false
canonicalKillingBoundaryProxyContinuumGapStillFalse =
  refl

canonicalKillingBoundaryProxyYMClayStillFalse :
  ymClayPromoted ≡ false
canonicalKillingBoundaryProxyYMClayStillFalse =
  refl
