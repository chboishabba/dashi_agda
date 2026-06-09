module DASHI.Physics.Closure.NSQuantitativeStationarityRateProxyHarnessResult where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSQuantitativeStationarityRateBoundary
  as RateBoundary
import DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary
  as Transfer

------------------------------------------------------------------------
-- NS quantitative stationarity-rate proxy harness result receipt.
--
-- Source harness:
--
--   scripts/ns_stationarity_rate_proxy_harness.py
--
-- Last validation run recorded by this receipt:
--
--   python scripts/ns_stationarity_rate_proxy_harness.py
--     --depths 8
--     --min-depth 3
--     --json-output outputs/ns_stationarity_rate_proxy_summary.json
--     --json
--
-- Scope:
--
--   finite synthetic stationarity-rate proxy only.
--
-- This file records the observed proxy fields from the executable harness:
-- log-rate theta profiles, synthetic Gronwall/Lipschitz delta updates,
-- bias-bound proxy delta_r * sqrt(11/60), a deliberately bad
-- nondecaying counterprofile, and promotion=false.  It does not construct
-- a PDE Abel triadic defect measure, prove the Seregin/ESS quantitative
-- rate, prove transfer-operator stationarity, or close any Clay theorem.

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

------------------------------------------------------------------------
-- Harness identity and run configuration.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ns_stationarity_rate_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_stationarity_rate_proxy_summary.json"

receiptScope : String
receiptScope =
  "finite_synthetic_stationarity_rate_proxy_not_pde_proof"

runCommandText : String
runCommandText =
  "python scripts/ns_stationarity_rate_proxy_harness.py --depths 8 --min-depth 3 --json-output outputs/ns_stationarity_rate_proxy_summary.json --json"

rateGridText : String
rateGridText =
  "r = 2 ^ (-depth), depth = 3 .. 10"

thetaRateText : String
thetaRateText =
  "theta_r = theta_scale / sqrt(log(1/r))"

deltaUpdateText : String
deltaUpdateText =
  "delta_i = exp(L*dt) * (exp(-memory_decay*dt)*delta_{i-1} + dt*(L*theta_i + control_i))"

biasBoundText : String
biasBoundText =
  "bias_bound = delta_r * sqrt(11/60)"

biasConstantObservedText : String
biasConstantObservedText =
  "sqrt(11/60) ~= 0.4281744192888376"

parametersObservedText : String
parametersObservedText =
  "depths=8, min_depth=3, theta_scale=1.0, lipschitz=0.35, dt=0.25, memory_decay=2.4, initial_delta=0.0"

------------------------------------------------------------------------
-- Imported boundary anchors.

rateBoundaryReference : String
rateBoundaryReference =
  "DASHI.Physics.Closure.NSQuantitativeStationarityRateBoundary"

transferBiasNeutralityReference : String
transferBiasNeutralityReference =
  "DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary"

rateBoundaryImported : Bool
rateBoundaryImported =
  true

transferBiasNeutralityImported : Bool
transferBiasNeutralityImported =
  true

record ImportedRateProxySupport : Set where
  field
    quantitativeStationarityRateBoundary :
      RateBoundary.NSQuantitativeStationarityRateBoundary
    quantitativeStationarityRateBoundaryIsCanonical :
      quantitativeStationarityRateBoundary
        ≡ RateBoundary.canonicalNSQuantitativeStationarityRateBoundary
    transferBiasNeutralityBoundary :
      Transfer.NSTransferOperatorBiasNeutralityBoundary
    transferBiasNeutralityBoundaryIsCanonical :
      transferBiasNeutralityBoundary
        ≡ Transfer.canonicalNSTransferOperatorBiasNeutralityBoundary
    rateBoundaryImportedIsTrue :
      rateBoundaryImported ≡ true
    transferBiasNeutralityImportedIsTrue :
      transferBiasNeutralityImported ≡ true

canonicalImportedRateProxySupport : ImportedRateProxySupport
canonicalImportedRateProxySupport =
  record
    { quantitativeStationarityRateBoundary =
        RateBoundary.canonicalNSQuantitativeStationarityRateBoundary
    ; quantitativeStationarityRateBoundaryIsCanonical =
        refl
    ; transferBiasNeutralityBoundary =
        Transfer.canonicalNSTransferOperatorBiasNeutralityBoundary
    ; transferBiasNeutralityBoundaryIsCanonical =
        refl
    ; rateBoundaryImportedIsTrue =
        refl
    ; transferBiasNeutralityImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Observed top-level harness fields.

data StationarityRateHarnessField : Set where
  okField :
    StationarityRateHarnessField
  scriptField :
    StationarityRateHarnessField
  scopeField :
    StationarityRateHarnessField
  rateModelField :
    StationarityRateHarnessField
  parametersField :
    StationarityRateHarnessField
  profilesField :
    StationarityRateHarnessField
  checksField :
    StationarityRateHarnessField
  promotionField :
    StationarityRateHarnessField
  promotionFalseField :
    StationarityRateHarnessField

canonicalStationarityRateHarnessFields :
  List StationarityRateHarnessField
canonicalStationarityRateHarnessFields =
  okField
  ∷ scriptField
  ∷ scopeField
  ∷ rateModelField
  ∷ parametersField
  ∷ profilesField
  ∷ checksField
  ∷ promotionField
  ∷ promotionFalseField
  ∷ []

stationarityRateHarnessFieldCount : Nat
stationarityRateHarnessFieldCount =
  listLength canonicalStationarityRateHarnessFields

stationarityRateHarnessFieldCountIs9 :
  stationarityRateHarnessFieldCount ≡ 9
stationarityRateHarnessFieldCountIs9 =
  refl

ok_observed : Bool
ok_observed =
  true

promotion : Bool
promotion =
  false

promotion_false_observed : Bool
promotion_false_observed =
  true

ok_observed_is_true :
  ok_observed ≡ true
ok_observed_is_true =
  refl

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

promotion_false_observed_is_true :
  promotion_false_observed ≡ true
promotion_false_observed_is_true =
  refl

------------------------------------------------------------------------
-- Profile observations.

data StationarityRateProfile : Set where
  logSquareControl :
    StationarityRateProfile
  logThreeHalvesControl :
    StationarityRateProfile
  lipschitzMatchedControl :
    StationarityRateProfile
  badNondecayingControl :
    StationarityRateProfile

canonicalStationarityRateProfiles :
  List StationarityRateProfile
canonicalStationarityRateProfiles =
  logSquareControl
  ∷ logThreeHalvesControl
  ∷ lipschitzMatchedControl
  ∷ badNondecayingControl
  ∷ []

stationarityRateProfileCount : Nat
stationarityRateProfileCount =
  listLength canonicalStationarityRateProfiles

stationarityRateProfileCountIs4 :
  stationarityRateProfileCount ≡ 4
stationarityRateProfileCountIs4 =
  refl

data GoodLogRateProfile : Set where
  goodLogSquareControl :
    GoodLogRateProfile
  goodLogThreeHalvesControl :
    GoodLogRateProfile
  goodLipschitzMatchedControl :
    GoodLogRateProfile

canonicalGoodLogRateProfiles :
  List GoodLogRateProfile
canonicalGoodLogRateProfiles =
  goodLogSquareControl
  ∷ goodLogThreeHalvesControl
  ∷ goodLipschitzMatchedControl
  ∷ []

goodLogRateProfileCount : Nat
goodLogRateProfileCount =
  listLength canonicalGoodLogRateProfiles

goodLogRateProfileCountIs3 :
  goodLogRateProfileCount ≡ 3
goodLogRateProfileCountIs3 =
  refl

logSquareProfileDescription : String
logSquareProfileDescription =
  "log_square_control: decaying control c_r = 0.35 * theta_r^2"

logThreeHalvesProfileDescription : String
logThreeHalvesProfileDescription =
  "log_32_control: decaying control c_r = 0.20 * log(1/r)^(-3/2)"

lipschitzMatchedProfileDescription : String
lipschitzMatchedProfileDescription =
  "lipschitz_matched_control: mild control c_r = 0.12 * theta_r"

badNondecayingProfileDescription : String
badNondecayingProfileDescription =
  "bad_nondecaying_control: deliberately bad profile with c_r = 0.20 independent of r"

all_good_profiles_decay : Bool
all_good_profiles_decay =
  true

bad_nondecaying_profile_included : Bool
bad_nondecaying_profile_included =
  true

bad_nondecaying_profile_visible : Bool
bad_nondecaying_profile_visible =
  true

bad_nondecaying_profile_classified_as_counterprofile : Bool
bad_nondecaying_profile_classified_as_counterprofile =
  true

all_good_profiles_decay_is_true :
  all_good_profiles_decay ≡ true
all_good_profiles_decay_is_true =
  refl

bad_nondecaying_profile_included_is_true :
  bad_nondecaying_profile_included ≡ true
bad_nondecaying_profile_included_is_true =
  refl

bad_nondecaying_profile_visible_is_true :
  bad_nondecaying_profile_visible ≡ true
bad_nondecaying_profile_visible_is_true =
  refl

bad_nondecaying_profile_classified_as_counterprofile_is_true :
  bad_nondecaying_profile_classified_as_counterprofile ≡ true
bad_nondecaying_profile_classified_as_counterprofile_is_true =
  refl

------------------------------------------------------------------------
-- Observed numerical-proxy summaries as strings.
--
-- These strings intentionally avoid claiming exact Agda arithmetic.  They
-- record the executable receipt values and their governance meaning.

logSquareTerminalDeltaText : String
logSquareTerminalDeltaText =
  "log_square_control terminal_delta ~= 0.13881243642369887; terminal_bias_bound ~= 0.05943593435578595; tail delta ratio ~= 0.7974626735486054"

logThreeHalvesTerminalDeltaText : String
logThreeHalvesTerminalDeltaText =
  "log_32_control terminal_delta ~= 0.1077277346559931; terminal_bias_bound ~= 0.04612626022763183; tail delta ratio ~= 0.8159777432660118"

lipschitzMatchedTerminalDeltaText : String
lipschitzMatchedTerminalDeltaText =
  "lipschitz_matched_control terminal_delta ~= 0.1309452555966478; terminal_bias_bound ~= 0.056067408773723085; tail delta ratio ~= 0.8677832918455748"

badNondecayingTerminalDeltaText : String
badNondecayingTerminalDeltaText =
  "bad_nondecaying_control terminal_delta ~= 0.2313458426456035; terminal_bias_bound ~= 0.09905637182966809; control ratio = 1.0; visible nondecay"

thetaTerminalObservationText : String
thetaTerminalObservationText =
  "all profiles use theta_r decreasing from ~= 0.6934683460425486 at depth 3 to ~= 0.3798282560433022 at depth 10"

------------------------------------------------------------------------
-- Harness checks and rate-model governance.

data StationarityRateHarnessCheck : Set where
  allBiasBoundsMatch :
    StationarityRateHarnessCheck
  allGoodProfilesDecay :
    StationarityRateHarnessCheck
  badNondecayingProfileIncluded :
    StationarityRateHarnessCheck
  badNondecayingProfileVisible :
    StationarityRateHarnessCheck
  promotionFalseCheck :
    StationarityRateHarnessCheck

canonicalStationarityRateHarnessChecks :
  List StationarityRateHarnessCheck
canonicalStationarityRateHarnessChecks =
  allBiasBoundsMatch
  ∷ allGoodProfilesDecay
  ∷ badNondecayingProfileIncluded
  ∷ badNondecayingProfileVisible
  ∷ promotionFalseCheck
  ∷ []

stationarityRateHarnessCheckCount : Nat
stationarityRateHarnessCheckCount =
  listLength canonicalStationarityRateHarnessChecks

stationarityRateHarnessCheckCountIs5 :
  stationarityRateHarnessCheckCount ≡ 5
stationarityRateHarnessCheckCountIs5 =
  refl

all_bias_bounds_match : Bool
all_bias_bounds_match =
  true

bias_bound_proxy_observed : Bool
bias_bound_proxy_observed =
  true

finite_nonnegative_delta_and_bias_observed : Bool
finite_nonnegative_delta_and_bias_observed =
  true

theta_log_minus_half_nonincreasing_observed : Bool
theta_log_minus_half_nonincreasing_observed =
  true

all_bias_bounds_match_is_true :
  all_bias_bounds_match ≡ true
all_bias_bounds_match_is_true =
  refl

bias_bound_proxy_observed_is_true :
  bias_bound_proxy_observed ≡ true
bias_bound_proxy_observed_is_true =
  refl

finite_nonnegative_delta_and_bias_observed_is_true :
  finite_nonnegative_delta_and_bias_observed ≡ true
finite_nonnegative_delta_and_bias_observed_is_true =
  refl

theta_log_minus_half_nonincreasing_observed_is_true :
  theta_log_minus_half_nonincreasing_observed ≡ true
theta_log_minus_half_nonincreasing_observed_is_true =
  refl

------------------------------------------------------------------------
-- Boundary-only status and explicit non-claims.

data BoundaryOnlyNonClaim : Set where
  syntheticProxyOnlyNotPDEMeasure :
    BoundaryOnlyNonClaim
  noSereginESSRateProof :
    BoundaryOnlyNonClaim
  noTransferOperatorStationarityProof :
    BoundaryOnlyNonClaim
  noAbelTriadicDefectMeasureConstruction :
    BoundaryOnlyNonClaim
  noTriadicCompensatedLeakageIdentity :
    BoundaryOnlyNonClaim
  noResidualDepletionClosure :
    BoundaryOnlyNonClaim
  noNavierStokesClayPromotion :
    BoundaryOnlyNonClaim
  noTerminalUnificationPromotion :
    BoundaryOnlyNonClaim

canonicalBoundaryOnlyNonClaims :
  List BoundaryOnlyNonClaim
canonicalBoundaryOnlyNonClaims =
  syntheticProxyOnlyNotPDEMeasure
  ∷ noSereginESSRateProof
  ∷ noTransferOperatorStationarityProof
  ∷ noAbelTriadicDefectMeasureConstruction
  ∷ noTriadicCompensatedLeakageIdentity
  ∷ noResidualDepletionClosure
  ∷ noNavierStokesClayPromotion
  ∷ noTerminalUnificationPromotion
  ∷ []

boundaryOnlyNonClaimCount : Nat
boundaryOnlyNonClaimCount =
  listLength canonicalBoundaryOnlyNonClaims

boundaryOnlyNonClaimCountIs8 :
  boundaryOnlyNonClaimCount ≡ 8
boundaryOnlyNonClaimCountIs8 =
  refl

boundary_only_status : Bool
boundary_only_status =
  true

pde_measure_constructed : Bool
pde_measure_constructed =
  false

seregin_ess_rate_proved : Bool
seregin_ess_rate_proved =
  false

transfer_stationarity_proved : Bool
transfer_stationarity_proved =
  false

triadic_compensated_leakage_proved : Bool
triadic_compensated_leakage_proved =
  false

residual_depletion_closed : Bool
residual_depletion_closed =
  false

navier_stokes_clay_promotion : Bool
navier_stokes_clay_promotion =
  false

terminal_unification_promotion : Bool
terminal_unification_promotion =
  false

boundary_only_status_is_true :
  boundary_only_status ≡ true
boundary_only_status_is_true =
  refl

pde_measure_constructed_is_false :
  pde_measure_constructed ≡ false
pde_measure_constructed_is_false =
  refl

seregin_ess_rate_proved_is_false :
  seregin_ess_rate_proved ≡ false
seregin_ess_rate_proved_is_false =
  refl

transfer_stationarity_proved_is_false :
  transfer_stationarity_proved ≡ false
transfer_stationarity_proved_is_false =
  refl

triadic_compensated_leakage_proved_is_false :
  triadic_compensated_leakage_proved ≡ false
triadic_compensated_leakage_proved_is_false =
  refl

residual_depletion_closed_is_false :
  residual_depletion_closed ≡ false
residual_depletion_closed_is_false =
  refl

navier_stokes_clay_promotion_is_false :
  navier_stokes_clay_promotion ≡ false
navier_stokes_clay_promotion_is_false =
  refl

terminal_unification_promotion_is_false :
  terminal_unification_promotion ≡ false
terminal_unification_promotion_is_false =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record NSQuantitativeStationarityRateProxyHarnessResult : Set where
  field
    sourceHarness :
      String
    jsonReceipt :
      String
    scope :
      String
    command :
      String
    importedSupport :
      ImportedRateProxySupport
    observedFields :
      List StationarityRateHarnessField
    observedFieldCountIs9 :
      listLength observedFields ≡ 9
    profiles :
      List StationarityRateProfile
    profileCountIs4 :
      listLength profiles ≡ 4
    goodProfiles :
      List GoodLogRateProfile
    goodProfileCountIs3 :
      listLength goodProfiles ≡ 3
    harnessChecks :
      List StationarityRateHarnessCheck
    harnessCheckCountIs5 :
      listLength harnessChecks ≡ 5
    boundaryOnlyNonClaims :
      List BoundaryOnlyNonClaim
    boundaryOnlyNonClaimCountProof :
      listLength boundaryOnlyNonClaims ≡ 8
    okObserved :
      ok_observed ≡ true
    allGoodProfilesDecayObserved :
      all_good_profiles_decay ≡ true
    badNondecayingProfileIncludedObserved :
      bad_nondecaying_profile_included ≡ true
    badNondecayingProfileVisibleObserved :
      bad_nondecaying_profile_visible ≡ true
    allBiasBoundsMatchObserved :
      all_bias_bounds_match ≡ true
    biasBoundProxyObserved :
      bias_bound_proxy_observed ≡ true
    thetaRateObserved :
      theta_log_minus_half_nonincreasing_observed ≡ true
    promotionFalse :
      promotion ≡ false
    boundaryOnly :
      boundary_only_status ≡ true
    pdeMeasureConstructedFalse :
      pde_measure_constructed ≡ false
    sereginESSRateProvedFalse :
      seregin_ess_rate_proved ≡ false
    transferStationarityProvedFalse :
      transfer_stationarity_proved ≡ false
    triadicCompensatedLeakageProvedFalse :
      triadic_compensated_leakage_proved ≡ false
    residualDepletionClosedFalse :
      residual_depletion_closed ≡ false
    navierStokesClayPromotionFalse :
      navier_stokes_clay_promotion ≡ false
    terminalUnificationPromotionFalse :
      terminal_unification_promotion ≡ false
    rateGrid :
      String
    thetaRate :
      String
    deltaUpdate :
      String
    biasBound :
      String
    biasConstant :
      String
    parameters :
      String
    logSquareObservation :
      String
    logThreeHalvesObservation :
      String
    lipschitzMatchedObservation :
      String
    badNondecayingObservation :
      String
    thetaTerminalObservation :
      String

canonicalNSQuantitativeStationarityRateProxyHarnessResult :
  NSQuantitativeStationarityRateProxyHarnessResult
canonicalNSQuantitativeStationarityRateProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        jsonReceiptPath
    ; scope =
        receiptScope
    ; command =
        runCommandText
    ; importedSupport =
        canonicalImportedRateProxySupport
    ; observedFields =
        canonicalStationarityRateHarnessFields
    ; observedFieldCountIs9 =
        stationarityRateHarnessFieldCountIs9
    ; profiles =
        canonicalStationarityRateProfiles
    ; profileCountIs4 =
        stationarityRateProfileCountIs4
    ; goodProfiles =
        canonicalGoodLogRateProfiles
    ; goodProfileCountIs3 =
        goodLogRateProfileCountIs3
    ; harnessChecks =
        canonicalStationarityRateHarnessChecks
    ; harnessCheckCountIs5 =
        stationarityRateHarnessCheckCountIs5
    ; boundaryOnlyNonClaims =
        canonicalBoundaryOnlyNonClaims
    ; boundaryOnlyNonClaimCountProof =
        boundaryOnlyNonClaimCountIs8
    ; okObserved =
        ok_observed_is_true
    ; allGoodProfilesDecayObserved =
        all_good_profiles_decay_is_true
    ; badNondecayingProfileIncludedObserved =
        bad_nondecaying_profile_included_is_true
    ; badNondecayingProfileVisibleObserved =
        bad_nondecaying_profile_visible_is_true
    ; allBiasBoundsMatchObserved =
        all_bias_bounds_match_is_true
    ; biasBoundProxyObserved =
        bias_bound_proxy_observed_is_true
    ; thetaRateObserved =
        theta_log_minus_half_nonincreasing_observed_is_true
    ; promotionFalse =
        promotion_is_false
    ; boundaryOnly =
        boundary_only_status_is_true
    ; pdeMeasureConstructedFalse =
        pde_measure_constructed_is_false
    ; sereginESSRateProvedFalse =
        seregin_ess_rate_proved_is_false
    ; transferStationarityProvedFalse =
        transfer_stationarity_proved_is_false
    ; triadicCompensatedLeakageProvedFalse =
        triadic_compensated_leakage_proved_is_false
    ; residualDepletionClosedFalse =
        residual_depletion_closed_is_false
    ; navierStokesClayPromotionFalse =
        navier_stokes_clay_promotion_is_false
    ; terminalUnificationPromotionFalse =
        terminal_unification_promotion_is_false
    ; rateGrid =
        rateGridText
    ; thetaRate =
        thetaRateText
    ; deltaUpdate =
        deltaUpdateText
    ; biasBound =
        biasBoundText
    ; biasConstant =
        biasConstantObservedText
    ; parameters =
        parametersObservedText
    ; logSquareObservation =
        logSquareTerminalDeltaText
    ; logThreeHalvesObservation =
        logThreeHalvesTerminalDeltaText
    ; lipschitzMatchedObservation =
        lipschitzMatchedTerminalDeltaText
    ; badNondecayingObservation =
        badNondecayingTerminalDeltaText
    ; thetaTerminalObservation =
        thetaTerminalObservationText
    }

------------------------------------------------------------------------
-- Promotion guards exported as small named facts.

nsQuantitativeStationarityRateProxyHarnessIsBoundaryOnly :
  boundary_only_status ≡ true
nsQuantitativeStationarityRateProxyHarnessIsBoundaryOnly =
  refl

nsQuantitativeStationarityRateProxyHarnessKeepsPromotionFalse :
  promotion ≡ false
nsQuantitativeStationarityRateProxyHarnessKeepsPromotionFalse =
  refl

nsQuantitativeStationarityRateProxyHarnessKeepsNSClayFalse :
  navier_stokes_clay_promotion ≡ false
nsQuantitativeStationarityRateProxyHarnessKeepsNSClayFalse =
  refl

nsQuantitativeStationarityRateProxyHarnessKeepsTerminalFalse :
  terminal_unification_promotion ≡ false
nsQuantitativeStationarityRateProxyHarnessKeepsTerminalFalse =
  refl
