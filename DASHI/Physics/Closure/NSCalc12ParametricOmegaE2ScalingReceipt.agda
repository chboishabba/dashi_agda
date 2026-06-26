module DASHI.Physics.Closure.NSCalc12ParametricOmegaE2ScalingReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Calc 12 parametric omega-e2 scaling receipt.
--
-- Candidate-only route selector for the NS Clay chain after Calc 11.
-- This module records the fit surface only.  It does not claim theorem
-- authority, calculation authority, or Clay promotion.  The exact
-- parametric scaling law |<omega,e2>|^2 ~ C*g12^beta is logged together
-- with the fitted beta interval, sample counts, fit quality, and a
-- conservative aggregate route selector.
--
-- Decision convention:
--   * regularity_consistent when the lower CI bound is > 1
--   * blowup_precursor when the upper CI bound is < 1
--   * inconclusive when the 95% CI straddles 1
--   * aggregate_decision uses blowup_precursor > regularity_consistent
--     only when all regularity-consistent inputs agree, otherwise
--     inconclusive.
--
-- The route is linked to the current 7 closeable + 2 hard-wall proof
-- distance ledger, but this receipt remains non-blocking and optional.

data NSCalc12ParametricOmegaE2ScalingDecision : Set where
  regularity_consistent :
    NSCalc12ParametricOmegaE2ScalingDecision
  blowup_precursor :
    NSCalc12ParametricOmegaE2ScalingDecision
  inconclusive :
    NSCalc12ParametricOmegaE2ScalingDecision

data NSCalc12ParametricOmegaE2ScalingShape : Set where
  datumIdRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  fittedBetaRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  fittedCRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  betaCI95Recorded :
    NSCalc12ParametricOmegaE2ScalingShape
  betaCI95JsonRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  nPairsRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  nPairsRawRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  nPairsUsedRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  minG12ObservedRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  rSquaredRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  standardErrorBetaRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  decisionRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  aggregateDecisionRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  powerLawEquationRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  ciThresholdsRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  optionalRouteAfterCalc11Recorded :
    NSCalc12ParametricOmegaE2ScalingShape
  proofDistanceSevenPlusTwoRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  proofBlockingRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  noAuthorityRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  noPromotionRecorded :
    NSCalc12ParametricOmegaE2ScalingShape

canonicalNSCalc12ParametricOmegaE2ScalingShape :
  List NSCalc12ParametricOmegaE2ScalingShape
canonicalNSCalc12ParametricOmegaE2ScalingShape =
  datumIdRecorded
  ∷ fittedBetaRecorded
  ∷ fittedCRecorded
  ∷ betaCI95Recorded
  ∷ betaCI95JsonRecorded
  ∷ nPairsRecorded
  ∷ nPairsRawRecorded
  ∷ nPairsUsedRecorded
  ∷ minG12ObservedRecorded
  ∷ rSquaredRecorded
  ∷ standardErrorBetaRecorded
  ∷ decisionRecorded
  ∷ aggregateDecisionRecorded
  ∷ powerLawEquationRecorded
  ∷ ciThresholdsRecorded
  ∷ optionalRouteAfterCalc11Recorded
  ∷ proofDistanceSevenPlusTwoRecorded
  ∷ proofBlockingRecorded
  ∷ noAuthorityRecorded
  ∷ noPromotionRecorded
  ∷ []

datumIdText : String
datumIdText =
  "NSCalc12ParametricOmegaE2Scaling"

fittedBetaText : String
fittedBetaText =
  "candidate-only fitted beta placeholder"

fittedCText : String
fittedCText =
  "candidate-only fitted C placeholder"

betaCI95Text : String
betaCI95Text =
  "95% CI placeholder; compare the interval to 1 for route selection"

betaCI95JsonText : String
betaCI95JsonText =
  betaCI95Text

nPairsRawText : String
nPairsRawText =
  "candidate-only raw pair count placeholder"

nPairsUsedText : String
nPairsUsedText =
  "candidate-only used pair count placeholder"

minG12ObservedText : String
minG12ObservedText =
  "candidate-only minimum observed g12 placeholder"

rSquaredText : String
rSquaredText =
  "candidate-only r^2 placeholder"

standardErrorBetaText : String
standardErrorBetaText =
  "candidate-only standard error for beta placeholder"

powerLawEquationText : String
powerLawEquationText =
  "|<omega,e2>|^2 ~ C*g12^beta"

aggregateDecisionText : String
aggregateDecisionText =
  "aggregate_decision: any blowup_precursor wins; else all regularity_consistent => regularity_consistent; else inconclusive."

ciThresholdsText : String
ciThresholdsText =
  "thresholds: lower CI > 1 => regularity_consistent; upper CI < 1 => blowup_precursor; CI straddles 1 => inconclusive"

optionalRouteText : String
optionalRouteText =
  "Calc 12 is an optional, non-blocking route-selector after Calc 11."

proofDistanceText : String
proofDistanceText =
  "Linked to the current 7 closeable + 2 hard-wall proof distance ledger."

proofBlockingText : String
proofBlockingText =
  "proof_blocking is false"

noAuthorityText : String
noAuthorityText =
  "No theorem authority. No calculation authority."

routeCardOText : String
routeCardOText =
  "O: Calc 12 after Calc 11; optional route-selector only."

routeCardRText : String
routeCardRText =
  "R: record the omega-e2 power-law fit, beta interval, sample counts, and minimum observed g12."

routeCardCText : String
routeCardCText =
  "C: candidate-only Agda receipt surface with no theorem or calculation authority."

routeCardSText : String
routeCardSText =
  "S: promotion flags false; decision tracks the beta CI relative to 1."

routeCardLText : String
routeCardLText =
  "L: 7 closeable + 2 hard-wall proof distance remains the linked downstream ledger."

routeCardPText : String
routeCardPText =
  "P: keep Calc 12 as a non-blocking selector after Calc 11, not as a proof claim."

routeCardGText : String
routeCardGText =
  "G: no theorem authority, no calculation authority, no Clay promotion."

routeCardFText : String
routeCardFText =
  "F: route is optional; lower CI > 1 leans regularity_consistent, upper CI < 1 leans blowup_precursor, and a CI straddling 1 stays inconclusive."

routeCardAggregateText : String
routeCardAggregateText =
  "Aggregate: any blowup_precursor wins; otherwise all regularity_consistent inputs yield regularity_consistent; otherwise inconclusive."

routeCardText : List String
routeCardText =
  routeCardOText
  ∷ routeCardRText
  ∷ routeCardCText
  ∷ routeCardSText
  ∷ routeCardLText
  ∷ routeCardPText
  ∷ routeCardGText
  ∷ routeCardFText
  ∷ routeCardAggregateText
  ∷ []

record NSCalc12ParametricOmegaE2ScalingReceipt : Set where
  constructor mkNSCalc12ParametricOmegaE2ScalingReceipt
  field
    datum_id :
      String
    datum_idIsCanonical :
      datum_id ≡ datumIdText

    fitted_beta :
      String
    fitted_betaIsCanonical :
      fitted_beta ≡ fittedBetaText

    fitted_C :
      String
    fitted_CIsCanonical :
      fitted_C ≡ fittedCText

    betaCI95 :
      String
    betaCI95IsCanonical :
      betaCI95 ≡ betaCI95Text

    betaCI95Json :
      String
    betaCI95JsonIsCanonical :
      betaCI95Json ≡ betaCI95JsonText

    n_pairs :
      Nat
    n_pairsIsNine :
      n_pairs ≡ 9

    n_pairs_raw :
      Nat
    n_pairs_rawIsNine :
      n_pairs_raw ≡ 9

    n_pairs_used :
      Nat
    n_pairs_usedIsNine :
      n_pairs_used ≡ 9

    min_g12_observed :
      String
    min_g12_observedIsCanonical :
      min_g12_observed ≡ minG12ObservedText

    r_squared :
      String
    r_squaredIsCanonical :
      r_squared ≡ rSquaredText

    standard_error_beta :
      String
    standard_error_betaIsCanonical :
      standard_error_beta ≡ standardErrorBetaText

    decision :
      NSCalc12ParametricOmegaE2ScalingDecision
    decisionIsCanonical :
      decision ≡ inconclusive

    aggregate_decision :
      NSCalc12ParametricOmegaE2ScalingDecision
    aggregate_decisionIsCanonical :
      aggregate_decision ≡ inconclusive

    power_law_equation :
      String
    power_law_equationIsCanonical :
      power_law_equation ≡ powerLawEquationText

    ci_thresholds :
      String
    ci_thresholdsIsCanonical :
      ci_thresholds ≡ ciThresholdsText

    optional_route_after_calc11 :
      String
    optional_route_after_calc11IsCanonical :
      optional_route_after_calc11 ≡ optionalRouteText

    proof_distance_closeable :
      Nat
    proof_distance_closeableIsSeven :
      proof_distance_closeable ≡ 7

    proof_distance_hard_wall :
      Nat
    proof_distance_hard_wallIsTwo :
      proof_distance_hard_wall ≡ 2

    proof_distance_total :
      Nat
    proof_distance_totalIsNine :
      proof_distance_total ≡ 9

    proof_distance_link :
      String
    proof_distance_linkIsCanonical :
      proof_distance_link ≡ proofDistanceText

    proof_blocking :
      Bool
    proof_blockingIsFalse :
      proof_blocking ≡ false

    theorem_authority :
      Bool
    theorem_authorityIsFalse :
      theorem_authority ≡ false

    calculation_authority :
      Bool
    calculation_authorityIsFalse :
      calculation_authority ≡ false

    clay_promotion :
      Bool
    clay_promotionIsFalse :
      clay_promotion ≡ false

    terminal_promotion :
      Bool
    terminal_promotionIsFalse :
      terminal_promotion ≡ false

    route_card :
      List String
    route_cardIsCanonical :
      route_card ≡ routeCardText

open NSCalc12ParametricOmegaE2ScalingReceipt public

canonicalNSCalc12ParametricOmegaE2ScalingReceipt :
  NSCalc12ParametricOmegaE2ScalingReceipt
canonicalNSCalc12ParametricOmegaE2ScalingReceipt =
  mkNSCalc12ParametricOmegaE2ScalingReceipt
    datumIdText
    refl
    fittedBetaText
    refl
    fittedCText
    refl
    betaCI95Text
    refl
    betaCI95JsonText
    refl
    9
    refl
    9
    refl
    9
    refl
    minG12ObservedText
    refl
    rSquaredText
    refl
    standardErrorBetaText
    refl
    inconclusive
    refl
    inconclusive
    refl
    powerLawEquationText
    refl
    ciThresholdsText
    refl
    optionalRouteText
    refl
    7
    refl
    2
    refl
    9
    refl
    proofDistanceText
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    routeCardText
    refl

calc12RouteIsOptional :
  optional_route_after_calc11 canonicalNSCalc12ParametricOmegaE2ScalingReceipt ≡
  optionalRouteText
calc12RouteIsOptional = refl

calc12NoAuthority :
  theorem_authority canonicalNSCalc12ParametricOmegaE2ScalingReceipt ≡ false
calc12NoAuthority = refl

calc12NoCalculationAuthority :
  calculation_authority canonicalNSCalc12ParametricOmegaE2ScalingReceipt ≡ false
calc12NoCalculationAuthority = refl

calc12NoPromotion :
  clay_promotion canonicalNSCalc12ParametricOmegaE2ScalingReceipt ≡ false
calc12NoPromotion = refl

calc12TerminalPromotionFalse :
  terminal_promotion canonicalNSCalc12ParametricOmegaE2ScalingReceipt ≡ false
calc12TerminalPromotionFalse = refl
