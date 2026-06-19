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
-- authority, calculation authority, or Clay promotion.  The equation
-- |<omega,e2>|^2 ~ C*g12^beta is logged as a parametric scaling law,
-- and the decision is routed by the fitted beta interval relative to 1.
--
-- Decision convention:
--   * regularity_consistent when fitted beta > 1
--   * blowup_precursor when fitted beta < 1
--   * inconclusive when the 95% CI straddles 1
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
  nPairsRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  minG12ObservedRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  decisionRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  powerLawEquationRecorded :
    NSCalc12ParametricOmegaE2ScalingShape
  optionalRouteAfterCalc11Recorded :
    NSCalc12ParametricOmegaE2ScalingShape
  proofDistanceSevenPlusTwoRecorded :
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
  ∷ nPairsRecorded
  ∷ minG12ObservedRecorded
  ∷ decisionRecorded
  ∷ powerLawEquationRecorded
  ∷ optionalRouteAfterCalc11Recorded
  ∷ proofDistanceSevenPlusTwoRecorded
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

powerLawEquationText : String
powerLawEquationText =
  "|<omega,e2>|^2 ~ C*g12^beta"

optionalRouteText : String
optionalRouteText =
  "Calc 12 is an optional, non-blocking route-selector after Calc 11."

proofDistanceText : String
proofDistanceText =
  "Linked to the current 7 closeable + 2 hard-wall proof distance ledger."

noAuthorityText : String
noAuthorityText =
  "No theorem authority. No calculation authority."

routeCardOText : String
routeCardOText =
  "O: Calc 12 after Calc 11; optional route-selector only."

routeCardRText : String
routeCardRText =
  "R: record the omega-e2 power-law fit, beta interval, sample count, and minimum observed g12."

routeCardCText : String
routeCardCText =
  "C: candidate-only Agda receipt surface with no theorem or calculation authority."

routeCardSText : String
routeCardSText =
  "S: promotion flags false; decision tracks beta relative to 1."

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
  "F: route is optional; beta below 1 leans blowup_precursor, beta above 1 leans regularity_consistent, and a CI straddling 1 stays inconclusive."

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

    n_pairs :
      Nat
    n_pairsIsNine :
      n_pairs ≡ 9

    min_g12_observed :
      String
    min_g12_observedIsCanonical :
      min_g12_observed ≡ "candidate-only minimum observed g12 placeholder"

    decision :
      NSCalc12ParametricOmegaE2ScalingDecision
    decisionIsCanonical :
      decision ≡ inconclusive

    power_law_equation :
      String
    power_law_equationIsCanonical :
      power_law_equation ≡ powerLawEquationText

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
    9
    refl
    "candidate-only minimum observed g12 placeholder"
    refl
    inconclusive
    refl
    powerLawEquationText
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
