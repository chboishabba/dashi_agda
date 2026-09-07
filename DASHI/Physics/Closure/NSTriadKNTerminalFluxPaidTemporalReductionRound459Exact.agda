module DASHI.Physics.Closure.NSTriadKNTerminalFluxPaidTemporalReductionRound459Exact where

------------------------------------------------------------------------
-- ROUND459 / TERMINAL FLUX PAYMENT -> TWO-LEAF TEMPORAL FRONTIER
--
-- R393 proves on the literal same-object temporal realization
--
--   integral GramDebt = F(0) - F(T) + integral Remainder.
--
-- If an endpoint producer pays only the orientation actually needed,
--
--   -F(T) <= terminalBound,
--
-- then finite ordered-field algebra yields
--
--   integral GramDebt
--     <= F(0) + terminalBound + integral Remainder.
--
-- R458 supplies exactly such a terminal payment for the Cauchy/R397 endpoint.
-- This compiler therefore removes the terminal endpoint from the remaining
-- temporal discovery frontier without pretending to bound +F(T).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact as R393

record TerminalFluxPayment
    {t} {Time : Set t}
    (R : R393.LiteralR378TemporalRealization Time) : Set t where
  constructor terminal-flux-payment
  field
    terminalBound : ℚ
    negativeTerminalFluxPaid :
      0ℚ - R393.literalOffDiagonalFlux R (R393.finalTime R)
      ≤ terminalBound

open TerminalFluxPayment public

terminalPaymentRemovesFinalFlux :
  ∀ {t} {Time : Set t}
    (R : R393.LiteralR378TemporalRealization Time) →
  (P : TerminalFluxPayment R) →
  R393.Integral R (R393.literalGlobalGramDebt R)
  ≤
  R393.literalOffDiagonalFlux R (R393.initialTime R)
    + terminalBound P
    + R393.Integral R (R393.literalWeightedRemainder R)
terminalPaymentRemovesFinalFlux R P =
  let
    exact = R393.literalR378IntegratedGramFluxIdentity R
    initial = R393.literalOffDiagonalFlux R (R393.initialTime R)
    terminal = R393.literalOffDiagonalFlux R (R393.finalTime R)
    remainder = R393.Integral R (R393.literalWeightedRemainder R)

    endpointStep :
      initial - terminal ≤ initial + terminalBound P
    endpointStep =
      let
        shifted = ℚP.+-monoˡ-≤ initial (negativeTerminalFluxPaid P)
        leftMeaning : initial + (0ℚ - terminal) ≡ initial - terminal
        leftMeaning = solve (initial ∷ terminal ∷ [])
      in
      subst
        (λ lower → lower ≤ initial + terminalBound P)
        leftMeaning
        shifted

    withRemainder :
      (initial - terminal) + remainder
      ≤ (initial + terminalBound P) + remainder
    withRemainder = ℚP.+-monoʳ-≤ remainder endpointStep
  in
  subst
    (λ lower →
      lower ≤ initial + terminalBound P + remainder)
    exact
    withRemainder

record InitialAndRemainderPayment
    {t} {Time : Set t}
    (R : R393.LiteralR378TemporalRealization Time)
    (T : TerminalFluxPayment R) : Set t where
  constructor initial-and-remainder-payment
  field
    initialBound remainderBound : ℚ
    initialFluxPaid :
      R393.literalOffDiagonalFlux R (R393.initialTime R) ≤ initialBound
    integratedRemainderPaid :
      R393.Integral R (R393.literalWeightedRemainder R) ≤ remainderBound

open InitialAndRemainderPayment public

initialRemainderPaymentsCloseTemporalBudget :
  ∀ {t} {Time : Set t}
    (R : R393.LiteralR378TemporalRealization Time)
    (T : TerminalFluxPayment R) →
  (P : InitialAndRemainderPayment R T) →
  R393.Integral R (R393.literalGlobalGramDebt R)
  ≤ initialBound P + terminalBound T + remainderBound P
initialRemainderPaymentsCloseTemporalBudget R T P =
  let
    first = terminalPaymentRemovesFinalFlux R T
    endpoints = ℚP.+-monoˡ-≤ (terminalBound T) (initialFluxPaid P)
    endpointsWithRemainder =
      ℚP.+-mono-≤ endpoints (integratedRemainderPaid P)
  in
  ℚP.≤-trans first endpointsWithRemainder

round459TerminalEndpointRemovedFromTemporalFrontier : Bool
round459TerminalEndpointRemovedFromTemporalFrontier = true

round459RemainingInitialPositiveFluxLeaf : Bool
round459RemainingInitialPositiveFluxLeaf = true

round459RemainingIntegratedNonlinearRemainderLeaf : Bool
round459RemainingIntegratedNonlinearRemainderLeaf = true

round459IntroducesCardinalityTax : Bool
round459IntroducesCardinalityTax = false

round459ContainsPostulate : Bool
round459ContainsPostulate = false

round459PackageAClosed : Bool
round459PackageAClosed = false

round459ClayPromotion : Bool
round459ClayPromotion = false

round459TerminalEndpointRemovedFromTemporalFrontierIsTrue :
  round459TerminalEndpointRemovedFromTemporalFrontier ≡ true
round459TerminalEndpointRemovedFromTemporalFrontierIsTrue = refl

round459ContainsPostulateIsFalse : round459ContainsPostulate ≡ false
round459ContainsPostulateIsFalse = refl
