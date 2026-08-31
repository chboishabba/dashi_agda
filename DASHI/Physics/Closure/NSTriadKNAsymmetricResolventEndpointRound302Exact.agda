module DASHI.Physics.Closure.NSTriadKNAsymmetricResolventEndpointRound302Exact where

------------------------------------------------------------------------
-- ROUND302 / BIDI ENDPOINT CORRECTION: INITIAL AND TERMINAL FLUXES ARE DIFFERENT
--
-- Integrating the R290 flux identity gives
--
--   integral D_Gram = F_off(0) - F_off(T) + integral R_weighted.
--
-- R297's positive completion controls the terminal contribution
--
--   -F_off(T) <= F_diag(T),
--
-- but does not upper-bound +F_off(0).  There is no reason to demand one common
-- endpoint theorem: the initial state is fixed smooth data and may be paid by
-- an initial-data norm, while the terminal state must be controlled uniformly.
--
-- This module compiles those asymmetric endpoint payments exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

record AsymmetricResolventEndpointPayment : Set where
  constructor asymmetric-resolvent-endpoint-payment
  field
    initialOffDiagonal terminalNegativeOffDiagonal : ℚ
    initialDataUpperBound terminalDiagonalUpperBound : ℚ

    initialFluxPaidByData :
      initialOffDiagonal ≤ initialDataUpperBound

    terminalFluxPaidByPositiveCompletion :
      terminalNegativeOffDiagonal ≤ terminalDiagonalUpperBound

open AsymmetricResolventEndpointPayment public

endpointBudget : AsymmetricResolventEndpointPayment → ℚ
endpointBudget P = initialDataUpperBound P + terminalDiagonalUpperBound P

bothEndpointsPaid :
  (P : AsymmetricResolventEndpointPayment) →
  initialOffDiagonal P + terminalNegativeOffDiagonal P
  ≤ endpointBudget P
bothEndpointsPaid P =
  ℚP.+-mono-≤
    (initialFluxPaidByData P)
    (terminalFluxPaidByPositiveCompletion P)

record PhysicalResolventEndpointLeaf : Set where
  constructor physical-resolvent-endpoint-leaf
  field
    endpointPayment : AsymmetricResolventEndpointPayment

    initialFluxIsLiteralR290OffDiagonalAtZero : Bool
    initialFluxIsLiteralR290OffDiagonalAtZeroIsTrue :
      initialFluxIsLiteralR290OffDiagonalAtZero ≡ true

    terminalPaymentUsesR297PositiveCompletion : Bool
    terminalPaymentUsesR297PositiveCompletionIsTrue :
      terminalPaymentUsesR297PositiveCompletion ≡ true

    terminalDiagonalUsesR298NoCardinalityPayment : Bool
    terminalDiagonalUsesR298NoCardinalityPaymentIsTrue :
      terminalDiagonalUsesR298NoCardinalityPayment ≡ true

open PhysicalResolventEndpointLeaf public

round302EndpointAsymmetryCompilerClosed : Bool
round302EndpointAsymmetryCompilerClosed = true

round302InitialSmoothDataFluxPaid : Bool
round302InitialSmoothDataFluxPaid = false

round302TerminalPositiveCompletionPaid : Bool
round302TerminalPositiveCompletionPaid = false

round302PhysicalEndpointLeafClosed : Bool
round302PhysicalEndpointLeafClosed = false

round302PackageAClosed : Bool
round302PackageAClosed = false

round302ClayPromotion : Bool
round302ClayPromotion = false

round302EndpointAsymmetryCompilerClosedIsTrue :
  round302EndpointAsymmetryCompilerClosed ≡ true
round302EndpointAsymmetryCompilerClosedIsTrue = refl
