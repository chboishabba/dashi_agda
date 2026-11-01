module DASHI.Physics.Closure.NSTriadKNResolventEndpointCompletionRound297Exact where

------------------------------------------------------------------------
-- ROUND297 / POSITIVE COMPLETION REDUCES THE OFF-DIAGONAL ENDPOINT
--
-- For the resolvent-weighted same-output Gram form write
--
--   F_full = F_diag + F_off.
--
-- If the full Cauchy/resolvent kernel form is nonnegative, then
--
--   -F_off <= F_diag.
--
-- This is the exact endpoint inequality needed after integrating R290.  It is
-- purely ordered-field algebra.  The analytic producer still has to establish
-- positivity of the literal full physical resolvent form and bound its diagonal
-- on the same R227 cell family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record PositiveResolventCompletion : Set where
  constructor positive-resolvent-completion
  field
    diagonal offDiagonal full : ℚ
    fullSplits : full ≡ diagonal + offDiagonal
    fullNonnegative : 0ℚ ≤ full

open PositiveResolventCompletion public

negativeOffDiagonalBoundedByDiagonal :
  (P : PositiveResolventCompletion) →
  0ℚ - offDiagonal P ≤ diagonal P
negativeOffDiagonalBoundedByDiagonal P =
  let
    shifted :
      0ℚ + (0ℚ - offDiagonal P)
      ≤ full P + (0ℚ - offDiagonal P)
    shifted = ℚP.+-monoʳ-≤ (0ℚ - offDiagonal P) (fullNonnegative P)

    leftNormalize :
      0ℚ + (0ℚ - offDiagonal P) ≡ 0ℚ - offDiagonal P
    leftNormalize = solve (offDiagonal P ∷ [])

    rightNormalize :
      full P + (0ℚ - offDiagonal P) ≡ diagonal P
    rightNormalize rewrite fullSplits P = solve (diagonal P ∷ offDiagonal P ∷ [])
  in
  subst
    (λ left → left ≤ diagonal P)
    leftNormalize
    (subst
      (0ℚ + (0ℚ - offDiagonal P) ≤_)
      rightNormalize
      shifted)

record ResolventEndpointPayment : Set where
  constructor resolvent-endpoint-payment
  field
    completion : PositiveResolventCompletion
    diagonalUpperBound : ℚ
    diagonalPaid : diagonal completion ≤ diagonalUpperBound

open ResolventEndpointPayment public

negativeTerminalFluxPaid :
  (P : ResolventEndpointPayment) →
  0ℚ - offDiagonal (completion P) ≤ diagonalUpperBound P
negativeTerminalFluxPaid P =
  ℚP.≤-trans
    (negativeOffDiagonalBoundedByDiagonal (completion P))
    (diagonalPaid P)

round297EndpointReductionClosed : Bool
round297EndpointReductionClosed = true

round297RequiresFullCoherentEndpointAbsoluteValue : Bool
round297RequiresFullCoherentEndpointAbsoluteValue = false

round297PhysicalCauchyKernelPositivityInstalled : Bool
round297PhysicalCauchyKernelPositivityInstalled = false

round297PhysicalDiagonalEndpointPaid : Bool
round297PhysicalDiagonalEndpointPaid = false

round297EndpointLeafClosed : Bool
round297EndpointLeafClosed = false

round297PackageAClosed : Bool
round297PackageAClosed = false

round297ClayPromotion : Bool
round297ClayPromotion = false

round297EndpointReductionClosedIsTrue : round297EndpointReductionClosed ≡ true
round297EndpointReductionClosedIsTrue = refl
