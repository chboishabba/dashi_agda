module DASHI.Physics.Closure.NSTriadKNCauchyFullVsSignedFluxBoundaryRound484Exact where

------------------------------------------------------------------------
-- ROUND484 / FULL CAUCHY FORM IS A PRODUCER, NOT THE SIGNED-FLUX CONSUMER
--
-- Same-object correction discovered by R481 proof search.
--
-- R473/R432 consume the signed cross / Gram debt.  On the literal physical
-- Cauchy carrier, R447/R448 instead give three distinct scalars:
--
--   full = diagonal + offDiagonal
--   offDiagonal = literal R397/R385 weighted signed flux.
--
-- Therefore
--
--   full != offDiagonal
--
-- as a same-object identification unless an additional diagonal = 0 receipt is
-- supplied.  No such receipt is part of the physical route.
--
-- A FULL upper bound is still a valid sufficient producer for the signed flux:
-- if 0 <= diagonal and full <= budget, then offDiagonal <= full <= budget.
-- Thus R477/R478 remain useful producer routes, but they are strictly stronger
-- than the literal R432/R397 signed-flux consumer and must not be used as its
-- identity receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Generic algebra/order boundary.
------------------------------------------------------------------------

fullEqualsOffDiagonalForcesDiagonalZero :
  (full diagonal offDiagonal : ℚ) →
  full ≡ diagonal + offDiagonal →
  full ≡ offDiagonal →
  diagonal ≡ 0ℚ
fullEqualsOffDiagonalForcesDiagonalZero full diagonal offDiagonal fullSplit fullIsOff =
  let
    cancelled :
      (diagonal + offDiagonal) - offDiagonal ≡ offDiagonal - offDiagonal
    cancelled =
      cong (λ selected → selected - offDiagonal)
        (trans (sym fullSplit) fullIsOff)

    leftNormal : (diagonal + offDiagonal) - offDiagonal ≡ diagonal
    leftNormal = solve (diagonal ∷ offDiagonal ∷ [])

    rightNormal : offDiagonal - offDiagonal ≡ 0ℚ
    rightNormal = solve (offDiagonal ∷ [])
  in
  trans (sym leftNormal) (trans cancelled rightNormal)

offDiagonalBelowFull :
  (full diagonal offDiagonal : ℚ) →
  full ≡ diagonal + offDiagonal →
  0ℚ ≤ diagonal →
  offDiagonal ≤ full
offDiagonalBelowFull full diagonal offDiagonal fullSplit diagonalNN =
  let
    add : offDiagonal ≤ diagonal + offDiagonal
    add =
      subst
        (offDiagonal ≤_)
        (ℚP.+-comm diagonal offDiagonal)
        (ℚP.+-monoˡ-≤ offDiagonal diagonalNN)
  in
  subst (offDiagonal ≤_) (sym fullSplit) add

fullUpperBoundPaysOffDiagonal :
  (full diagonal offDiagonal budget : ℚ) →
  full ≡ diagonal + offDiagonal →
  0ℚ ≤ diagonal →
  full ≤ budget →
  offDiagonal ≤ budget
fullUpperBoundPaysOffDiagonal full diagonal offDiagonal budget fullSplit diagonalNN fullBound =
  ℚP.≤-trans
    (offDiagonalBelowFull full diagonal offDiagonal fullSplit diagonalNN)
    fullBound

------------------------------------------------------------------------
-- Search / trust boundary.
------------------------------------------------------------------------

round484R432ConsumerIsSignedFluxNotFullCauchyForm : Bool
round484R432ConsumerIsSignedFluxNotFullCauchyForm = true

round484R448IdentifiesLiteralSignedFluxWithOffDiagonal : Bool
round484R448IdentifiesLiteralSignedFluxWithOffDiagonal = true

round484FullFormSameObjectAsSignedFlux : Bool
round484FullFormSameObjectAsSignedFlux = false

round484FullUpperBoundIsSufficientProducerForSignedFlux : Bool
round484FullUpperBoundIsSufficientProducerForSignedFlux = true

round484FullUpperBoundIsMandatoryProducerForSignedFlux : Bool
round484FullUpperBoundIsMandatoryProducerForSignedFlux = false

round484PreferredTerminalLeafIsPositiveSignedFluxAllowance : Bool
round484PreferredTerminalLeafIsPositiveSignedFluxAllowance = true

round484PositiveSignedFluxAllowanceClosed : Bool
round484PositiveSignedFluxAllowanceClosed = false

round484PackageAClosed : Bool
round484PackageAClosed = false

round484ClayPromotion : Bool
round484ClayPromotion = false

round484FullFormSameObjectAsSignedFluxIsFalse :
  round484FullFormSameObjectAsSignedFlux ≡ false
round484FullFormSameObjectAsSignedFluxIsFalse = refl

round484PositiveSignedFluxAllowanceClosedIsFalse :
  round484PositiveSignedFluxAllowanceClosed ≡ false
round484PositiveSignedFluxAllowanceClosedIsFalse = refl

round484ClayPromotionIsFalse : round484ClayPromotion ≡ false
round484ClayPromotionIsFalse = refl
