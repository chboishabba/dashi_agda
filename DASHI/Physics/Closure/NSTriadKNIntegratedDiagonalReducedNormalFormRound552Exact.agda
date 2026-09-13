module DASHI.Physics.Closure.NSTriadKNIntegratedDiagonalReducedNormalFormRound552Exact where

------------------------------------------------------------------------
-- ROUND552 / INTEGRATE THE R551 DIAGONAL-REDUCED NORMAL FORM
--
-- R495 gives only congruence, zero and finite additivity.  Those laws already
-- derive integration of rational negation/subtraction and multiplication by
-- two.  Hence any pointwise R551-shaped identity
--
--   2 R = F - G - T
--
-- integrates exactly to
--
--   2 int R = int F - int G - int T.
--
-- No FTC, positivity or Navier--Stokes estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539

module Integrated
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  integrateNeg :
    (f : Time → ℚ) (terminal : Time) →
    integrateTo (λ t → 0ℚ - f t) terminal
    ≡ 0ℚ - integrateTo f terminal
  integrateNeg f terminal =
    let
      negf : Time → ℚ
      negf t = 0ℚ - f t

      pointwiseZero : (t : Time) → f t + negf t ≡ 0ℚ
      pointwiseZero t = solve (f t ∷ [])

      sumToZeroIntegral :
        integrateTo (λ t → f t + negf t) terminal
        ≡ integrateTo (λ _ → 0ℚ) terminal
      sumToZeroIntegral =
        R495.integrateCongruent integration
          (λ t → f t + negf t) (λ _ → 0ℚ)
          pointwiseZero terminal

      integratedEquation :
        integrateTo f terminal + integrateTo negf terminal ≡ 0ℚ
      integratedEquation =
        trans
          (sym (R495.integrateAdd integration f negf terminal))
          (trans sumToZeroIntegral (R495.integrateZero integration terminal))

      subtractLeft =
        cong (λ x → x - integrateTo f terminal) integratedEquation
    in
    trans
      (sym
        (solve
          (integrateTo f terminal
            ∷ integrateTo negf terminal
            ∷ [])))
      subtractLeft

  integrateSubtract :
    (f g : Time → ℚ) (terminal : Time) →
    integrateTo (λ t → f t - g t) terminal
    ≡ integrateTo f terminal - integrateTo g terminal
  integrateSubtract f g terminal =
    let
      negG : Time → ℚ
      negG t = 0ℚ - g t

      subtractionAsAdd :
        (t : Time) → f t - g t ≡ f t + negG t
      subtractionAsAdd t = solve (f t ∷ g t ∷ [])
    in
    trans
      (R495.integrateCongruent integration
        (λ t → f t - g t)
        (λ t → f t + negG t)
        subtractionAsAdd terminal)
      (trans
        (R495.integrateAdd integration f negG terminal)
        (cong (integrateTo f terminal +_)
          (integrateNeg g terminal)))

  integrateTwo :
    (f : Time → ℚ) (terminal : Time) →
    integrateTo (λ t → R539.two * f t) terminal
    ≡ R539.two * integrateTo f terminal
  integrateTwo f terminal =
    let
      twiceAsAdd : (t : Time) → R539.two * f t ≡ f t + f t
      twiceAsAdd t = solve (f t ∷ [])
    in
    trans
      (R495.integrateCongruent integration
        (λ t → R539.two * f t)
        (λ t → f t + f t)
        twiceAsAdd terminal)
      (trans
        (R495.integrateAdd integration f f terminal)
        (solve (integrateTo f terminal ∷ [])))

  integratedReducedNormalForm :
    (remainder factored selfGram selfFluxTangent : Time → ℚ) →
    ((t : Time) →
      R539.two * remainder t
      ≡ (factored t - selfGram t) - selfFluxTangent t) →
    (terminal : Time) →
    R539.two * integrateTo remainder terminal
    ≡ (integrateTo factored terminal - integrateTo selfGram terminal)
        - integrateTo selfFluxTangent terminal
  integratedReducedNormalForm remainder factored selfGram selfFluxTangent
      pointwise terminal =
    let
      transport =
        R495.integrateCongruent integration
          (λ t → R539.two * remainder t)
          (λ t → (factored t - selfGram t) - selfFluxTangent t)
          pointwise terminal

      left = integrateTwo remainder terminal
      firstSubtract = integrateSubtract factored selfGram terminal
      secondSubtract =
        integrateSubtract
          (λ t → factored t - selfGram t)
          selfFluxTangent terminal
    in
    trans
      (sym left)
      (trans transport
        (trans secondSubtract
          (cong (λ x → x - integrateTo selfFluxTangent terminal)
            firstSubtract)))

round552R495DerivesNegationTransport : Bool
round552R495DerivesNegationTransport = true

round552R495DerivesSubtractionTransport : Bool
round552R495DerivesSubtractionTransport = true

round552IntegratedDiagonalReducedNormalFormClosed : Bool
round552IntegratedDiagonalReducedNormalFormClosed = true

round552FTCIntroduced : Bool
round552FTCIntroduced = false

round552SignedSpacetimeEstimateClosed : Bool
round552SignedSpacetimeEstimateClosed = false

round552ClayPromotion : Bool
round552ClayPromotion = false

round552IntegratedDiagonalReducedNormalFormClosedIsTrue :
  round552IntegratedDiagonalReducedNormalFormClosed ≡ true
round552IntegratedDiagonalReducedNormalFormClosedIsTrue = refl

round552ClayPromotionIsFalse : round552ClayPromotion ≡ false
round552ClayPromotionIsFalse = refl
