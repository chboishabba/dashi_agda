module DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact where

------------------------------------------------------------------------
-- ROUND303 / ENDPOINT + WEIGHTED REMAINDER -> SIGNED INTEGRATED GRAM PAYMENT
--
-- The temporal route now has the exact integrated form
--
--   integral D_Gram
--     = F_off(0) - F_off(T) + integral R_weighted.
--
-- R302 pays the first two terms asymmetrically.  R300/R301 are responsible for
-- the weighted nonlinear remainder.  This file contains only the final ordered
-- scalar compiler into the signed-integral upper bound consumed by R293.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record SignedGramFluxPayment : Set where
  constructor signed-gram-flux-payment
  field
    signedGramIntegral initialFlux terminalNegativeFlux weightedRemainderIntegral : ℚ
    initialUpper terminalUpper remainderUpper : ℚ

    fluxIdentity :
      signedGramIntegral
      ≡ initialFlux + terminalNegativeFlux + weightedRemainderIntegral

    initialPaid : initialFlux ≤ initialUpper
    terminalPaid : terminalNegativeFlux ≤ terminalUpper
    remainderPaid : weightedRemainderIntegral ≤ remainderUpper

open SignedGramFluxPayment public

signedGramUpperBound : SignedGramFluxPayment → ℚ
signedGramUpperBound P = initialUpper P + terminalUpper P + remainderUpper P

signedGramIntegralPaid :
  (P : SignedGramFluxPayment) →
  signedGramIntegral P ≤ signedGramUpperBound P
signedGramIntegralPaid P =
  let
    first = ℚP.+-mono-≤ (initialPaid P) (terminalPaid P)
    second = ℚP.+-mono-≤ first (remainderPaid P)

    sourceNormalize :
      (initialFlux P + terminalNegativeFlux P) + weightedRemainderIntegral P
      ≡ initialFlux P + terminalNegativeFlux P + weightedRemainderIntegral P
    sourceNormalize = solve
      (initialFlux P ∷ terminalNegativeFlux P ∷ weightedRemainderIntegral P ∷ [])

    targetNormalize :
      (initialUpper P + terminalUpper P) + remainderUpper P
      ≡ signedGramUpperBound P
    targetNormalize = solve
      (initialUpper P ∷ terminalUpper P ∷ remainderUpper P ∷ [])
  in
  subst
    (λ left → left ≤ signedGramUpperBound P)
    (fluxIdentity P)
    (subst
      (λ left → left ≤ signedGramUpperBound P)
      sourceNormalize
      (subst
        (((initialFlux P + terminalNegativeFlux P)
          + weightedRemainderIntegral P) ≤_)
        targetNormalize
        second))

round303SignedGramFluxCompilerClosed : Bool
round303SignedGramFluxCompilerClosed = true

round303InitialEndpointPaid : Bool
round303InitialEndpointPaid = false

round303TerminalEndpointPaid : Bool
round303TerminalEndpointPaid = false

round303WeightedRemainderPaid : Bool
round303WeightedRemainderPaid = false

round303PhysicalSignedGramIntegralPaid : Bool
round303PhysicalSignedGramIntegralPaid = false

round303FeedsR293SignedConsumer : Bool
round303FeedsR293SignedConsumer = true

round303PackageAClosed : Bool
round303PackageAClosed = false

round303ClayPromotion : Bool
round303ClayPromotion = false

round303SignedGramFluxCompilerClosedIsTrue :
  round303SignedGramFluxCompilerClosed ≡ true
round303SignedGramFluxCompilerClosedIsTrue = refl
