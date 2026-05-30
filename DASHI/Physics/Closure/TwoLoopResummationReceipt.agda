module DASHI.Physics.Closure.TwoLoopResummationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23Candidate14302Receipt as Candidate

data TwoLoopResummationTerm : Set where
  alphaOneOverTwo :
    TwoLoopResummationTerm

  alphaOneSquaredOverFour :
    TwoLoopResummationTerm

  denominatorOneMinusBothTerms :
    TwoLoopResummationTerm

  physicalInterpretationOpen :
    TwoLoopResummationTerm

canonicalTwoLoopResummationTerms : List TwoLoopResummationTerm
canonicalTwoLoopResummationTerms =
  alphaOneOverTwo
  ∷ alphaOneSquaredOverFour
  ∷ denominatorOneMinusBothTerms
  ∷ physicalInterpretationOpen
  ∷ []

twoLoopStatement : String
twoLoopStatement =
  "The two-loop-looking denominator 1-alpha1/2-alpha1^2/4 is a high-accuracy diagnostic pattern, not a derived arithmetic correction."

record TwoLoopResummationReceipt : Setω where
  field
    candidateReceipt :
      Candidate.Deg23Candidate14302Receipt

    candidateFormulaNotDerived :
      Candidate.deg23FormulaDerived candidateReceipt ≡ false

    terms :
      List TwoLoopResummationTerm

    termsAreCanonical :
      terms ≡ canonicalTwoLoopResummationTerms

    deg23TwoLoopFormulaCandidate :
      Bool

    deg23TwoLoopFormulaCandidateIsTrue :
      deg23TwoLoopFormulaCandidate ≡ true

    physicalInterpretationStillOpen :
      Bool

    physicalInterpretationStillOpenIsTrue :
      physicalInterpretationStillOpen ≡ true

    exactDeg23Derived :
      Bool

    exactDeg23DerivedIsFalse :
      exactDeg23Derived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ twoLoopStatement

open TwoLoopResummationReceipt public

canonicalTwoLoopResummationReceipt :
  TwoLoopResummationReceipt
canonicalTwoLoopResummationReceipt =
  record
    { candidateReceipt =
        Candidate.canonicalDeg23Candidate14302Receipt
    ; candidateFormulaNotDerived =
        refl
    ; terms =
        canonicalTwoLoopResummationTerms
    ; termsAreCanonical =
        refl
    ; deg23TwoLoopFormulaCandidate =
        true
    ; deg23TwoLoopFormulaCandidateIsTrue =
        refl
    ; physicalInterpretationStillOpen =
        true
    ; physicalInterpretationStillOpenIsTrue =
        refl
    ; exactDeg23Derived =
        false
    ; exactDeg23DerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; statement =
        twoLoopStatement
    ; statementIsCanonical =
        refl
    }
