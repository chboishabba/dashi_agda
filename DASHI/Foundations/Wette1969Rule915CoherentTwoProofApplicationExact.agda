module DASHI.Foundations.Wette1969Rule915CoherentTwoProofApplicationExact where

------------------------------------------------------------------------
-- COHERENT SAME-OBJECT 9.1.5 TWO-PROOF APPLICATION
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969Rule915ParameterCoherenceExact as Coherent
import DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact as Cutset
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Cutset.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record CoherentTwoProofApplicationInputs
    (context : Context)
    (parameters : Coherent.CoherentRule915Parameters) : Set where
  constructor coherentTwoProofApplicationInputs
  field
    recursivePredicate : WordTerm
    scaffold :
      Cutset.Rule915SyntacticScaffoldEvidence
        context
        (Coherent.firstSeven parameters)
        (Coherent.laterTwenty parameters)
    majorProofs :
      Cutset.Rule915MajorProofEvidence
        context
        (Coherent.laterTwenty parameters)

open CoherentTwoProofApplicationInputs public

selectCoherentRule915 :
  {context : Context} →
  (parameters : Coherent.CoherentRule915Parameters) →
  CoherentTwoProofApplicationInputs context parameters →
  PCRA.SelectedRuleApplication historicalSystem context
selectCoherentRule915 parameters inputs =
  Cutset.selectRule915FromTwoProofCutset
    (Coherent.firstSeven parameters)
    (Coherent.laterTwenty parameters)
    (recursivePredicate inputs)
    (scaffold inputs)
    (majorProofs inputs)

record Wette1969Rule915CoherentTwoProofApplicationBoundary : Set where
  constructor wette1969Rule915CoherentTwoProofApplicationBoundary
  field
    twoProofCutsetNowHasSameObjectParameterWeld : Bool
    twoProofCutsetNowHasSameObjectParameterWeldIsTrue :
      twoProofCutsetNowHasSameObjectParameterWeld ≡ true
    sameObjectWeldDoesNotReplacePremiseProofs : Bool
    sameObjectWeldDoesNotReplacePremiseProofsIsTrue :
      sameObjectWeldDoesNotReplacePremiseProofs ≡ true

canonicalWette1969Rule915CoherentTwoProofApplicationBoundary :
  Wette1969Rule915CoherentTwoProofApplicationBoundary
canonicalWette1969Rule915CoherentTwoProofApplicationBoundary =
  wette1969Rule915CoherentTwoProofApplicationBoundary true refl true refl
