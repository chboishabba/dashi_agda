module DASHI.Foundations.Wette1969Rule915Premise18Rule93SearchExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: PREMISE-18 TERMINAL SEARCH INSIDE 9.3.1--30
--
-- The primary source calls 9.3.1--30 the thirty implication rules.  Premise 18
-- is itself an L judgement.  We therefore refine the generic terminal-production
-- normal form to a finite source-stable candidate carrier indexed by Fin 30.
--
-- This does NOT say that every 9.3 rule can conclude premise 18.  It says that
-- a terminal candidate in the implication family must identify the actual
-- certified terminal rule with one of the thirty historical 9.3 addresses.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915MajorPureWordRecoveryFrontierExact as Recovery
import DASHI.Foundations.Wette1969Rule915Premise18BackwardSearchExact as Backward
import DASHI.Foundations.Wette1969Rule93ImplicationFamilyExact as Rule93
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

Context = Finite.DerivationContext

record Premise18Rule93TerminalCandidate
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later)
    (recovery : Recovery.Rule915MajorPureWordRecovery later) : Set₁ where
  constructor premise18Rule93TerminalCandidate
  field
    rule93Candidate : Rule93.ImplicationRule93
    backwardCandidate :
      Backward.Premise18BackwardSearchCandidate
        firstSeven later scaffold recovery
    terminalAddressIsCandidate :
      RuleBody.address
        (PCRA.selectedRule
          (Backward.terminalRule
            (Backward.terminalProduction backwardCandidate)))
        ≡ Rule93.rule93Address rule93Candidate

open Premise18Rule93TerminalCandidate public

candidateStillProducesPremise18 :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  {recovery : Recovery.Rule915MajorPureWordRecovery later} →
  Premise18Rule93TerminalCandidate firstSeven later scaffold recovery →
  Backward.Premise18BackwardSearchCandidate firstSeven later scaffold recovery
candidateStillProducesPremise18 = backwardCandidate

record Wette1969Rule915Premise18Rule93SearchBoundary : Set where
  constructor wette1969Rule915Premise18Rule93SearchBoundary
  field
    terminalSearchNowHasFiniteThirtyAddressCarrier : Bool
    terminalSearchNowHasFiniteThirtyAddressCarrierIsTrue :
      terminalSearchNowHasFiniteThirtyAddressCarrier ≡ true

    candidateMustBeActualCertifiedHistoricalTerminalRule : Bool
    candidateMustBeActualCertifiedHistoricalTerminalRuleIsTrue :
      candidateMustBeActualCertifiedHistoricalTerminalRule ≡ true

    candidateAddressMustBeOneOf931Through9330 : Bool
    candidateAddressMustBeOneOf931Through9330IsTrue :
      candidateAddressMustBeOneOf931Through9330 ≡ true

    allThirtyRuleBodiesAlreadyAvailableForUnification : Bool
    allThirtyRuleBodiesAlreadyAvailableForUnificationIsFalse :
      allThirtyRuleBodiesAlreadyAvailableForUnification ≡ false

    finiteCarrierAloneProvesPremise18 : Bool
    finiteCarrierAloneProvesPremise18IsFalse :
      finiteCarrierAloneProvesPremise18 ≡ false

canonicalWette1969Rule915Premise18Rule93SearchBoundary :
  Wette1969Rule915Premise18Rule93SearchBoundary
canonicalWette1969Rule915Premise18Rule93SearchBoundary =
  wette1969Rule915Premise18Rule93SearchBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
