module DASHI.Foundations.Wette1969Rule915Premise18BackwardSearchExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: PREMISE-18 BACKWARD SEARCH NORMAL FORM
--
-- The repository does not yet contain the complete historical rule catalogue,
-- so it would be unsound to enumerate all possible final rules for premise 18.
-- What we can require exactly is a terminal-production certificate:
--
--   certified prefix trace
--   + one actual certified historical rule at the reached context
--   + equality identifying that rule's conclusion with the recovered premise 18
--
-- This is the correct proof-search normal form for backward reasoning while the
-- source recovery of the remaining rule families is still incomplete.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915MajorPureWordRecoveryFrontierExact as Recovery
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Formula = Signature.Formula
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record TerminalHistoricalProduction
    (start : Context)
    (goal : Formula) : Set₁ where
  constructor terminalHistoricalProduction
  field
    prefix : PCRA.CertifiedRuleTrace historicalSystem start
    terminalRule :
      PCRA.SelectedRuleApplication
        historicalSystem
        (PCRA.runCertifiedTrace historicalSystem prefix)
    terminalConclusionIsGoal :
      RuleBody.conclusion (PCRA.selectedRule terminalRule) ≡ goal

open TerminalHistoricalProduction public

terminalOneStepTrace :
  {start : Context} {goal : Formula} →
  TerminalHistoricalProduction start goal →
  PCRA.CertifiedRuleTrace
    historicalSystem
    (PCRA.runCertifiedTrace historicalSystem
      (prefix _))
terminalOneStepTrace production =
  PCRA.choose (terminalRule production) PCRA.done

terminalProductionTrace :
  {start : Context} {goal : Formula} →
  (production : TerminalHistoricalProduction start goal) →
  PCRA.CertifiedRuleTrace historicalSystem start
terminalProductionTrace production =
  PCRA.appendCertifiedTrace
    (prefix production)
    (terminalOneStepTrace production)

terminalGoalAtOneStepTarget :
  {start : Context} {goal : Formula} →
  (production : TerminalHistoricalProduction start goal) →
  goal Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem
      (terminalOneStepTrace production))
terminalGoalAtOneStepTarget production
  rewrite terminalConclusionIsGoal production =
  Closure.certifiedConclusionAvailable
    (PCRA.runCertifiedTrace historicalSystem (prefix production))
    (terminalRule production)

asCertifiedMajorTrace :
  {start : Context} {goal : Formula} →
  (production : TerminalHistoricalProduction start goal) →
  Join.CertifiedMajorTrace start goal
asCertifiedMajorTrace production =
  Join.certifiedMajorTrace
    (terminalProductionTrace production)
    targetEvidence
  where
    targetEvidence :
      goal Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem
          (terminalProductionTrace production))
    targetEvidence
      rewrite PCRA.runAppendCertifiedTrace
        (prefix production)
        (terminalOneStepTrace production) =
      terminalGoalAtOneStepTarget production

record Premise18BackwardSearchCandidate
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later)
    (recovery : Recovery.Rule915MajorPureWordRecovery later) : Set₁ where
  constructor premise18BackwardSearchCandidate
  field
    terminalProduction :
      TerminalHistoricalProduction
        (Source.sourceExactScaffoldTarget scaffold)
        (Recovery.premise18PureFormula later recovery)

open Premise18BackwardSearchCandidate public

premise18CandidateAsPureMajorTrace :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  {recovery : Recovery.Rule915MajorPureWordRecovery later} →
  Premise18BackwardSearchCandidate firstSeven later scaffold recovery →
  Join.CertifiedMajorTrace
    (Source.sourceExactScaffoldTarget scaffold)
    (Recovery.premise18PureFormula later recovery)
premise18CandidateAsPureMajorTrace candidate =
  asCertifiedMajorTrace (terminalProduction candidate)

premise18CandidateAsTypedMajorTrace :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  {recovery : Recovery.Rule915MajorPureWordRecovery later} →
  Premise18BackwardSearchCandidate firstSeven later scaffold recovery →
  Join.CertifiedMajorTrace
    (Source.sourceExactScaffoldTarget scaffold)
    (Later.premise18 later)
premise18CandidateAsTypedMajorTrace
  {later = later} {recovery = recovery} candidate
  with Recovery.premise18PureFormulaMatchesTypedSlot later recovery
... | refl = premise18CandidateAsPureMajorTrace candidate

terminalPremise18RuleHasHistoricalLRelator :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  {recovery : Recovery.Rule915MajorPureWordRecovery later} →
  (candidate : Premise18BackwardSearchCandidate firstSeven later scaffold recovery) →
  Signature.relator
    (RuleBody.conclusion
      (PCRA.selectedRule
        (terminalRule (terminalProduction candidate))))
    ≡ Signature.implicationDerivabilityRelator
terminalPremise18RuleHasHistoricalLRelator candidate
  rewrite terminalConclusionIsGoal (terminalProduction candidate) = refl

record Wette1969Rule915Premise18BackwardSearchBoundary : Set where
  constructor wette1969Rule915Premise18BackwardSearchBoundary
  field
    backwardCandidateEndsInActualCertifiedHistoricalRule : Bool
    backwardCandidateEndsInActualCertifiedHistoricalRuleIsTrue :
      backwardCandidateEndsInActualCertifiedHistoricalRule ≡ true

    terminalRuleMustConcludeRecoveredPremise18Exactly : Bool
    terminalRuleMustConcludeRecoveredPremise18ExactlyIsTrue :
      terminalRuleMustConcludeRecoveredPremise18Exactly ≡ true

    terminalPremise18RuleMustHaveHistoricalLRelator : Bool
    terminalPremise18RuleMustHaveHistoricalLRelatorIsTrue :
      terminalPremise18RuleMustHaveHistoricalLRelator ≡ true

    arbitraryCertifiedPrefixBeforeTerminalStepIsAllowed : Bool
    arbitraryCertifiedPrefixBeforeTerminalStepIsAllowedIsTrue :
      arbitraryCertifiedPrefixBeforeTerminalStepIsAllowed ≡ true

    currentRepositoryEnumeratesAllHistoricalTerminalRulesForPremise18 : Bool
    currentRepositoryEnumeratesAllHistoricalTerminalRulesForPremise18IsFalse :
      currentRepositoryEnumeratesAllHistoricalTerminalRulesForPremise18 ≡ false

    backwardSearchInterfaceManufacturesPremise18Derivation : Bool
    backwardSearchInterfaceManufacturesPremise18DerivationIsFalse :
      backwardSearchInterfaceManufacturesPremise18Derivation ≡ false

canonicalWette1969Rule915Premise18BackwardSearchBoundary :
  Wette1969Rule915Premise18BackwardSearchBoundary
canonicalWette1969Rule915Premise18BackwardSearchBoundary =
  wette1969Rule915Premise18BackwardSearchBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
