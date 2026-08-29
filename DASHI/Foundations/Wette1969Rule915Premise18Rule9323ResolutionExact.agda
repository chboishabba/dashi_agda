module DASHI.Foundations.Wette1969Rule915Premise18Rule9323ResolutionExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5 PREMISE 18: 9.3.23 -> CORE LEAF -> D18
--
-- Rule 9.3.23 is Wette's printed complete-induction rule.  It is not generic
-- predecessor induction relative to arbitrary R.  This module therefore asks
-- for an *actual matched instance*: after an arbitrary certified prefix, the
-- five historical 9.3.23 premises must all be available and its conclusion
-- must be identified with the p.145 premise-18 core leaf.
--
-- Once those receipts exist, one certified 9.3.23 step constructs the core
-- leaf, and Wette1969Rule915Premise18CoreLeafClosureExact supplies the two
-- source-exact 9.3.9 currying steps to D18.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969Rule915Premise18ImplicationSpineExact as Spine
import DASHI.Foundations.Wette1969Rule915Premise18CoreLeafClosureExact as Closure18
import DASHI.Foundations.Wette1969Rule9323InductionExact as Rule9323
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record Rule9323MatchedCoreLeafAttempt
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) : Set₁ where
  constructor rule9323MatchedCoreLeafAttempt
  field
    p145SpineRecovery : Spine.Premise18P145SpineRecovery later

    prefix :
      PCRA.CertifiedRuleTrace
        historicalSystem
        (Source.sourceExactScaffoldTarget scaffold)

    inductionVariable : WordTerm
    inductionBody : WordTerm
    successorInstance : WordTerm
    zeroInstance : WordTerm

    variableEvidence :
      Judgment.naturalVariable inductionVariable Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem prefix)
    bodyEvidence :
      Judgment.assertionSchema inductionBody Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem prefix)
    successorSubstitutionEvidence :
      Judgment.substitution
        inductionVariable inductionBody
        (Rule9323.successor inductionVariable)
        successorInstance
        Finite.∈Context (PCRA.runCertifiedTrace historicalSystem prefix)
    zeroSubstitutionEvidence :
      Judgment.substitution
        inductionVariable inductionBody
        Rule9323.zeroWord
        zeroInstance
        Finite.∈Context (PCRA.runCertifiedTrace historicalSystem prefix)
    inductionStepEvidence :
      Judgment.implies inductionBody successorInstance Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem prefix)

    rule9323ConclusionIsCoreLeaf :
      Judgment.implies zeroInstance inductionBody ≡ Spine.coreLeaf later

open Rule9323MatchedCoreLeafAttempt public

prefixTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Rule9323MatchedCoreLeafAttempt firstSeven later scaffold → Context
prefixTarget attempt = PCRA.runCertifiedTrace historicalSystem (prefix attempt)

selectedRule9323 :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Rule9323MatchedCoreLeafAttempt firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem (prefixTarget attempt)
selectedRule9323 attempt =
  Rule9323.selectRule9323
    (prefixTarget attempt)
    (inductionVariable attempt)
    (inductionBody attempt)
    (successorInstance attempt)
    (zeroInstance attempt)
    (variableEvidence attempt)
    (bodyEvidence attempt)
    (successorSubstitutionEvidence attempt)
    (zeroSubstitutionEvidence attempt)
    (inductionStepEvidence attempt)

rule9323Target :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Rule9323MatchedCoreLeafAttempt firstSeven later scaffold → Context
rule9323Target attempt =
  PCRA.applySelected historicalSystem (selectedRule9323 attempt)

coreLeafAtRule9323Target :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Rule9323MatchedCoreLeafAttempt firstSeven later scaffold) →
  Spine.coreLeaf later Finite.∈Context (rule9323Target attempt)
coreLeafAtRule9323Target attempt
  rewrite sym (rule9323ConclusionIsCoreLeaf attempt) =
  Closure.certifiedConclusionAvailable
    (prefixTarget attempt)
    (selectedRule9323 attempt)

coreLeafTrace :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Rule9323MatchedCoreLeafAttempt firstSeven later scaffold) →
  PCRA.CertifiedRuleTrace
    historicalSystem
    (Source.sourceExactScaffoldTarget scaffold)
coreLeafTrace attempt =
  PCRA.appendCertifiedTrace
    (prefix attempt)
    (PCRA.choose (selectedRule9323 attempt) PCRA.done)

coreLeafAtTraceTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Rule9323MatchedCoreLeafAttempt firstSeven later scaffold) →
  Spine.coreLeaf later Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem (coreLeafTrace attempt))
coreLeafAtTraceTarget attempt
  rewrite PCRA.runAppendCertifiedTrace
    (prefix attempt)
    (PCRA.choose (selectedRule9323 attempt) PCRA.done) =
  coreLeafAtRule9323Target attempt

asCoreLeafAttempt :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Rule9323MatchedCoreLeafAttempt firstSeven later scaffold) →
  Closure18.Premise18CoreLeafAttempt firstSeven later scaffold
asCoreLeafAttempt attempt =
  Closure18.premise18CoreLeafAttempt
    (p145SpineRecovery attempt)
    (Join.certifiedMajorTrace
      (coreLeafTrace attempt)
      (coreLeafAtTraceTarget attempt))

matchedRule9323ClosesPremise18 :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Rule9323MatchedCoreLeafAttempt firstSeven later scaffold) →
  Join.CertifiedMajorTrace
    (Source.sourceExactScaffoldTarget scaffold)
    (Later.premise18 later)
matchedRule9323ClosesPremise18 attempt =
  Closure18.coreLeafAttemptClosesPremise18 (asCoreLeafAttempt attempt)

record Wette1969Rule915Premise18Rule9323ResolutionBoundary : Set where
  constructor wette1969Rule915Premise18Rule9323ResolutionBoundary
  field
    matched9323PremisesProduceCoreLeaf : Bool
    matched9323PremisesProduceCoreLeafIsTrue :
      matched9323PremisesProduceCoreLeaf ≡ true
    coreLeafThenClosesD18ByTwoRule939Steps : Bool
    coreLeafThenClosesD18ByTwoRule939StepsIsTrue :
      coreLeafThenClosesD18ByTwoRule939Steps ≡ true
    completeResolutionUsesActualProofCarryingHistoricalSteps : Bool
    completeResolutionUsesActualProofCarryingHistoricalStepsIsTrue :
      completeResolutionUsesActualProofCarryingHistoricalSteps ≡ true
    genericScaffoldAutomaticallySuppliesFive9323Premises : Bool
    genericScaffoldAutomaticallySuppliesFive9323PremisesIsFalse :
      genericScaffoldAutomaticallySuppliesFive9323Premises ≡ false
    arbitraryRelationRIsAutomaticallyHandledBy9323 : Bool
    arbitraryRelationRIsAutomaticallyHandledBy9323IsFalse :
      arbitraryRelationRIsAutomaticallyHandledBy9323 ≡ false

canonicalWette1969Rule915Premise18Rule9323ResolutionBoundary :
  Wette1969Rule915Premise18Rule9323ResolutionBoundary
canonicalWette1969Rule915Premise18Rule9323ResolutionBoundary =
  wette1969Rule915Premise18Rule9323ResolutionBoundary
    true refl true refl true refl false refl false refl
