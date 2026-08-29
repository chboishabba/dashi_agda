module DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: JOIN INDEPENDENT MAJOR-PROOF TRACES
--
-- Premises 18 and 27 are genuinely separate L-proof obligations.  Requiring
-- both finished proofs to inhabit one pre-existing derivation context would add
-- an artificial coupling not present in the source.  Both proof attempts may
-- instead start from the same generated source-exact scaffold.  After the first
-- trace runs, monotone replay weakens the second trace over the enlarged
-- context.  The joined target therefore contains the preserved syntactic
-- scaffold and both substantive proof conclusions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact as Cutset
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969CertifiedTraceWeakeningExact as Weakening
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Formula = Signature.Formula
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record CertifiedMajorTrace (start : Context) (goal : Formula) : Set₁ where
  constructor certifiedMajorTrace
  field
    trace : PCRA.CertifiedRuleTrace historicalSystem start
    goalAtTarget :
      goal Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem trace)

open CertifiedMajorTrace public

record IndependentMajorTraceInputs
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) : Set₁ where
  constructor independentMajorTraceInputs
  field
    inductionAttempt :
      CertifiedMajorTrace
        (Source.sourceExactScaffoldTarget scaffold)
        (Later.premise18 later)
    independenceAttempt :
      CertifiedMajorTrace
        (Source.sourceExactScaffoldTarget scaffold)
        (Later.premise27 later)

open IndependentMajorTraceInputs public

preserveScaffoldThroughInduction :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  Weakening.PreservesContext
    (Source.sourceExactScaffoldTarget scaffold)
    (PCRA.runCertifiedTrace historicalSystem
      (trace (inductionAttempt inputs)))
preserveScaffoldThroughInduction inputs formula evidence =
  Closure.certifiedTracePreservesPriorFormula
    (trace (inductionAttempt inputs)) formula evidence

weakenedIndependenceAttempt :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  Weakening.WeakenedCertifiedTrace
    (preserveScaffoldThroughInduction inputs)
    (trace (independenceAttempt inputs))
weakenedIndependenceAttempt inputs =
  Weakening.weakenCertifiedTrace
    (preserveScaffoldThroughInduction inputs)
    (trace (independenceAttempt inputs))

replayedIndependenceTrace :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  PCRA.CertifiedRuleTrace historicalSystem
    (PCRA.runCertifiedTrace historicalSystem
      (trace (inductionAttempt inputs)))
replayedIndependenceTrace inputs =
  Weakening.replay (weakenedIndependenceAttempt inputs)

joinedMajorTrace :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  PCRA.CertifiedRuleTrace historicalSystem
    (Source.sourceExactScaffoldTarget scaffold)
joinedMajorTrace inputs =
  PCRA.appendCertifiedTrace
    (trace (inductionAttempt inputs))
    (replayedIndependenceTrace inputs)

joinedMajorTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  IndependentMajorTraceInputs firstSeven later scaffold →
  Context
joinedMajorTarget inputs =
  PCRA.runCertifiedTrace historicalSystem
    (replayedIndependenceTrace inputs)

joinedTraceTargetAgreement :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  PCRA.runCertifiedTrace historicalSystem (joinedMajorTrace inputs)
    ≡ joinedMajorTarget inputs
joinedTraceTargetAgreement inputs =
  PCRA.runAppendCertifiedTrace
    (trace (inductionAttempt inputs))
    (replayedIndependenceTrace inputs)

preserveScaffoldToJoinedTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  Weakening.PreservesContext
    (Source.sourceExactScaffoldTarget scaffold)
    (joinedMajorTarget inputs)
preserveScaffoldToJoinedTarget inputs formula evidence =
  Closure.certifiedTracePreservesPriorFormula
    (replayedIndependenceTrace inputs) formula
    (Closure.certifiedTracePreservesPriorFormula
      (trace (inductionAttempt inputs)) formula evidence)

transportScaffoldEvidence :
  {before after : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  Weakening.PreservesContext before after →
  Cutset.Rule915SyntacticScaffoldEvidence before firstSeven later →
  Cutset.Rule915SyntacticScaffoldEvidence after firstSeven later
transportScaffoldEvidence preserve scaffold =
  Cutset.rule915SyntacticScaffoldEvidence
    (preserve _ (Cutset.p01 scaffold))
    (preserve _ (Cutset.p02 scaffold))
    (preserve _ (Cutset.p03 scaffold))
    (preserve _ (Cutset.p04 scaffold))
    (preserve _ (Cutset.p05 scaffold))
    (preserve _ (Cutset.p06 scaffold))
    (preserve _ (Cutset.p07 scaffold))
    (preserve _ (Cutset.p08 scaffold))
    (preserve _ (Cutset.p09 scaffold))
    (preserve _ (Cutset.p10 scaffold))
    (preserve _ (Cutset.p11 scaffold))
    (preserve _ (Cutset.p12 scaffold))
    (preserve _ (Cutset.p13 scaffold))
    (preserve _ (Cutset.p14 scaffold))
    (preserve _ (Cutset.p15 scaffold))
    (preserve _ (Cutset.p16 scaffold))
    (preserve _ (Cutset.p17 scaffold))
    (preserve _ (Cutset.p19 scaffold))
    (preserve _ (Cutset.p20 scaffold))
    (preserve _ (Cutset.p21 scaffold))
    (preserve _ (Cutset.p22 scaffold))
    (preserve _ (Cutset.p23 scaffold))
    (preserve _ (Cutset.p24 scaffold))
    (preserve _ (Cutset.p25 scaffold))
    (preserve _ (Cutset.p26 scaffold))

joinedScaffoldEvidence :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  Cutset.Rule915SyntacticScaffoldEvidence
    (joinedMajorTarget inputs) firstSeven later
joinedScaffoldEvidence firstSeven later scaffold inputs =
  transportScaffoldEvidence
    (preserveScaffoldToJoinedTarget inputs)
    (Source.scaffoldEvidenceAtSourceExactTarget
      firstSeven later scaffold)

premise18AtJoinedTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  Later.premise18 later Finite.∈Context (joinedMajorTarget inputs)
premise18AtJoinedTarget inputs =
  Closure.certifiedTracePreservesPriorFormula
    (replayedIndependenceTrace inputs)
    _
    (goalAtTarget (inductionAttempt inputs))

premise27AtJoinedTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  Later.premise27 later Finite.∈Context (joinedMajorTarget inputs)
premise27AtJoinedTarget inputs =
  Weakening.targetPreservation
    (weakenedIndependenceAttempt inputs)
    _
    (goalAtTarget (independenceAttempt inputs))

joinedMajorProofEvidence :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  Cutset.Rule915MajorProofEvidence (joinedMajorTarget inputs) later
joinedMajorProofEvidence inputs =
  Cutset.rule915MajorProofEvidence
    (premise18AtJoinedTarget inputs)
    (premise27AtJoinedTarget inputs)

selectRule915FromIndependentMajorTraces :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (recursivePredicate : WordTerm) →
  (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) →
  (inputs : IndependentMajorTraceInputs firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem (joinedMajorTarget inputs)
selectRule915FromIndependentMajorTraces
  firstSeven later recursivePredicate scaffold inputs =
  Cutset.selectRule915FromTwoProofCutset
    firstSeven later recursivePredicate
    (joinedScaffoldEvidence firstSeven later scaffold inputs)
    (joinedMajorProofEvidence inputs)

record Wette1969Rule915IndependentMajorTraceJoinBoundary : Set where
  constructor wette1969Rule915IndependentMajorTraceJoinBoundary
  field
    premise18And27TracesMayStartIndependentlyFromSameScaffold : Bool
    premise18And27TracesMayStartIndependentlyFromSameScaffoldIsTrue :
      premise18And27TracesMayStartIndependentlyFromSameScaffold ≡ true
    secondMajorTraceReplaysOverFirstWithoutChangingRuleBodies : Bool
    secondMajorTraceReplaysOverFirstWithoutChangingRuleBodiesIsTrue :
      secondMajorTraceReplaysOverFirstWithoutChangingRuleBodies ≡ true
    joinedTargetContainsBothMajorProofs : Bool
    joinedTargetContainsBothMajorProofsIsTrue :
      joinedTargetContainsBothMajorProofs ≡ true
    generatedScaffoldPersistsToJoinedMajorTarget : Bool
    generatedScaffoldPersistsToJoinedMajorTargetIsTrue :
      generatedScaffoldPersistsToJoinedMajorTarget ≡ true
    replayManufacturesEitherMajorProofWithoutItsOriginalTrace : Bool
    replayManufacturesEitherMajorProofWithoutItsOriginalTraceIsFalse :
      replayManufacturesEitherMajorProofWithoutItsOriginalTrace ≡ false

canonicalWette1969Rule915IndependentMajorTraceJoinBoundary :
  Wette1969Rule915IndependentMajorTraceJoinBoundary
canonicalWette1969Rule915IndependentMajorTraceJoinBoundary =
  wette1969Rule915IndependentMajorTraceJoinBoundary
    true refl true refl true refl true refl false refl
