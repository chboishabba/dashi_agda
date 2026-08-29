module DASHI.Foundations.Wette1969Rule915MajorDerivationProblemExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: TWO SOURCE-EXACT MAJOR DERIVATION PROBLEMS
--
-- The source-exact syntactic scaffold and the independent-trace join already
-- exist.  The remaining mathematical work is therefore represented literally
-- as two certified historical traces, one for premise 18 and one for premise
-- 27, both starting from the same generated scaffold context.
--
-- The traces are indexed first by recovered pure source words.  Only the
-- recovery equalities are then used to coerce them to the existing typed 9.1.5
-- slots and feed the already-merged independent trace join.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969Rule915MajorPureWordRecoveryFrontierExact as Recovery
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record SourceExactMajorDerivationAttempts
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) : Set₁ where
  constructor sourceExactMajorDerivationAttempts
  field
    pureWordRecovery : Recovery.Rule915MajorPureWordRecovery later

    premise18Attempt :
      Join.CertifiedMajorTrace
        (Source.sourceExactScaffoldTarget scaffold)
        (Recovery.premise18PureFormula later pureWordRecovery)

    premise27Attempt :
      Join.CertifiedMajorTrace
        (Source.sourceExactScaffoldTarget scaffold)
        (Recovery.premise27PureFormula later pureWordRecovery)

open SourceExactMajorDerivationAttempts public

premise18AttemptAtTypedSlot :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempts : SourceExactMajorDerivationAttempts firstSeven later scaffold) →
  Join.CertifiedMajorTrace
    (Source.sourceExactScaffoldTarget scaffold)
    (Later.premise18 later)
premise18AttemptAtTypedSlot {later = later} attempts
  rewrite Recovery.premise18PureFormulaMatchesTypedSlot
    later (pureWordRecovery attempts) =
  premise18Attempt attempts

premise27AttemptAtTypedSlot :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempts : SourceExactMajorDerivationAttempts firstSeven later scaffold) →
  Join.CertifiedMajorTrace
    (Source.sourceExactScaffoldTarget scaffold)
    (Later.premise27 later)
premise27AttemptAtTypedSlot {later = later} attempts
  rewrite Recovery.premise27PureFormulaMatchesTypedSlot
    later (pureWordRecovery attempts) =
  premise27Attempt attempts

asIndependentMajorTraceInputs :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  SourceExactMajorDerivationAttempts firstSeven later scaffold →
  Join.IndependentMajorTraceInputs firstSeven later scaffold
asIndependentMajorTraceInputs attempts =
  Join.independentMajorTraceInputs
    (premise18AttemptAtTypedSlot attempts)
    (premise27AttemptAtTypedSlot attempts)

selectRule915FromRecoveredIndependentMajorAttempts :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (recursivePredicate : WordTerm) →
  (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) →
  (attempts : SourceExactMajorDerivationAttempts firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem
    (Join.joinedMajorTarget (asIndependentMajorTraceInputs attempts))
selectRule915FromRecoveredIndependentMajorAttempts
  firstSeven later recursivePredicate scaffold attempts =
  Join.selectRule915FromIndependentMajorTraces
    firstSeven later recursivePredicate scaffold
    (asIndependentMajorTraceInputs attempts)

record Wette1969Rule915MajorDerivationProblemBoundary : Set where
  constructor wette1969Rule915MajorDerivationProblemBoundary
  field
    premise18And27AreNowSeparateCertifiedTraceProblems : Bool
    premise18And27AreNowSeparateCertifiedTraceProblemsIsTrue :
      premise18And27AreNowSeparateCertifiedTraceProblems ≡ true

    bothProblemsStartFromSameGeneratedSourceExactScaffold : Bool
    bothProblemsStartFromSameGeneratedSourceExactScaffoldIsTrue :
      bothProblemsStartFromSameGeneratedSourceExactScaffold ≡ true

    recoveredPureWordIdentityIsRequiredBeforeJoining : Bool
    recoveredPureWordIdentityIsRequiredBeforeJoiningIsTrue :
      recoveredPureWordIdentityIsRequiredBeforeJoining ≡ true

    solvingBothProblemsFeedsExistingIndependentTraceJoin : Bool
    solvingBothProblemsFeedsExistingIndependentTraceJoinIsTrue :
      solvingBothProblemsFeedsExistingIndependentTraceJoin ≡ true

    thisInterfaceManufacturesEitherMajorDerivation : Bool
    thisInterfaceManufacturesEitherMajorDerivationIsFalse :
      thisInterfaceManufacturesEitherMajorDerivation ≡ false

canonicalWette1969Rule915MajorDerivationProblemBoundary :
  Wette1969Rule915MajorDerivationProblemBoundary
canonicalWette1969Rule915MajorDerivationProblemBoundary =
  wette1969Rule915MajorDerivationProblemBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
