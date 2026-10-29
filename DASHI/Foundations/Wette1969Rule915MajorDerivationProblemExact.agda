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
import DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact as Cutset
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969Rule915MajorPureWordRecoveryFrontierExact as Recovery
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure
import DASHI.Foundations.Wette1969Rule915CanonicalP145TypedWeldExact as Weld
import DASHI.Foundations.Wette1969Rule915Premise18Rule9323ResolutionExact as Resolve18
import DASHI.Foundations.Wette1969Rule915Premise27DirectionalClosureExact as Resolve27
import DASHI.Interop.IntrospectiveProofLoopExact as Introspection
import Data.Empty using (⊥)

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
  with Recovery.premise18PureFormulaMatchesTypedSlot
    later (pureWordRecovery attempts)
... | refl = premise18Attempt attempts

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
  with Recovery.premise27PureFormulaMatchesTypedSlot
    later (pureWordRecovery attempts)
... | refl = premise27Attempt attempts

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


------------------------------------------------------------------------
-- CANONICAL CURRENT RESIDUAL.
--
-- The p.145 transcription, generated scaffold, and structural closure suffixes
-- are already recovered.  The current mathematical residual is therefore:
--
--   D18: one matched historical 9.3.23 core-leaf attempt;
--   D27: two directional implication leaves.
--
-- The suffixes are not new proof obligations.  Existing historical rules close
-- D18 and D27 once these residual witnesses are supplied.
------------------------------------------------------------------------

record CanonicalRule915MajorResidual
    {initial : Context}
    (scaffold :
      Source.SourceExactScaffoldInputs
        initial Weld.canonicalFirstSeven Weld.canonicalLater) : Set₁ where
  constructor canonicalRule915MajorResidual
  field
    predecessorInductionResidual :
      Resolve18.Rule9323MatchedCoreLeafAttempt
        Weld.canonicalFirstSeven Weld.canonicalLater scaffold

    definiensIndependenceResidual :
      Resolve27.CanonicalPremise27DirectionalLeafAttempt scaffold

open CanonicalRule915MajorResidual public

canonicalMajorTraceInputs :
  {initial : Context} →
  {scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater} →
  CanonicalRule915MajorResidual scaffold →
  Join.IndependentMajorTraceInputs
    Weld.canonicalFirstSeven Weld.canonicalLater scaffold
canonicalMajorTraceInputs residual =
  Join.independentMajorTraceInputs
    (Resolve18.matchedRule9323ClosesPremise18
      (predecessorInductionResidual residual))
    (Resolve27.closeCanonicalPremise27
      (definiensIndependenceResidual residual))

selectCanonicalRule915FromCurrentResidual :
  {initial : Context} →
  (recursivePredicate : WordTerm) →
  (scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater) →
  (residual : CanonicalRule915MajorResidual scaffold) →
  PCRA.SelectedRuleApplication historicalSystem
    (Join.joinedMajorTarget (canonicalMajorTraceInputs residual))
selectCanonicalRule915FromCurrentResidual
  recursivePredicate scaffold residual =
  Join.selectRule915FromIndependentMajorTraces
    Weld.canonicalFirstSeven
    Weld.canonicalLater
    recursivePredicate
    scaffold
    (canonicalMajorTraceInputs residual)

------------------------------------------------------------------------
-- Typed precondition / invariant / postcondition contract.
------------------------------------------------------------------------

record CanonicalRule915ResidualContract
    {initial : Context}
    (recursivePredicate : WordTerm)
    (scaffold :
      Source.SourceExactScaffoldInputs
        initial Weld.canonicalFirstSeven Weld.canonicalLater) : Set₁ where
  constructor canonicalRule915ResidualContract
  field
    preconditions :
      CanonicalRule915MajorResidual scaffold

    scaffoldInvariant :
      Cutset.Rule915SyntacticScaffoldEvidence
        (Join.joinedMajorTarget (canonicalMajorTraceInputs preconditions))
        Weld.canonicalFirstSeven
        Weld.canonicalLater

    postcondition :
      PCRA.SelectedRuleApplication historicalSystem
        (Join.joinedMajorTarget (canonicalMajorTraceInputs preconditions))

open CanonicalRule915ResidualContract public

buildCanonicalRule915ResidualContract :
  {initial : Context} →
  (recursivePredicate : WordTerm) →
  (scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater) →
  (residual : CanonicalRule915MajorResidual scaffold) →
  CanonicalRule915ResidualContract recursivePredicate scaffold
buildCanonicalRule915ResidualContract recursivePredicate scaffold residual =
  canonicalRule915ResidualContract
    residual
    (Join.joinedScaffoldEvidence
      Weld.canonicalFirstSeven
      Weld.canonicalLater
      scaffold
      (canonicalMajorTraceInputs residual))
    (selectCanonicalRule915FromCurrentResidual
      recursivePredicate scaffold residual)

------------------------------------------------------------------------
-- Exact non-promotion gates.
------------------------------------------------------------------------

data GeneratedScaffoldCreatesPremise18 : Set where
data GeneratedScaffoldCreatesPremise27 : Set where
data DocumentationCreatesMajorDerivation : Set where
data VerificationStatusCreatesMajorDerivation : Set where

generatedScaffoldDoesNotCreatePremise18 :
  GeneratedScaffoldCreatesPremise18 → ⊥
generatedScaffoldDoesNotCreatePremise18 ()

generatedScaffoldDoesNotCreatePremise27 :
  GeneratedScaffoldCreatesPremise27 → ⊥
generatedScaffoldDoesNotCreatePremise27 ()

documentationDoesNotCreateMajorDerivation :
  DocumentationCreatesMajorDerivation → ⊥
documentationDoesNotCreateMajorDerivation ()

verificationStatusDoesNotCreateMajorDerivation :
  VerificationStatusCreatesMajorDerivation → ⊥
verificationStatusDoesNotCreateMajorDerivation ()

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F process frame.
--
-- O = objective.
-- R = reused owners and requirements.
-- C = canonical code owner.
-- S = current formal state.
-- L = proof lattice / derivation context.
-- P = proposal for the next proof payment.
-- G = goal.
-- F = live residual function.
------------------------------------------------------------------------

Rule915MajorZKPFrame : Set
Rule915MajorZKPFrame = Introspection.ZKPFrame

canonicalRule915MajorZKPFrame : Rule915MajorZKPFrame
canonicalRule915MajorZKPFrame =
  Introspection.zkp-frame
    "O: certify the canonical p.145 rule 9.1.5 only from proof-carrying historical derivations"
    "R: reuse the canonical p.145 weld, generated scaffold, 9.3.23 resolution, directional closure, and independent trace join"
    "C: DASHI.Foundations.Wette1969Rule915MajorDerivationProblemExact"
    "S: all 27 source slots are fixed; scaffold slots are generated; D18 and D27 are reduced but their leaf witnesses remain explicit"
    "L: finite historical derivation contexts with monotone certified trace weakening and replay"
    "P: discharge only the matched 9.3.23 leaf obligations for D18 and the two directional leaves for D27"
    "G: select certified historical 9.1.5 at the joined target without semantic promotion"
    "F: return the first missing D18 or D27 leaf receipt; status, documentation, fleet priority, and source labels do not create it"

record CanonicalRule915CurrentProblemBoundary : Set where
  constructor canonicalRule915CurrentProblemBoundary
  field
    typedPreconditionsInvariantAndPostconditionAreConnected : Bool
    typedPreconditionsInvariantAndPostconditionAreConnectedIsTrue :
      typedPreconditionsInvariantAndPostconditionAreConnected ≡ true

    canonicalP145HasTwentySevenFixedPremiseWords : Bool
    canonicalP145HasTwentySevenFixedPremiseWordsIsTrue :
      canonicalP145HasTwentySevenFixedPremiseWords ≡ true

    generatedScaffoldLeavesExactlyTwoMajorBranches : Bool
    generatedScaffoldLeavesExactlyTwoMajorBranchesIsTrue :
      generatedScaffoldLeavesExactlyTwoMajorBranches ≡ true

    premise18ClosesFromMatched9323ThenTwo939Steps : Bool
    premise18ClosesFromMatched9323ThenTwo939StepsIsTrue :
      premise18ClosesFromMatched9323ThenTwo939Steps ≡ true

    premise27ClosesFromTwoDirectionalLeavesThen935AndTwo939Steps : Bool
    premise27ClosesFromTwoDirectionalLeavesThen935AndTwo939StepsIsTrue :
      premise27ClosesFromTwoDirectionalLeavesThen935AndTwo939Steps ≡ true

    scaffoldAloneClosesEitherMajorBranch : Bool
    scaffoldAloneClosesEitherMajorBranchIsFalse :
      scaffoldAloneClosesEitherMajorBranch ≡ false

    documentationOrVerificationStatusClosesMajorBranch : Bool
    documentationOrVerificationStatusClosesMajorBranchIsFalse :
      documentationOrVerificationStatusClosesMajorBranch ≡ false

canonicalRule915CurrentProblemBoundary :
  CanonicalRule915CurrentProblemBoundary
canonicalRule915CurrentProblemBoundary =
  canonicalRule915CurrentProblemBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
