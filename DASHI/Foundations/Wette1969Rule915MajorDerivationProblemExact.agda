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
-- CANONICAL CURRENT PROBLEM AND SELECTED SUFFICIENT ROUTES.
--
-- The canonical current problem is still the pair of certified D18/D27 traces
-- from the generated p.145 scaffold.  The existing 9.3.23 construction is a
-- selected sufficient route for D18.  It is not proved complete for D18.
--
-- D27 has a selected sufficient route through its two directional leaves.
------------------------------------------------------------------------

CanonicalRule915CurrentProblem :
  {initial : Context} →
  Source.SourceExactScaffoldInputs
    initial Weld.canonicalFirstSeven Weld.canonicalLater →
  Set₁
CanonicalRule915CurrentProblem scaffold =
  Join.IndependentMajorTraceInputs
    Weld.canonicalFirstSeven Weld.canonicalLater scaffold

record CanonicalRule915SelectedRouteResidual
    {initial : Context}
    (scaffold :
      Source.SourceExactScaffoldInputs
        initial Weld.canonicalFirstSeven Weld.canonicalLater) : Set₁ where
  constructor canonicalRule915SelectedRouteResidual
  field
    selectedPredecessorInductionRoute :
      Resolve18.Rule9323MatchedCoreLeafAttempt
        Weld.canonicalFirstSeven Weld.canonicalLater scaffold

    selectedDefiniensIndependenceRoute :
      Resolve27.CanonicalPremise27DirectionalLeafAttempt scaffold

open CanonicalRule915SelectedRouteResidual public

selectedRouteToCurrentProblem :
  {initial : Context} →
  {scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater} →
  CanonicalRule915SelectedRouteResidual scaffold →
  CanonicalRule915CurrentProblem scaffold
selectedRouteToCurrentProblem residual =
  Join.independentMajorTraceInputs
    (Resolve18.matchedRule9323ClosesPremise18
      (selectedPredecessorInductionRoute residual))
    (Resolve27.closeCanonicalPremise27
      (selectedDefiniensIndependenceRoute residual))

selectCanonicalRule915FromCurrentProblem :
  {initial : Context} →
  (recursivePredicate : WordTerm) →
  (scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater) →
  (problem : CanonicalRule915CurrentProblem scaffold) →
  PCRA.SelectedRuleApplication historicalSystem
    (Join.joinedMajorTarget problem)
selectCanonicalRule915FromCurrentProblem
  recursivePredicate scaffold problem =
  Join.selectRule915FromIndependentMajorTraces
    Weld.canonicalFirstSeven
    Weld.canonicalLater
    recursivePredicate
    scaffold
    problem

selectCanonicalRule915FromSelectedRoute :
  {initial : Context} →
  (recursivePredicate : WordTerm) →
  (scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater) →
  (residual : CanonicalRule915SelectedRouteResidual scaffold) →
  PCRA.SelectedRuleApplication historicalSystem
    (Join.joinedMajorTarget (selectedRouteToCurrentProblem residual))
selectCanonicalRule915FromSelectedRoute
  recursivePredicate scaffold residual =
  selectCanonicalRule915FromCurrentProblem
    recursivePredicate scaffold (selectedRouteToCurrentProblem residual)

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
      CanonicalRule915CurrentProblem scaffold

    scaffoldInvariant :
      Cutset.Rule915SyntacticScaffoldEvidence
        (Join.joinedMajorTarget preconditions)
        Weld.canonicalFirstSeven
        Weld.canonicalLater

    postcondition :
      PCRA.SelectedRuleApplication historicalSystem
        (Join.joinedMajorTarget preconditions)

open CanonicalRule915ResidualContract public

buildCanonicalRule915ResidualContract :
  {initial : Context} →
  (recursivePredicate : WordTerm) →
  (scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater) →
  (problem : CanonicalRule915CurrentProblem scaffold) →
  CanonicalRule915ResidualContract recursivePredicate scaffold
buildCanonicalRule915ResidualContract recursivePredicate scaffold problem =
  canonicalRule915ResidualContract
    problem
    (Join.joinedScaffoldEvidence
      Weld.canonicalFirstSeven
      Weld.canonicalLater
      scaffold
      problem)
    (selectCanonicalRule915FromCurrentProblem
      recursivePredicate scaffold problem)

buildCanonicalRule915SelectedRouteContract :
  {initial : Context} →
  (recursivePredicate : WordTerm) →
  (scaffold :
    Source.SourceExactScaffoldInputs
      initial Weld.canonicalFirstSeven Weld.canonicalLater) →
  (residual : CanonicalRule915SelectedRouteResidual scaffold) →
  CanonicalRule915ResidualContract recursivePredicate scaffold
buildCanonicalRule915SelectedRouteContract
  recursivePredicate scaffold residual =
  buildCanonicalRule915ResidualContract
    recursivePredicate scaffold (selectedRouteToCurrentProblem residual)

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
    "P: search the general D18 trace problem; use matched 9.3.23 only as a selected sufficient route; use the two directional leaves as the selected D27 route"
    "G: select certified historical 9.1.5 at the joined target without semantic promotion"
    "F: return the first missing general D18/D27 trace receipt; selected route, status, documentation, fleet priority, and source labels do not create it"

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

    premise18Selected9323RouteClosesThenTwo939Steps : Bool
    premise18Selected9323RouteClosesThenTwo939StepsIsTrue :
      premise18Selected9323RouteClosesThenTwo939Steps ≡ true

    selected9323RouteIsKnownCompleteForPremise18 : Bool
    selected9323RouteIsKnownCompleteForPremise18IsFalse :
      selected9323RouteIsKnownCompleteForPremise18 ≡ false

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
    false refl
    true refl
    false refl
    false refl
