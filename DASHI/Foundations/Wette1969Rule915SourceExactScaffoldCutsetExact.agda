module DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: SOURCE-EXACT GENERATED SCAFFOLD -> TWO PROOFS
--
--   F1--7         actual historical conclusion producers
--   S10--15       one shared sequence of actual historical conclusions
--   S8,9,16,17    induction-side syntactic producers
--   S19--26       independence-side syntactic producers
--   D18 + D27     the only two substantive proof sockets
--
-- Premise 9 is explicitly included. Freshness slots cannot be satisfied merely
-- by arbitrary membership: the strong producer layer requires a certified
-- historical rule whose conclusion is the requested formula.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969Rule915GeneratedScaffoldExact as Generated
import DASHI.Foundations.Wette1969Rule915FormationProducerExact as Formation
import DASHI.Foundations.Wette1969Rule915Shared1015ProducerExact as Shared
import DASHI.Foundations.Wette1969Rule915InductionScaffoldProducerExact as Induction
import DASHI.Foundations.Wette1969Rule915IndependenceScaffoldProducerExact as Independence
import DASHI.Foundations.Wette1969Rule915SeparatedMajorProofsExact as Major
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Later.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record SourceExactScaffoldInputs
    (initial : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor sourceExactScaffoldInputs
  field
    formation : Formation.FormationProducerChain initial firstSeven later

    shared1015 :
      Shared.Shared1015ProducerChain
        (Formation.formationTarget formation)
        firstSeven later

    inductionScaffold :
      Induction.InductionScaffoldProducerChain
        (Shared.sharedTarget shared1015) later

    independenceScaffold :
      Independence.IndependenceScaffoldProducerChain
        (Induction.inductionScaffoldTarget inductionScaffold) later

open SourceExactScaffoldInputs public

asGeneratedScaffoldChain :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  SourceExactScaffoldInputs initial firstSeven later →
  Generated.Rule915GeneratedScaffoldChain initial firstSeven later
asGeneratedScaffoldChain firstSeven later inputs =
  Generated.rule915GeneratedScaffoldChain
    (Formation.formationTrace (formation inputs))
    (Formation.formationEvidenceAtTarget (formation inputs))
    (Shared.sharedTrace (shared1015 inputs))
    (Shared.sharedEvidenceAtTarget (shared1015 inputs))
    (Induction.inductionScaffoldTrace (inductionScaffold inputs))
    (Induction.inductionScaffoldEvidenceAtTarget (inductionScaffold inputs))
    (Independence.independenceScaffoldTrace (independenceScaffold inputs))
    (Independence.independenceScaffoldEvidenceAtTarget (independenceScaffold inputs))

sourceExactScaffoldTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  SourceExactScaffoldInputs initial firstSeven later → Context
sourceExactScaffoldTarget {firstSeven = firstSeven} {later = later} inputs =
  Generated.generatedScaffoldTarget
    (asGeneratedScaffoldChain firstSeven later inputs)

shared1015AtSourceExactTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  Obligations.Shared1015Evidence
    (sourceExactScaffoldTarget inputs)
    (Later.completeTypedTranscription firstSeven later)
shared1015AtSourceExactTarget {firstSeven = firstSeven} {later = later} inputs =
  Generated.sharedAtTarget (asGeneratedScaffoldChain firstSeven later inputs)

record SourceExactTwoMajorProofs
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (inputs : SourceExactScaffoldInputs initial firstSeven later) : Set where
  constructor sourceExactTwoMajorProofs
  field
    induction :
      Major.PredecessorInductionDischarge
        (sourceExactScaffoldTarget inputs) firstSeven later
        (shared1015AtSourceExactTarget inputs)
    independence :
      Major.DefiniensIndependenceDischarge
        (sourceExactScaffoldTarget inputs) firstSeven later
        (shared1015AtSourceExactTarget inputs)

open SourceExactTwoMajorProofs public

majorDischarges :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  SourceExactTwoMajorProofs firstSeven later inputs →
  Major.SharedMajorDischarges
    (sourceExactScaffoldTarget inputs) firstSeven later
majorDischarges firstSeven later inputs proofs =
  Major.sharedMajorDischarges
    (shared1015AtSourceExactTarget inputs)
    (induction proofs)
    (independence proofs)

selectRule915SourceExactCutset :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (recursivePredicate : WordTerm) →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  SourceExactTwoMajorProofs firstSeven later inputs →
  PCRA.SelectedRuleApplication historicalSystem (sourceExactScaffoldTarget inputs)
selectRule915SourceExactCutset firstSeven later recursivePredicate inputs proofs =
  Generated.selectRule915FromGeneratedScaffoldAndTwoProofs
    firstSeven later recursivePredicate
    (asGeneratedScaffoldChain firstSeven later inputs)
    (Major.asTwoProofEvidence (majorDischarges firstSeven later inputs proofs))

record Wette1969Rule915SourceExactScaffoldCutsetBoundary : Set where
  constructor wette1969Rule915SourceExactScaffoldCutsetBoundary
  field
    premise9CorrectionIsBuiltIntoGeneratedScaffold : Bool
    premise9CorrectionIsBuiltIntoGeneratedScaffoldIsTrue :
      premise9CorrectionIsBuiltIntoGeneratedScaffold ≡ true
    everyNonMajorSlot1To27MustBeActualHistoricalConclusion : Bool
    everyNonMajorSlot1To27MustBeActualHistoricalConclusionIsTrue :
      everyNonMajorSlot1To27MustBeActualHistoricalConclusion ≡ true
    shared1015IsOneObjectConsumedByBothMajorBranches : Bool
    shared1015IsOneObjectConsumedByBothMajorBranchesIsTrue :
      shared1015IsOneObjectConsumedByBothMajorBranches ≡ true
    exactRemainingMajorCutsetIs18And27 : Bool
    exactRemainingMajorCutsetIs18And27IsTrue :
      exactRemainingMajorCutsetIs18And27 ≡ true
    syntacticProductionUniversallyDischarges18Or27 : Bool
    syntacticProductionUniversallyDischarges18Or27IsFalse :
      syntacticProductionUniversallyDischarges18Or27 ≡ false

canonicalWette1969Rule915SourceExactScaffoldCutsetBoundary :
  Wette1969Rule915SourceExactScaffoldCutsetBoundary
canonicalWette1969Rule915SourceExactScaffoldCutsetBoundary =
  wette1969Rule915SourceExactScaffoldCutsetBoundary
    true refl true refl true refl true refl false refl
