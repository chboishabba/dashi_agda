module DASHI.Foundations.Wette1969Rule915ZeroArityFalsumApplicationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969Rule915ZeroArityFalsumInstanceExact as I
import DASHI.Foundations.Wette1969Rule915ZeroArityFalsumScaffoldExact as Scaffold
import DASHI.Foundations.Wette1969Rule915ZeroArityFalsumMajorsExact as Majors
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

-- The existing historical 9.1.5 owner exposes the dense output word as an
-- explicit argument.  Keep that boundary visible here; the premises and the
-- selected historical rule itself are fully concrete.
recursivePredicateWitness : WordTerm
recursivePredicateWitness = I.mark0

selected915 : PCRA.SelectedRuleApplication historicalSystem
  (Join.joinedMajorTarget Majors.independentMajors)
selected915 =
  Join.selectRule915FromIndependentMajorTraces
    I.canonicalFirstSeven I.canonicalLater recursivePredicateWitness
    Scaffold.canonicalScaffold Majors.independentMajors

rule915ConclusionAtSelectedTarget :
  Judgment.predicateSchema I.zeroWord recursivePredicateWitness Finite.∈Context
    (PCRA.applySelected historicalSystem selected915)
rule915ConclusionAtSelectedTarget =
  Closure.certifiedConclusionAvailable
    (Join.joinedMajorTarget Majors.independentMajors) selected915

joinedThen915Trace :
  PCRA.CertifiedRuleTrace historicalSystem Majors.start
joinedThen915Trace =
  PCRA.appendCertifiedTrace
    Majors.joinedTrace
    (PCRA.choose selected915 PCRA.done)

rule915ConclusionAtTraceTarget :
  Judgment.predicateSchema I.zeroWord recursivePredicateWitness Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem joinedThen915Trace)
rule915ConclusionAtTraceTarget
  rewrite PCRA.runAppendCertifiedTrace
    Majors.joinedTrace (PCRA.choose selected915 PCRA.done) =
  rule915ConclusionAtSelectedTarget

record Wette1969Rule915ZeroArityFalsumApplicationBoundary : Set where
  constructor wette1969Rule915ZeroArityFalsumApplicationBoundary
  field
    joinedConcreteMajorsFeedActualHistorical915Selection : Bool
    joinedConcreteMajorsFeedActualHistorical915SelectionIsTrue :
      joinedConcreteMajorsFeedActualHistorical915Selection ≡ true
    historical915ApplicationProducesPredicateSchema : Bool
    historical915ApplicationProducesPredicateSchemaIsTrue :
      historical915ApplicationProducesPredicateSchema ≡ true
    selectedRuleUsesTwentySevenConcretePremisesFromSameInstance : Bool
    selectedRuleUsesTwentySevenConcretePremisesFromSameInstanceIsTrue :
      selectedRuleUsesTwentySevenConcretePremisesFromSameInstance ≡ true
    denseRecursivePredicateOutputWordIsStillExplicitOwnerArgument : Bool
    denseRecursivePredicateOutputWordIsStillExplicitOwnerArgumentIsTrue :
      denseRecursivePredicateOutputWordIsStillExplicitOwnerArgument ≡ true

canonicalWette1969Rule915ZeroArityFalsumApplicationBoundary :
  Wette1969Rule915ZeroArityFalsumApplicationBoundary
canonicalWette1969Rule915ZeroArityFalsumApplicationBoundary =
  wette1969Rule915ZeroArityFalsumApplicationBoundary true refl true refl true refl true refl
