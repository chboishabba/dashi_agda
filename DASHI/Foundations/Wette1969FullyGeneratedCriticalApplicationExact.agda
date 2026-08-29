module DASHI.Foundations.Wette1969FullyGeneratedCriticalApplicationExact where

------------------------------------------------------------------------
-- FULLY GENERATED LOCAL 9.3.24/25 APPLICATION PATH
--
-- At this layer none of the four critical premises needs to be an initial
-- context membership fact:
--
--   premise 1 is the conclusion of a certified predicate producer trace;
--   premise 2 is the conclusion of a certified distinct-tuple producer trace;
--   premise 3 is the conclusion of a certified freshness producer trace;
--   premise 4 is produced by two certified sequential II derivations followed
--             by historical rule 8.2.8.
--
-- All four are transported to the same actual reached state and consumed by
-- 9.3.24 or 9.3.25.  This is a local derivational closure result, not semantic
-- soundness and not yet a proof that all producer side conditions are derivable
-- from the empty context.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero; suc)

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as CriticalRule
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969CertifiedTwoStageIIDerivationExact as CertifiedTwoStage
import DASHI.Foundations.Wette1969Rule828To9324x25DerivationExact as Weld
import DASHI.Foundations.Wette1969CriticalPremiseLocalDerivationExact as Local
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

historicalSystem :
  PCRA.RuleApplicationSystem Context RuleBody.HistoricalRuleBody
historicalSystem = Local.historicalSystem

criticalParameters :
  WordTerm → WordTerm → TwoStage.DependentTwoStageSubstitution →
  CriticalRule.Rule9324x25PremiseParameters
criticalParameters = Weld.criticalPremiseParametersFromStages

record FullyGeneratedCriticalPremises
    (initial : Context)
    (arity freshnessContext : WordTerm)
    (stages : TwoStage.DependentTwoStageSubstitution) : Set₁ where
  constructor fullyGeneratedCriticalPremises
  field
    firstThree :
      Local.FirstThreeCriticalProducerChain
        initial
        (criticalParameters arity freshnessContext stages)

    sequentialII :
      CertifiedTwoStage.CertifiedTwoStageIIDerivation
        (Local.producerTarget firstThree)
        stages

open FullyGeneratedCriticalPremises public

criticalContext :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  FullyGeneratedCriticalPremises initial arity freshnessContext stages →
  Context
criticalContext generated =
  PCRA.runCertifiedTrace
    historicalSystem
    (CertifiedTwoStage.pairedTrace (sequentialII generated))

predicateAvailableAtCriticalContext :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  CriticalRule.premiseAt
    (criticalParameters arity freshnessContext stages)
    Critical.recursivePredicateFormation
    Finite.∈Context criticalContext generated
predicateAvailableAtCriticalContext
  {arity = arity} {freshnessContext} {stages} generated =
  Closure.certifiedTracePreservesPriorFormula
    (CertifiedTwoStage.pairedTrace (sequentialII generated))
    (CriticalRule.premiseAt
      (criticalParameters arity freshnessContext stages)
      Critical.recursivePredicateFormation)
    (Local.predicateAvailableAtProducerTarget (firstThree generated))

freshTupleAvailableAtCriticalContext :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  CriticalRule.premiseAt
    (criticalParameters arity freshnessContext stages)
    Critical.freshVariableTupleFormation
    Finite.∈Context criticalContext generated
freshTupleAvailableAtCriticalContext
  {arity = arity} {freshnessContext} {stages} generated =
  Closure.certifiedTracePreservesPriorFormula
    (CertifiedTwoStage.pairedTrace (sequentialII generated))
    (CriticalRule.premiseAt
      (criticalParameters arity freshnessContext stages)
      Critical.freshVariableTupleFormation)
    (Local.freshTupleAvailableAtProducerTarget (firstThree generated))

freshnessAvailableAtCriticalContext :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  CriticalRule.premiseAt
    (criticalParameters arity freshnessContext stages)
    Critical.variableFreshnessCondition
    Finite.∈Context criticalContext generated
freshnessAvailableAtCriticalContext
  {arity = arity} {freshnessContext} {stages} generated =
  Closure.certifiedTracePreservesPriorFormula
    (CertifiedTwoStage.pairedTrace (sequentialII generated))
    (CriticalRule.premiseAt
      (criticalParameters arity freshnessContext stages)
      Critical.variableFreshnessCondition)
    (Local.freshnessAvailableAtProducerTarget (firstThree generated))

pairedIIAvailableAtCriticalContext :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  CriticalRule.premiseAt
    (criticalParameters arity freshnessContext stages)
    Critical.orderedSubstitutionCondition
    Finite.∈Context criticalContext generated
pairedIIAvailableAtCriticalContext
  {arity = arity} {freshnessContext} {stages} generated =
  CertifiedTwoStage.pairedIIAvailable (sequentialII generated)

premises9324FullyGenerated :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    (criticalContext generated)
    (CriticalRule.rule9-3-24
      (criticalParameters arity freshnessContext stages)
      conclusions)
premises9324FullyGenerated generated conclusions zero =
  predicateAvailableAtCriticalContext generated
premises9324FullyGenerated generated conclusions (suc zero) =
  freshTupleAvailableAtCriticalContext generated
premises9324FullyGenerated generated conclusions (suc (suc zero)) =
  freshnessAvailableAtCriticalContext generated
premises9324FullyGenerated generated conclusions (suc (suc (suc zero))) =
  pairedIIAvailableAtCriticalContext generated

premises9325FullyGenerated :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    (criticalContext generated)
    (CriticalRule.rule9-3-25
      (criticalParameters arity freshnessContext stages)
      conclusions)
premises9325FullyGenerated generated conclusions zero =
  predicateAvailableAtCriticalContext generated
premises9325FullyGenerated generated conclusions (suc zero) =
  freshTupleAvailableAtCriticalContext generated
premises9325FullyGenerated generated conclusions (suc (suc zero)) =
  freshnessAvailableAtCriticalContext generated
premises9325FullyGenerated generated conclusions (suc (suc (suc zero))) =
  pairedIIAvailableAtCriticalContext generated

select9324FromFullyGeneratedPremises :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  PCRA.SelectedRuleApplication historicalSystem (criticalContext generated)
select9324FromFullyGeneratedPremises
  {arity = arity} {freshnessContext} {stages} generated conclusions =
  Historical.selectRule9324
    Finite.finiteHistoricalContextSystem
    (criticalContext generated)
    (criticalParameters arity freshnessContext stages)
    conclusions
    (premises9324FullyGenerated generated conclusions)

select9325FromFullyGeneratedPremises :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  PCRA.SelectedRuleApplication historicalSystem (criticalContext generated)
select9325FromFullyGeneratedPremises
  {arity = arity} {freshnessContext} {stages} generated conclusions =
  Historical.selectRule9325
    Finite.finiteHistoricalContextSystem
    (criticalContext generated)
    (criticalParameters arity freshnessContext stages)
    conclusions
    (premises9325FullyGenerated generated conclusions)

fullyGeneratedTrace9324 :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  PCRA.CertifiedRuleTrace historicalSystem initial
fullyGeneratedTrace9324 generated conclusions =
  PCRA.appendCertifiedTrace
    (Local.predicateTrace (firstThree generated))
    (PCRA.appendCertifiedTrace
      (Local.tupleTrace (firstThree generated))
      (PCRA.appendCertifiedTrace
        (Local.freshnessTrace (firstThree generated))
        (PCRA.appendCertifiedTrace
          (CertifiedTwoStage.pairedTrace (sequentialII generated))
          (PCRA.choose
            (select9324FromFullyGeneratedPremises generated conclusions)
            PCRA.done))))

fullyGeneratedTrace9325 :
  {initial : Context} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (generated : FullyGeneratedCriticalPremises initial arity freshnessContext stages) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  PCRA.CertifiedRuleTrace historicalSystem initial
fullyGeneratedTrace9325 generated conclusions =
  PCRA.appendCertifiedTrace
    (Local.predicateTrace (firstThree generated))
    (PCRA.appendCertifiedTrace
      (Local.tupleTrace (firstThree generated))
      (PCRA.appendCertifiedTrace
        (Local.freshnessTrace (firstThree generated))
        (PCRA.appendCertifiedTrace
          (CertifiedTwoStage.pairedTrace (sequentialII generated))
          (PCRA.choose
            (select9325FromFullyGeneratedPremises generated conclusions)
            PCRA.done))))

record Wette1969FullyGeneratedCriticalBoundary : Set where
  constructor wette1969FullyGeneratedCriticalBoundary
  field
    allFourCriticalPremisesCanBeGeneratedByCertifiedLocalTraces : Bool
    allFourCriticalPremisesCanBeGeneratedByCertifiedLocalTracesIsTrue :
      allFourCriticalPremisesCanBeGeneratedByCertifiedLocalTraces ≡ true
    sequentialIIPremisesNoLongerNeedInitialMembership : Bool
    sequentialIIPremisesNoLongerNeedInitialMembershipIsTrue :
      sequentialIIPremisesNoLongerNeedInitialMembership ≡ true
    rules9324And9325CanConsumeFullyGeneratedPremiseContexts : Bool
    rules9324And9325CanConsumeFullyGeneratedPremiseContextsIsTrue :
      rules9324And9325CanConsumeFullyGeneratedPremiseContexts ≡ true
    fullyGeneratedLocalTraceStartsFromEmptyContextWithoutAnySideConditions : Bool
    fullyGeneratedLocalTraceStartsFromEmptyContextWithoutAnySideConditionsIsFalse :
      fullyGeneratedLocalTraceStartsFromEmptyContextWithoutAnySideConditions ≡ false
    localDerivationalClosureIsAlreadyArithmeticSoundness : Bool
    localDerivationalClosureIsAlreadyArithmeticSoundnessIsFalse :
      localDerivationalClosureIsAlreadyArithmeticSoundness ≡ false

canonicalWette1969FullyGeneratedCriticalBoundary :
  Wette1969FullyGeneratedCriticalBoundary
canonicalWette1969FullyGeneratedCriticalBoundary =
  wette1969FullyGeneratedCriticalBoundary
    true refl true refl true refl false refl false refl
