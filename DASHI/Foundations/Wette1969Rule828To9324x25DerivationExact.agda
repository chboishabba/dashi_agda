module DASHI.Foundations.Wette1969Rule828To9324x25DerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 8.2.8 -> 9.3.24/25 PROOF-CARRYING DERIVATION WELD
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Source geometry:
--   * 8.2.8 composes two sequential II judgements into the paired four-place II;
--   * 9.3.24/25 premise 4 consumes that paired ordered-substitution judgement;
--   * section 1.632 fixes the order: V2 -> V3 first, then W2 -> recursive
--     predicate on the actual intermediate result.
--
-- This module closes the proof-carrying gap.  If the two sequential II premises
-- are already derivable in a finite context, rule 8.2.8 is certified there.  Its
-- paired-II conclusion is then genuinely present in the reached context and is
-- used directly as premise 4 of 9.3.24 or 9.3.25, while the other three critical
-- premises are transported monotonically from the source context.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero; suc)

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as CriticalRule
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

------------------------------------------------------------------------
-- Instantiate 9.3.24/25 premise 4 from the exact paired-II output of 8.2.8.
------------------------------------------------------------------------

criticalPremiseParametersFromStages :
  WordTerm →
  WordTerm →
  TwoStage.DependentTwoStageSubstitution →
  CriticalRule.Rule9324x25PremiseParameters
criticalPremiseParametersFromStages arity freshnessContext stages =
  CriticalRule.rule9324x25PremiseParameters
    arity
    (TwoStage.recursivePredicate (TwoStage.second stages))
    (TwoStage.newTuple (TwoStage.first stages))
    freshnessContext
    (TwoStage.pairedSubstituend stages)
    (TwoStage.source (TwoStage.first stages))
    (TwoStage.pairedReplacement stages)
    (TwoStage.result (TwoStage.second stages))

criticalPremise4IsRule828PairedII :
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  CriticalRule.premiseAt
    (criticalPremiseParametersFromStages arity freshnessContext stages)
    Critical.orderedSubstitutionCondition
  ≡ TwoStage.pairedII stages
criticalPremise4IsRule828PairedII arity freshnessContext stages = refl

------------------------------------------------------------------------
-- Rule 8.2.8 becomes an actual proof-carrying transition from two available
-- sequential II premises.
------------------------------------------------------------------------

rule828PremisesHold :
  (context : Context) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context context →
  TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
    Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    context
    (TwoStage.rule8-2-8 stages)
rule828PremisesHold context stages firstEvidence secondEvidence zero =
  firstEvidence
rule828PremisesHold context stages firstEvidence secondEvidence (suc zero) =
  secondEvidence

selectRule828 :
  (context : Context) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context context →
  TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
    Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule828 context stages firstEvidence secondEvidence =
  PCRA.selectedRuleApplication
    (TwoStage.rule8-2-8 stages)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem
      context
      (TwoStage.rule8-2-8 stages)
      (rule828PremisesHold context stages firstEvidence secondEvidence))

contextAfter828 :
  Context →
  TwoStage.DependentTwoStageSubstitution →
  Context
contextAfter828 context stages = TwoStage.pairedII stages ∷ context

applyRule828AddsPairedII :
  (context : Context) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (firstEvidence :
    TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context context) →
  (secondEvidence :
    TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
      Finite.∈Context context) →
  PCRA.applySelected
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    (selectRule828 context stages firstEvidence secondEvidence)
  ≡ contextAfter828 context stages
applyRule828AddsPairedII context stages firstEvidence secondEvidence = refl

pairedIIAvailableAfter828 :
  (context : Context) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  TwoStage.pairedII stages Finite.∈Context (contextAfter828 context stages)
pairedIIAvailableAfter828 context stages = Finite.here

------------------------------------------------------------------------
-- Carry the other three 9.3.24/25 premises from the source context. Premise 4
-- is not externally supplied: it is generated by certified 8.2.8.
------------------------------------------------------------------------

record FirstThreeCriticalPremises
    (context : Context)
    (parameters : CriticalRule.Rule9324x25PremiseParameters) : Set where
  constructor firstThreeCriticalPremises
  field
    predicateFormation :
      CriticalRule.premiseAt parameters Critical.recursivePredicateFormation
        Finite.∈Context context
    freshVariableTupleFormation :
      CriticalRule.premiseAt parameters Critical.freshVariableTupleFormation
        Finite.∈Context context
    variableFreshness :
      CriticalRule.premiseAt parameters Critical.variableFreshnessCondition
        Finite.∈Context context

open FirstThreeCriticalPremises public

premises9324HoldAfter828 :
  (context : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  FirstThreeCriticalPremises
    context
    (criticalPremiseParametersFromStages arity freshnessContext stages) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    (contextAfter828 context stages)
    (CriticalRule.rule9-3-24
      (criticalPremiseParametersFromStages arity freshnessContext stages)
      conclusions)
premises9324HoldAfter828
  context arity freshnessContext stages conclusions evidence zero =
  Finite.there (predicateFormation evidence)
premises9324HoldAfter828
  context arity freshnessContext stages conclusions evidence (suc zero) =
  Finite.there (freshVariableTupleFormation evidence)
premises9324HoldAfter828
  context arity freshnessContext stages conclusions evidence (suc (suc zero)) =
  Finite.there (variableFreshness evidence)
premises9324HoldAfter828
  context arity freshnessContext stages conclusions evidence
  (suc (suc (suc zero))) = Finite.here

premises9325HoldAfter828 :
  (context : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  FirstThreeCriticalPremises
    context
    (criticalPremiseParametersFromStages arity freshnessContext stages) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    (contextAfter828 context stages)
    (CriticalRule.rule9-3-25
      (criticalPremiseParametersFromStages arity freshnessContext stages)
      conclusions)
premises9325HoldAfter828
  context arity freshnessContext stages conclusions evidence zero =
  Finite.there (predicateFormation evidence)
premises9325HoldAfter828
  context arity freshnessContext stages conclusions evidence (suc zero) =
  Finite.there (freshVariableTupleFormation evidence)
premises9325HoldAfter828
  context arity freshnessContext stages conclusions evidence (suc (suc zero)) =
  Finite.there (variableFreshness evidence)
premises9325HoldAfter828
  context arity freshnessContext stages conclusions evidence
  (suc (suc (suc zero))) = Finite.here

------------------------------------------------------------------------
-- Direct selectors: a derived 8.2.8 conclusion supplies premise 4 to the next
-- historical rule application.
------------------------------------------------------------------------

selectRule9324After828 :
  (context : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  FirstThreeCriticalPremises
    context
    (criticalPremiseParametersFromStages arity freshnessContext stages) →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    (contextAfter828 context stages)
selectRule9324After828 context arity freshnessContext stages conclusions evidence =
  Historical.selectRule9324
    Finite.finiteHistoricalContextSystem
    (contextAfter828 context stages)
    (criticalPremiseParametersFromStages arity freshnessContext stages)
    conclusions
    (premises9324HoldAfter828
      context arity freshnessContext stages conclusions evidence)

selectRule9325After828 :
  (context : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  FirstThreeCriticalPremises
    context
    (criticalPremiseParametersFromStages arity freshnessContext stages) →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    (contextAfter828 context stages)
selectRule9325After828 context arity freshnessContext stages conclusions evidence =
  Historical.selectRule9325
    Finite.finiteHistoricalContextSystem
    (contextAfter828 context stages)
    (criticalPremiseParametersFromStages arity freshnessContext stages)
    conclusions
    (premises9325HoldAfter828
      context arity freshnessContext stages conclusions evidence)

------------------------------------------------------------------------
-- Two-step certified traces. These are the first direct historical deduction
-- paths in this reconstruction where an earlier recovered substitution rule
-- manufactures a later critical-rule premise rather than merely carrying it as
-- external evidence.
------------------------------------------------------------------------

trace828Then9324 :
  (context : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  (firstEvidence :
    TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context context) →
  (secondEvidence :
    TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
      Finite.∈Context context) →
  (criticalEvidence :
    FirstThreeCriticalPremises
      context
      (criticalPremiseParametersFromStages arity freshnessContext stages)) →
  PCRA.CertifiedRuleTrace
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
trace828Then9324
  context arity freshnessContext stages conclusions
  firstEvidence secondEvidence criticalEvidence =
  PCRA.choose
    (selectRule828 context stages firstEvidence secondEvidence)
    (PCRA.choose
      (selectRule9324After828
        context arity freshnessContext stages conclusions criticalEvidence)
      PCRA.done)

trace828Then9325 :
  (context : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  (firstEvidence :
    TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context context) →
  (secondEvidence :
    TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
      Finite.∈Context context) →
  (criticalEvidence :
    FirstThreeCriticalPremises
      context
      (criticalPremiseParametersFromStages arity freshnessContext stages)) →
  PCRA.CertifiedRuleTrace
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
trace828Then9325
  context arity freshnessContext stages conclusions
  firstEvidence secondEvidence criticalEvidence =
  PCRA.choose
    (selectRule828 context stages firstEvidence secondEvidence)
    (PCRA.choose
      (selectRule9325After828
        context arity freshnessContext stages conclusions criticalEvidence)
      PCRA.done)

record Wette1969Rule828To9324x25Boundary : Set where
  constructor wette1969Rule828To9324x25Boundary
  field
    rule828ConclusionDefinitionallyMatchesCriticalPremise4 : Bool
    rule828ConclusionDefinitionallyMatchesCriticalPremise4IsTrue :
      rule828ConclusionDefinitionallyMatchesCriticalPremise4 ≡ true

    pairedIIPremiseGeneratedInsideDerivationContext : Bool
    pairedIIPremiseGeneratedInsideDerivationContextIsTrue :
      pairedIIPremiseGeneratedInsideDerivationContext ≡ true

    firstThreeCriticalPremisesPersistAcrossRule828 : Bool
    firstThreeCriticalPremisesPersistAcrossRule828IsTrue :
      firstThreeCriticalPremisesPersistAcrossRule828 ≡ true

    certified828Then9324And9325TracesNowConstructible : Bool
    certified828Then9324And9325TracesNowConstructibleIsTrue :
      certified828Then9324And9325TracesNowConstructible ≡ true

    criticalPremise4StillMustBeSuppliedExternallyAfterRule828 : Bool
    criticalPremise4StillMustBeSuppliedExternallyAfterRule828IsFalse :
      criticalPremise4StillMustBeSuppliedExternallyAfterRule828 ≡ false

    generatedHistoricalPremiseIsAlreadySemanticTruth : Bool
    generatedHistoricalPremiseIsAlreadySemanticTruthIsFalse :
      generatedHistoricalPremiseIsAlreadySemanticTruth ≡ false

canonicalWette1969Rule828To9324x25Boundary :
  Wette1969Rule828To9324x25Boundary
canonicalWette1969Rule828To9324x25Boundary =
  wette1969Rule828To9324x25Boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
