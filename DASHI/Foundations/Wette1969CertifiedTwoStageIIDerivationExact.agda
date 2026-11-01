module DASHI.Foundations.Wette1969CertifiedTwoStageIIDerivationExact where

------------------------------------------------------------------------
-- CERTIFIED TWO-STAGE II -> RULE 8.2.8 -> PAIRED II
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969CertifiedSubstitutionDerivationExact as DeriveII
import DASHI.Foundations.Wette1969Rule828To9324x25DerivationExact as Weld
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext

historicalSystem :
  PCRA.RuleApplicationSystem Context RuleBody.HistoricalRuleBody
historicalSystem = DeriveII.historicalSystem

record CertifiedTwoStageIIDerivation
    (context : Context)
    (stages : TwoStage.DependentTwoStageSubstitution) : Set₁ where
  constructor certifiedTwoStageIIDerivation
  field
    firstDerivation :
      DeriveII.CertifiedSubstitutionDerivation
        context
        (TwoStage.oldTuple (TwoStage.first stages))
        (TwoStage.source (TwoStage.first stages))
        (TwoStage.newTuple (TwoStage.first stages))
        (TwoStage.intermediate (TwoStage.first stages))

    secondDerivation :
      DeriveII.CertifiedSubstitutionDerivation
        (DeriveII.targetContext firstDerivation)
        (TwoStage.predicateMark (TwoStage.second stages))
        (TwoStage.intermediate (TwoStage.first stages))
        (TwoStage.recursivePredicate (TwoStage.second stages))
        (TwoStage.result (TwoStage.second stages))

open CertifiedTwoStageIIDerivation public

sequentialTarget :
  {context : Context} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  CertifiedTwoStageIIDerivation context stages → Context
sequentialTarget derivation =
  DeriveII.targetContext (secondDerivation derivation)

firstIIAvailableAtSequentialTarget :
  {context : Context} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (derivation : CertifiedTwoStageIIDerivation context stages) →
  TwoStage.firstStageII (TwoStage.first stages)
    Finite.∈Context sequentialTarget derivation
firstIIAvailableAtSequentialTarget {stages = stages} derivation =
  Closure.certifiedTracePreservesPriorFormula
    (DeriveII.trace (secondDerivation derivation))
    (TwoStage.firstStageII (TwoStage.first stages))
    (DeriveII.resultAvailable (firstDerivation derivation))

secondIIAvailableAtSequentialTarget :
  {context : Context} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (derivation : CertifiedTwoStageIIDerivation context stages) →
  TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
    Finite.∈Context sequentialTarget derivation
secondIIAvailableAtSequentialTarget derivation =
  DeriveII.resultAvailable (secondDerivation derivation)

selectRule828AfterCertifiedStages :
  {context : Context} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (derivation : CertifiedTwoStageIIDerivation context stages) →
  PCRA.SelectedRuleApplication historicalSystem (sequentialTarget derivation)
selectRule828AfterCertifiedStages {stages = stages} derivation =
  Weld.selectRule828
    (sequentialTarget derivation)
    stages
    (firstIIAvailableAtSequentialTarget derivation)
    (secondIIAvailableAtSequentialTarget derivation)

pairedTrace :
  {context : Context} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (derivation : CertifiedTwoStageIIDerivation context stages) →
  PCRA.CertifiedRuleTrace historicalSystem context
pairedTrace derivation =
  PCRA.appendCertifiedTrace
    (DeriveII.trace (firstDerivation derivation))
    (PCRA.appendCertifiedTrace
      (DeriveII.trace (secondDerivation derivation))
      (PCRA.choose (selectRule828AfterCertifiedStages derivation) PCRA.done))

pairedIIAvailable :
  {context : Context} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (derivation : CertifiedTwoStageIIDerivation context stages) →
  TwoStage.pairedII stages Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem (pairedTrace derivation))
pairedIIAvailable derivation = Finite.here

record Wette1969CertifiedTwoStageIIBoundary : Set where
  constructor wette1969CertifiedTwoStageIIBoundary
  field
    firstIICanBeGeneratedByHistorical82Derivation : Bool
    firstIICanBeGeneratedByHistorical82DerivationIsTrue :
      firstIICanBeGeneratedByHistorical82Derivation ≡ true
    secondIIStartsAtActualFirstDerivationTarget : Bool
    secondIIStartsAtActualFirstDerivationTargetIsTrue :
      secondIIStartsAtActualFirstDerivationTarget ≡ true
    rule828CanConsumeGeneratedSequentialIIs : Bool
    rule828CanConsumeGeneratedSequentialIIsIsTrue :
      rule828CanConsumeGeneratedSequentialIIs ≡ true
    pairedIINoLongerRequiresInitialContextMembership : Bool
    pairedIINoLongerRequiresInitialContextMembershipIsTrue :
      pairedIINoLongerRequiresInitialContextMembership ≡ true
    generatedIIsAreAlreadySemanticSubstitutionTruth : Bool
    generatedIIsAreAlreadySemanticSubstitutionTruthIsFalse :
      generatedIIsAreAlreadySemanticSubstitutionTruth ≡ false

canonicalWette1969CertifiedTwoStageIIBoundary :
  Wette1969CertifiedTwoStageIIBoundary
canonicalWette1969CertifiedTwoStageIIBoundary =
  wette1969CertifiedTwoStageIIBoundary
    true refl true refl true refl true refl false refl
