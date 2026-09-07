module DASHI.Core.TerminalRealisationValidationExact where

------------------------------------------------------------------------
-- TERMINAL REALISATION VALIDATION
--
-- Generic theorem shape shared by economic terminal-payer validation and
-- realised-remedy / material-justice validation.
--
-- Surrounding positive signals may be relevant evidence, but they do not
-- manufacture the terminal criterion required by a declared consumer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SurroundingSignals : Set₁ where
  constructor surrounding-signals
  field
    Demand Growth Utilisation Scarcity InvestmentGains PolicySupport : Set
    demand : Demand
    growth : Growth
    utilisation : Utilisation
    scarcity : Scarcity
    investmentGains : InvestmentGains
    policySupport : PolicySupport

open SurroundingSignals public

record InstitutionalRepairSignals : Set₁ where
  constructor institutional-repair-signals
  field
    Apology Consultation Funding Recognition Monitoring PolicyCommitment : Set
    apology : Apology
    consultation : Consultation
    funding : Funding
    recognition : Recognition
    monitoring : Monitoring
    policyCommitment : PolicyCommitment

open InstitutionalRepairSignals public

record TerminalCriterion : Set₁ where
  constructor terminal-criterion
  field
    Criterion : Set
    criterion : Criterion
    consumerReference : String

open TerminalCriterion public

data SurroundingSignalsManufactureTerminalCriterion : Set where
data InstitutionalSignalsManufactureMaterialRepair : Set where

surroundingSignalsDoNotManufactureTerminalCriterion :
  SurroundingSignalsManufactureTerminalCriterion → ⊥
surroundingSignalsDoNotManufactureTerminalCriterion ()

institutionalSignalsDoNotManufactureMaterialRepair :
  InstitutionalSignalsManufactureMaterialRepair → ⊥
institutionalSignalsDoNotManufactureMaterialRepair ()

record TerminalRealisationBoundary : Set where
  constructor terminal-realisation-boundary
  field
    surroundingSignalsMaySupportAssessment : Bool
    surroundingSignalsMaySupportAssessmentIsTrue :
      surroundingSignalsMaySupportAssessment ≡ true
    surroundingSignalsAreTerminalValidationByDefault : Bool
    surroundingSignalsAreTerminalValidationByDefaultIsFalse :
      surroundingSignalsAreTerminalValidationByDefault ≡ false
    declarationEqualsRealisation : Bool
    declarationEqualsRealisationIsFalse : declarationEqualsRealisation ≡ false
    fundingEqualsRealisation : Bool
    fundingEqualsRealisationIsFalse : fundingEqualsRealisation ≡ false
    consultationEqualsRealisation : Bool
    consultationEqualsRealisationIsFalse : consultationEqualsRealisation ≡ false
    recognitionEqualsRealisation : Bool
    recognitionEqualsRealisationIsFalse : recognitionEqualsRealisation ≡ false
    terminalCriterionMustBeConsumerIndexed : Bool
    terminalCriterionMustBeConsumerIndexedIsTrue :
      terminalCriterionMustBeConsumerIndexed ≡ true

open TerminalRealisationBoundary public

canonicalTerminalRealisationBoundary : TerminalRealisationBoundary
canonicalTerminalRealisationBoundary = terminal-realisation-boundary
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
