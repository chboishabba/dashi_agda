module DASHI.Reasoning.JusticeLeeSensibLawPNFWrongTypeBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.SensibLawResidualLattice as SL
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as Wrong
import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Lee
import DASHI.Reasoning.JusticeLeeSensibLawBidiSearchClosureExact as Search
import DASHI.Reasoning.JusticeLeeSensibLawPNFWrongTypeBridgeExact as Bridge

sampleAtom : SL.PredicatePNF
sampleAtom =
  SL.predicatePNF
    "discriminate"
    SL.sig-agent-theme
    (SL.opaqueArg "institution")
    (SL.opaqueArg "claimant")
    SL.absent
    SL.positive
    SL.attributedEvidence
    "source:sample#span=1:20"

sampleEmission : SL.PNFEmissionReceipt
sampleEmission =
  SL.pnfEmissionReceipt
    "parser:v1"
    "reducer:v1"
    "source:sample#span=1:20"
    sampleAtom

sampleContext : Bridge.ConsumerPNFContext
sampleContext =
  Bridge.consumer-pnf-context
    sampleEmission
    "consumer:legal-elements"
    "query:does-this-pay-the-element"
    "context:sample"

sampleDiagnosis : Bridge.PNFConsumerWrongTypeDiagnosis
sampleDiagnosis =
  Bridge.pnf-consumer-wrongtype-diagnosis
    sampleContext
    Wrong.nonFactorableRepresentation
    "diagnosis:nonfactorable"

applicantProjection : Bridge.LegalFibreProjection
applicantProjection =
  Bridge.legal-fibre-projection
    sampleContext
    Lee.applicant
    Lee.legalProposition
    Lee.alleged
    Lee.sourceText
    "time:sample"
    "relation:claim"
    "projection:applicant"

respondentProjection : Bridge.LegalFibreProjection
respondentProjection =
  Bridge.legal-fibre-projection
    sampleContext
    Lee.respondent
    Lee.legalProposition
    Lee.disputed
    Lee.sourceText
    "time:sample"
    "relation:response"
    "projection:respondent"

sampleBinding : Bridge.WrongTypeResidualBinding sampleDiagnosis
sampleBinding =
  Bridge.wrongtype-residual-binding
    applicantProjection
    respondentProjection
    refl
    refl
    refl
    refl
    Lee.characterisationDisagreement
    SL.partial
    "what characterisation is supported for this consumer?"
    "binding:explicit-not-automatic"

regression-compiles-explicit-residual :
  Lee.kind (Bridge.compileControversyResidual sampleBinding)
  ≡ Lee.characterisationDisagreement
regression-compiles-explicit-residual = refl

regression-reverse-search-uses-bound-kind :
  Search.residualKind
    (Bridge.compileSearchObligation Search.prepareForAdjudication sampleBinding)
  ≡ Lee.characterisationDisagreement
regression-reverse-search-uses-bound-kind = refl

regression-wrongtype-does-not-auto-create-disagreement :
  Bridge.wrongTypeDiagnosisAutomaticallyCreatesPartyDisagreement
    Bridge.canonicalPNFWrongTypeLeeBoundary
  ≡ false
regression-wrongtype-does-not-auto-create-disagreement = refl

regression-search-does-not-pay-residual :
  Bridge.compiledSearchDischargesResidual
    Bridge.canonicalPNFWrongTypeLeeBoundary
  ≡ false
regression-search-does-not-pay-residual = refl
