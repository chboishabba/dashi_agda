module DASHI.Reasoning.JusticeLeeSensibLawPNFWrongTypeBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawResidualLattice as SL
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as Wrong
import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Lee
import DASHI.Reasoning.JusticeLeeSensibLawBidiSearchClosureExact as Search

------------------------------------------------------------------------
-- PNF -> CONSUMER-TYPED WRONGTYPE -> LEE CONTROVERSY BRIDGE
--
-- Canonical-owner discipline:
--   * SL owns PredicatePNF and source-span emission receipts;
--   * Wrong owns consumer/factorisation mismatch vocabulary;
--   * Lee owns proposition fibres, typed disagreement, proof obligations and
--     the adjudicative-authority firewall;
--   * Search owns consumer-indexed residual -> obligation -> discriminator ->
--     evidence-probe compilation.
--
-- This module owns only the missing adapter.  A PNF emission does not become a
-- legal proposition by itself.  A WrongType diagnosis does not become a party
-- disagreement by itself.  Mapping a diagnosed mismatch into a Lee residual is
-- therefore an explicit witnessed binding rather than a total function.
------------------------------------------------------------------------

record ConsumerPNFContext : Set where
  constructor consumer-pnf-context
  field
    contextEmission : SL.PNFEmissionReceipt
    contextConsumerReference : String
    contextQueryReference : String
    contextReference : String
open ConsumerPNFContext public

------------------------------------------------------------------------
-- 1. Consumer typing is distinct from controversy.
------------------------------------------------------------------------

record PNFConsumerAdequacyReceipt : Set where
  constructor pnf-consumer-adequacy-receipt
  field
    adequateContext : ConsumerPNFContext
    adequacyReference : String
open PNFConsumerAdequacyReceipt public

record PNFConsumerWrongTypeDiagnosis : Set where
  constructor pnf-consumer-wrongtype-diagnosis
  field
    diagnosisContext : ConsumerPNFContext
    diagnosisMismatch : Wrong.AbstractWrongTypeMismatch
    diagnosisReference : String
open PNFConsumerWrongTypeDiagnosis public

data PNFConsumerTypingResult : Set where
  adequateForDeclaredConsumer :
    PNFConsumerAdequacyReceipt →
    PNFConsumerTypingResult
  wrongTypeForDeclaredConsumer :
    PNFConsumerWrongTypeDiagnosis →
    PNFConsumerTypingResult

------------------------------------------------------------------------
-- 2. Legal fibre projection requires explicit legal/epistemic coordinates.
------------------------------------------------------------------------

record LegalFibreProjection : Set where
  constructor legal-fibre-projection
  field
    fibreContext : ConsumerPNFContext
    fibreParty : Lee.PartyRole
    fibreLegalRole : Lee.LegalRole
    fibreStatus : Lee.EpistemicStatus
    fibreEvidenceKind : Lee.EvidenceKind
    fibreTemporalReference : String
    fibreRelationReference : String
    fibreProjectionReference : String
open LegalFibreProjection public

projectLegalFibre : LegalFibreProjection → Lee.PropositionFibre
projectLegalFibre projection =
  Lee.propositionFibre
    (SL.PNFEmissionReceipt.emittedAtom
      (contextEmission (fibreContext projection)))
    (fibreParty projection)
    (fibreLegalRole projection)
    (fibreStatus projection)
    (SL.PNFEmissionReceipt.sourceSpan
      (contextEmission (fibreContext projection)))
    (fibreEvidenceKind projection)
    (fibreTemporalReference projection)
    (fibreRelationReference projection)

------------------------------------------------------------------------
-- 3. WrongType -> controversy is explicit and proof-relevant.
--
-- There is deliberately no function
--
--   AbstractWrongTypeMismatch -> Lee.DisagreementKind
--
-- because a representation/consumer mismatch can remain pre-controversy, can
-- require repair, or can participate in more than one legally relevant
-- disagreement depending on the declared Matter/consumer.
------------------------------------------------------------------------

record WrongTypeResidualBinding
    (diagnosis : PNFConsumerWrongTypeDiagnosis) : Set where
  constructor wrongtype-residual-binding
  field
    bindingApplicantProjection : LegalFibreProjection
    bindingRespondentProjection : LegalFibreProjection

    applicantAtomMatchesDiagnosis :
      Lee.atom (projectLegalFibre bindingApplicantProjection)
      ≡
      SL.PNFEmissionReceipt.emittedAtom
        (contextEmission (diagnosisContext diagnosis))

    respondentAtomMatchesDiagnosis :
      Lee.atom (projectLegalFibre bindingRespondentProjection)
      ≡
      SL.PNFEmissionReceipt.emittedAtom
        (contextEmission (diagnosisContext diagnosis))

    applicantConsumerMatchesDiagnosis :
      contextConsumerReference (fibreContext bindingApplicantProjection)
      ≡
      contextConsumerReference (diagnosisContext diagnosis)

    respondentConsumerMatchesDiagnosis :
      contextConsumerReference (fibreContext bindingRespondentProjection)
      ≡
      contextConsumerReference (diagnosisContext diagnosis)

    bindingResidualKind : Lee.DisagreementKind
    bindingResidualLevel : SL.ResidualLevel
    bindingUnresolvedQuestion : String
    bindingReference : String
open WrongTypeResidualBinding public

compileControversyResidual :
  ∀ {diagnosis} →
  WrongTypeResidualBinding diagnosis →
  Lee.ControversyResidual
compileControversyResidual binding =
  Lee.controversyResidual
    (bindingResidualKind binding)
    (projectLegalFibre (bindingApplicantProjection binding))
    (projectLegalFibre (bindingRespondentProjection binding))
    (bindingResidualLevel binding)
    (bindingUnresolvedQuestion binding)

compileSearchObligation :
  ∀ {diagnosis} →
  Search.ProceduralConsumer →
  WrongTypeResidualBinding diagnosis →
  Search.CompiledSearchObligation
compileSearchObligation consumer binding =
  Search.compileSearchObligation
    consumer
    (bindingResidualKind binding)

compiledSearchUsesExplicitResidualBinding :
  ∀ {diagnosis}
    (consumer : Search.ProceduralConsumer)
    (binding : WrongTypeResidualBinding diagnosis) →
  Search.residualKind (compileSearchObligation consumer binding)
  ≡ bindingResidualKind binding
compiledSearchUsesExplicitResidualBinding consumer binding = refl

------------------------------------------------------------------------
-- 4. Canonical no-collapse boundary.
------------------------------------------------------------------------

record PNFWrongTypeLeeBoundary : Set where
  constructor pnf-wrongtype-lee-boundary
  field
    pnfEmissionAloneCreatesLegalProposition : Bool
    pnfEmissionAloneCreatesLegalPropositionIsFalse :
      pnfEmissionAloneCreatesLegalProposition ≡ false

    wrongTypeDiagnosisAutomaticallyCreatesPartyDisagreement : Bool
    wrongTypeDiagnosisAutomaticallyCreatesPartyDisagreementIsFalse :
      wrongTypeDiagnosisAutomaticallyCreatesPartyDisagreement ≡ false

    wrongTypeDiagnosisAutomaticallyDeterminesResidualKind : Bool
    wrongTypeDiagnosisAutomaticallyDeterminesResidualKindIsFalse :
      wrongTypeDiagnosisAutomaticallyDeterminesResidualKind ≡ false

    residualBindingCreatesClaimTruth : Bool
    residualBindingCreatesClaimTruthIsFalse :
      residualBindingCreatesClaimTruth ≡ false

    compiledSearchDischargesResidual : Bool
    compiledSearchDischargesResidualIsFalse :
      compiledSearchDischargesResidual ≡ false

    leeOwnsDashiBridgeTheorem : Bool
    leeOwnsDashiBridgeTheoremIsFalse :
      leeOwnsDashiBridgeTheorem ≡ false
open PNFWrongTypeLeeBoundary public

canonicalPNFWrongTypeLeeBoundary : PNFWrongTypeLeeBoundary
canonicalPNFWrongTypeLeeBoundary =
  pnf-wrongtype-lee-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Attribution boundary.
--
-- Justice Lee motivates proposition-oriented corpus interrogation,
-- source-linked structured synthesis and retention of human adjudicative
-- judgment.  The PNF carrier, WrongType calculus, explicit residual binding
-- and compiler above are DASHI/SensibLaw constructions.
------------------------------------------------------------------------
