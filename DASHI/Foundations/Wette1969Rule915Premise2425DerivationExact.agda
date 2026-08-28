module DASHI.Foundations.Wette1969Rule915Premise2425DerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5 PREMISES 24/25 AS GENERATED PAIRED II JUDGEMENTS
--
-- Printed p.145 gives the two premises as paired substitutions
--
--   II (u W2 V2) U (u W4 V3) U4
--   II (u W2 V2) U (u W5 V3) U5.
--
-- Section 1.632 says their component-substitution order is irrelevant under the
-- surrounding distinctness/freshness hypotheses.  We choose the p.148 / 8.2.8
-- component order W2 first, then V2, and generate each paired II by the already
-- certified historical 8.2 derivation machinery.  No commutativity theorem is
-- needed for this positive producer path.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969QuantifierCaptureSafetyExact as Capture
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969CertifiedTwoStageIIDerivationExact as CertifiedTwoStage
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Later.WordTerm
Context = Finite.DerivationContext

historicalSystem = Closure.historicalApplicationSystem

premise24Stages :
  (p : Later.Rule915LaterParameters) →
  (intermediate : WordTerm) →
  Capture.QuantifierCaptureSafe
    (Later.predicateMarkW2 p)
    (Later.predicateMarkW4 p)
    (Later.definiensSchemaWord p) →
  Capture.QuantifierCaptureSafe
    (Later.tupleV2 p)
    (Later.tupleV3 p)
    intermediate →
  TwoStage.DependentTwoStageSubstitution
premise24Stages p intermediate firstSafe secondSafe =
  TwoStage.dependentTwoStageSubstitution first second
  where
    first : TwoStage.TupleSubstitutionStage
    first =
      TwoStage.tupleSubstitutionStage
        (Later.predicateMarkW2 p)
        (Later.predicateMarkW4 p)
        (Later.definiensSchemaWord p)
        intermediate
        firstSafe

    second : TwoStage.PredicateSubstitutionStage first
    second =
      TwoStage.predicateSubstitutionStage
        (Later.tupleV2 p)
        (Later.tupleV3 p)
        (Later.substitutionResultU4 p)
        secondSafe

premise25Stages :
  (p : Later.Rule915LaterParameters) →
  (intermediate : WordTerm) →
  Capture.QuantifierCaptureSafe
    (Later.predicateMarkW2 p)
    (Later.predicateMarkW5 p)
    (Later.definiensSchemaWord p) →
  Capture.QuantifierCaptureSafe
    (Later.tupleV2 p)
    (Later.tupleV3 p)
    intermediate →
  TwoStage.DependentTwoStageSubstitution
premise25Stages p intermediate firstSafe secondSafe =
  TwoStage.dependentTwoStageSubstitution first second
  where
    first : TwoStage.TupleSubstitutionStage
    first =
      TwoStage.tupleSubstitutionStage
        (Later.predicateMarkW2 p)
        (Later.predicateMarkW5 p)
        (Later.definiensSchemaWord p)
        intermediate
        firstSafe

    second : TwoStage.PredicateSubstitutionStage first
    second =
      TwoStage.predicateSubstitutionStage
        (Later.tupleV2 p)
        (Later.tupleV3 p)
        (Later.substitutionResultU5 p)
        secondSafe

premise24IsPairedII :
  (p : Later.Rule915LaterParameters) →
  (intermediate : WordTerm) →
  (firstSafe : Capture.QuantifierCaptureSafe
    (Later.predicateMarkW2 p) (Later.predicateMarkW4 p)
    (Later.definiensSchemaWord p)) →
  (secondSafe : Capture.QuantifierCaptureSafe
    (Later.tupleV2 p) (Later.tupleV3 p) intermediate) →
  TwoStage.pairedII (premise24Stages p intermediate firstSafe secondSafe)
    ≡ Later.premise24 p
premise24IsPairedII p intermediate firstSafe secondSafe = refl

premise25IsPairedII :
  (p : Later.Rule915LaterParameters) →
  (intermediate : WordTerm) →
  (firstSafe : Capture.QuantifierCaptureSafe
    (Later.predicateMarkW2 p) (Later.predicateMarkW5 p)
    (Later.definiensSchemaWord p)) →
  (secondSafe : Capture.QuantifierCaptureSafe
    (Later.tupleV2 p) (Later.tupleV3 p) intermediate) →
  TwoStage.pairedII (premise25Stages p intermediate firstSafe secondSafe)
    ≡ Later.premise25 p
premise25IsPairedII p intermediate firstSafe secondSafe = refl

premise24AvailableFromCertifiedStages :
  {context : Context} →
  (p : Later.Rule915LaterParameters) →
  (intermediate : WordTerm) →
  (firstSafe : Capture.QuantifierCaptureSafe
    (Later.predicateMarkW2 p) (Later.predicateMarkW4 p)
    (Later.definiensSchemaWord p)) →
  (secondSafe : Capture.QuantifierCaptureSafe
    (Later.tupleV2 p) (Later.tupleV3 p) intermediate) →
  (derivation : CertifiedTwoStage.CertifiedTwoStageIIDerivation
    context (premise24Stages p intermediate firstSafe secondSafe)) →
  Later.premise24 p Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem
      (CertifiedTwoStage.pairedTrace derivation))
premise24AvailableFromCertifiedStages p intermediate firstSafe secondSafe derivation
  rewrite sym (premise24IsPairedII p intermediate firstSafe secondSafe) =
  CertifiedTwoStage.pairedIIAvailable derivation

premise25AvailableFromCertifiedStages :
  {context : Context} →
  (p : Later.Rule915LaterParameters) →
  (intermediate : WordTerm) →
  (firstSafe : Capture.QuantifierCaptureSafe
    (Later.predicateMarkW2 p) (Later.predicateMarkW5 p)
    (Later.definiensSchemaWord p)) →
  (secondSafe : Capture.QuantifierCaptureSafe
    (Later.tupleV2 p) (Later.tupleV3 p) intermediate) →
  (derivation : CertifiedTwoStage.CertifiedTwoStageIIDerivation
    context (premise25Stages p intermediate firstSafe secondSafe)) →
  Later.premise25 p Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem
      (CertifiedTwoStage.pairedTrace derivation))
premise25AvailableFromCertifiedStages p intermediate firstSafe secondSafe derivation
  rewrite sym (premise25IsPairedII p intermediate firstSafe secondSafe) =
  CertifiedTwoStage.pairedIIAvailable derivation

record Wette1969Rule915Premise2425Boundary : Set where
  constructor wette1969Rule915Premise2425Boundary
  field
    premise24CanBeGeneratedByHistorical82Composition : Bool
    premise24CanBeGeneratedByHistorical82CompositionIsTrue :
      premise24CanBeGeneratedByHistorical82Composition ≡ true
    premise25CanBeGeneratedByHistorical82Composition : Bool
    premise25CanBeGeneratedByHistorical82CompositionIsTrue :
      premise25CanBeGeneratedByHistorical82Composition ≡ true
    oneSourcePermittedComponentOrderSufficesForPositiveDerivation : Bool
    oneSourcePermittedComponentOrderSufficesForPositiveDerivationIsTrue :
      oneSourcePermittedComponentOrderSufficesForPositiveDerivation ≡ true
    generatedPremises2425AlreadyProveOrderIndependence : Bool
    generatedPremises2425AlreadyProveOrderIndependenceIsFalse :
      generatedPremises2425AlreadyProveOrderIndependence ≡ false

canonicalWette1969Rule915Premise2425Boundary :
  Wette1969Rule915Premise2425Boundary
canonicalWette1969Rule915Premise2425Boundary =
  wette1969Rule915Premise2425Boundary
    true refl true refl true refl false refl
