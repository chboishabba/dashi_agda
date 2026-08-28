module DASHI.Foundations.Wette1969InductionBranchPremise8ProducerExact where

------------------------------------------------------------------------
-- WETTE 9.1.5 PREDECESSOR-INDUCTION BRANCH: INTERNAL PREMISE 8
--
-- Premise 8 is `n V W3`: W3 is a V-place predicate mark.  Rule 4 is its
-- historical producer once W3 is identified with the canonical mark word for
-- an explicit index.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969ObjectVariableMarkWordsExact as ObjectSyntax
import DASHI.Foundations.Wette1969Rule34ObjectProducerExact as Rule34
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Later.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record Premise8ProducerInputs
    (context : Context)
    (later : Later.Rule915LaterParameters) : Set where
  constructor premise8ProducerInputs
  field
    index3 : WordTerm
    mark3Shape :
      Later.predicateMarkW3 later
        ≡ ObjectSyntax.predicateMarkWord (Later.arityWord later) index3
    arityNatural :
      Judgment.naturalNumber (Later.arityWord later) Finite.∈Context context
    indexNatural : Judgment.naturalNumber index3 Finite.∈Context context

open Premise8ProducerInputs public

selectedRule4ForPremise8 :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise8ProducerInputs context later) →
  PCRA.SelectedRuleApplication historicalSystem context
selectedRule4ForPremise8 {context} {later} inputs =
  Rule34.selectRule4
    context (Later.arityWord later) (index3 inputs)
    (arityNatural inputs) (indexNatural inputs)

premise8Trace :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  Premise8ProducerInputs context later →
  PCRA.CertifiedRuleTrace historicalSystem context
premise8Trace inputs =
  PCRA.choose (selectedRule4ForPremise8 inputs) PCRA.done

premise8Available :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise8ProducerInputs context later) →
  Later.premise08 later Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem (premise8Trace inputs))
premise8Available {later = later} inputs
  rewrite mark3Shape inputs = Finite.here

record Wette1969InductionBranchPremise8ProducerBoundary : Set where
  constructor wette1969InductionBranchPremise8ProducerBoundary
  field
    premise8NoLongerNeedsExternalMarkFormationEvidence : Bool
    premise8NoLongerNeedsExternalMarkFormationEvidenceIsTrue :
      premise8NoLongerNeedsExternalMarkFormationEvidence ≡ true
    mark3NaturalIndexEvidenceRemainsExplicit : Bool
    mark3NaturalIndexEvidenceRemainsExplicitIsTrue :
      mark3NaturalIndexEvidenceRemainsExplicit ≡ true

canonicalWette1969InductionBranchPremise8ProducerBoundary :
  Wette1969InductionBranchPremise8ProducerBoundary
canonicalWette1969InductionBranchPremise8ProducerBoundary =
  wette1969InductionBranchPremise8ProducerBoundary true refl true refl
