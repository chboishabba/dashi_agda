module DASHI.Foundations.Wette1969QuantifierCaptureSafetyExact where

------------------------------------------------------------------------
-- WETTE 1969 QUANTIFIER-FRAGMENT CAPTURE SAFETY
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source loci:
--   * printed pp.152--153: substitution replaces free occurrences only;
--     substitution is "konfusionslos" exactly when no free occurrence being
--     replaced lies in the scope of a quantifier that binds a variable occurring
--     free in the substitute;
--   * printed p.153: V and /\ bind their first word in the second-word scope;
--     the recursor introduces an additional binding regime handled separately;
--   * printed p.156, section 1.64: from the construction of P/A one can determine
--     which predicate-mark occurrences are free and which are bound by a
--     generalizer, particularizer, or recursor.
--
-- This module deliberately starts with the source-explicit V / /\ quantifier
-- fragment.  It does not pretend that the recursor binding regime has already
-- been reconstructed.  A safety certificate is therefore available only when a
-- source and substitute are proved to lie in this quantifier fragment.
--
-- Cross-pollination lesson from the repo's reduced-presentation work (e.g. the
-- PR #507 Yang--Mills quotient/reopening lane): a computational presentation is
-- not promoted to the final semantic quotient until the weld theorem is proved.
-- Here likewise the existing schematic substitution evaluator is not promoted
-- to Wette's historical capture-safe substitution merely because it executes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature

WordTerm = Signature.WordTerm

------------------------------------------------------------------------
-- Quantifier fragment.
--
-- The recursor is intentionally absent.  That absence is a positive domain
-- restriction, not an implicit declaration that recursor bodies are capture
-- safe.
------------------------------------------------------------------------

data QuantifierFragment : WordTerm → Set where
  fragmentVariable :
    ∀ {variable} →
    QuantifierFragment (Signature.variableWordTerm variable)

  fragmentConstant :
    ∀ {constant} →
    QuantifierFragment (Signature.constantWordTerm constant)

  fragmentSuccessor :
    ∀ {term} →
    QuantifierFragment term →
    QuantifierFragment
      (Signature.unaryWordTerm Signature.successorFunctor refl term)

  fragmentJuxtaposition :
    ∀ {left right} →
    QuantifierFragment left →
    QuantifierFragment right →
    QuantifierFragment
      (Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right)

  fragmentImplication :
    ∀ {left right} →
    QuantifierFragment left →
    QuantifierFragment right →
    QuantifierFragment
      (Signature.binaryWordTerm Signature.implicationFunctor refl left right)

  fragmentConjunction :
    ∀ {left right} →
    QuantifierFragment left →
    QuantifierFragment right →
    QuantifierFragment
      (Signature.binaryWordTerm Signature.conjunctionFunctor refl left right)

  fragmentDisjunction :
    ∀ {left right} →
    QuantifierFragment left →
    QuantifierFragment right →
    QuantifierFragment
      (Signature.binaryWordTerm Signature.disjunctionFunctor refl left right)

  fragmentParticularization :
    ∀ {binder body} →
    QuantifierFragment binder →
    QuantifierFragment body →
    QuantifierFragment
      (Signature.binaryWordTerm
        Signature.particularizationFunctor refl binder body)

  fragmentGeneralization :
    ∀ {binder body} →
    QuantifierFragment binder →
    QuantifierFragment body →
    QuantifierFragment
      (Signature.binaryWordTerm
        Signature.generalizationFunctor refl binder body)

------------------------------------------------------------------------
-- Proof-relevant free occurrence.
--
-- `needle` is a source word term representing the variable/mark whose free
-- occurrence is being tracked.  At a quantifier body we may descend only when
-- the quantifier binder is distinct from `needle`; the first argument of the
-- quantifier is the binding position and is never counted as a free body
-- occurrence.
------------------------------------------------------------------------

data FreeOccurrence (needle : WordTerm) : WordTerm → Set where
  freeHere : FreeOccurrence needle needle

  freeSuccessor :
    ∀ {term} →
    FreeOccurrence needle term →
    FreeOccurrence needle
      (Signature.unaryWordTerm Signature.successorFunctor refl term)

  freeJuxtapositionLeft :
    ∀ {left right} →
    FreeOccurrence needle left →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right)

  freeJuxtapositionRight :
    ∀ {left right} →
    FreeOccurrence needle right →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right)

  freeImplicationLeft :
    ∀ {left right} →
    FreeOccurrence needle left →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.implicationFunctor refl left right)

  freeImplicationRight :
    ∀ {left right} →
    FreeOccurrence needle right →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.implicationFunctor refl left right)

  freeConjunctionLeft :
    ∀ {left right} →
    FreeOccurrence needle left →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.conjunctionFunctor refl left right)

  freeConjunctionRight :
    ∀ {left right} →
    FreeOccurrence needle right →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.conjunctionFunctor refl left right)

  freeDisjunctionLeft :
    ∀ {left right} →
    FreeOccurrence needle left →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.disjunctionFunctor refl left right)

  freeDisjunctionRight :
    ∀ {left right} →
    FreeOccurrence needle right →
    FreeOccurrence needle
      (Signature.binaryWordTerm Signature.disjunctionFunctor refl left right)

  freeUnderParticularization :
    ∀ {binder body} →
    (needle ≡ binder → ⊥) →
    FreeOccurrence needle body →
    FreeOccurrence needle
      (Signature.binaryWordTerm
        Signature.particularizationFunctor refl binder body)

  freeUnderGeneralization :
    ∀ {binder body} →
    (needle ≡ binder → ⊥) →
    FreeOccurrence needle body →
    FreeOccurrence needle
      (Signature.binaryWordTerm
        Signature.generalizationFunctor refl binder body)

------------------------------------------------------------------------
-- Source-faithful capture-risk witness.
--
-- Wette's criterion says capture occurs when a free occurrence of the
-- substituend lies inside the scope of a quantifier whose bound variable occurs
-- free in the substitute.  The first two constructors are precisely that local
-- condition for V and /\.  The remaining constructors transport a risk witness
-- through surrounding quantifier-fragment syntax.
------------------------------------------------------------------------

data QuantifierCaptureRisk
    (substituend substitute : WordTerm) : WordTerm → Set where
  captureAtParticularization :
    ∀ {binder body} →
    (substituend ≡ binder → ⊥) →
    FreeOccurrence substituend body →
    FreeOccurrence binder substitute →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm
        Signature.particularizationFunctor refl binder body)

  captureAtGeneralization :
    ∀ {binder body} →
    (substituend ≡ binder → ⊥) →
    FreeOccurrence substituend body →
    FreeOccurrence binder substitute →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm
        Signature.generalizationFunctor refl binder body)

  captureUnderSuccessor :
    ∀ {term} →
    QuantifierCaptureRisk substituend substitute term →
    QuantifierCaptureRisk substituend substitute
      (Signature.unaryWordTerm Signature.successorFunctor refl term)

  captureUnderJuxtapositionLeft :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute left →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right)

  captureUnderJuxtapositionRight :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute right →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right)

  captureUnderImplicationLeft :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute left →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.implicationFunctor refl left right)

  captureUnderImplicationRight :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute right →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.implicationFunctor refl left right)

  captureUnderConjunctionLeft :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute left →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.conjunctionFunctor refl left right)

  captureUnderConjunctionRight :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute right →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.conjunctionFunctor refl left right)

  captureUnderDisjunctionLeft :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute left →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.disjunctionFunctor refl left right)

  captureUnderDisjunctionRight :
    ∀ {left right} →
    QuantifierCaptureRisk substituend substitute right →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm Signature.disjunctionFunctor refl left right)

  captureUnderParticularizationBody :
    ∀ {binder body} →
    (substituend ≡ binder → ⊥) →
    QuantifierCaptureRisk substituend substitute body →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm
        Signature.particularizationFunctor refl binder body)

  captureUnderGeneralizationBody :
    ∀ {binder body} →
    (substituend ≡ binder → ⊥) →
    QuantifierCaptureRisk substituend substitute body →
    QuantifierCaptureRisk substituend substitute
      (Signature.binaryWordTerm
        Signature.generalizationFunctor refl binder body)

------------------------------------------------------------------------
-- Positive safety certificate restricted to the recovered quantifier fragment.
------------------------------------------------------------------------

record QuantifierCaptureSafe
    (substituend substitute source : WordTerm) : Set where
  constructor quantifierCaptureSafe
  field
    sourceInRecoveredQuantifierFragment : QuantifierFragment source
    substituteInRecoveredQuantifierFragment : QuantifierFragment substitute
    noSourceQuantifierCapturesSubstitute :
      ¬ QuantifierCaptureRisk substituend substitute source

open QuantifierCaptureSafe public

captureRiskRefutesSafety :
  ∀ {substituend substitute source} →
  QuantifierCaptureRisk substituend substitute source →
  ¬ QuantifierCaptureSafe substituend substitute source
captureRiskRefutesSafety risk safe =
  noSourceQuantifierCapturesSubstitute safe risk

particularizationCaptureIsUnsafe :
  ∀ {substituend substitute binder body} →
  (substituend ≡ binder → ⊥) →
  FreeOccurrence substituend body →
  FreeOccurrence binder substitute →
  ¬ QuantifierCaptureSafe
      substituend substitute
      (Signature.binaryWordTerm
        Signature.particularizationFunctor refl binder body)
particularizationCaptureIsUnsafe distinct freeSubstituend freeBinder =
  captureRiskRefutesSafety
    (captureAtParticularization distinct freeSubstituend freeBinder)

generalizationCaptureIsUnsafe :
  ∀ {substituend substitute binder body} →
  (substituend ≡ binder → ⊥) →
  FreeOccurrence substituend body →
  FreeOccurrence binder substitute →
  ¬ QuantifierCaptureSafe
      substituend substitute
      (Signature.binaryWordTerm
        Signature.generalizationFunctor refl binder body)
generalizationCaptureIsUnsafe distinct freeSubstituend freeBinder =
  captureRiskRefutesSafety
    (captureAtGeneralization distinct freeSubstituend freeBinder)

------------------------------------------------------------------------
-- Recovery / promotion boundary.
------------------------------------------------------------------------

record Wette1969QuantifierCaptureSafetyBoundary : Set where
  constructor wette1969QuantifierCaptureSafetyBoundary
  field
    sourceQuantifierCaptureCriterionNowTyped : Bool
    sourceQuantifierCaptureCriterionNowTypedIsTrue :
      sourceQuantifierCaptureCriterionNowTyped ≡ true

    freeOccurrenceRespectsParticularizerAndGeneralizerBinding : Bool
    freeOccurrenceRespectsParticularizerAndGeneralizerBindingIsTrue :
      freeOccurrenceRespectsParticularizerAndGeneralizerBinding ≡ true

    directCaptureRiskRefutesSafety : Bool
    directCaptureRiskRefutesSafetyIsTrue :
      directCaptureRiskRefutesSafety ≡ true

    recursorBindingRegimeAlreadyIncluded : Bool
    recursorBindingRegimeAlreadyIncludedIsFalse :
      recursorBindingRegimeAlreadyIncluded ≡ false

    historicalVariableWellFormednessAlreadyDecidedByThisLayer : Bool
    historicalVariableWellFormednessAlreadyDecidedByThisLayerIsFalse :
      historicalVariableWellFormednessAlreadyDecidedByThisLayer ≡ false

    existingSchematicEvaluatorAlreadyDischargesQuantifierCaptureSafety : Bool
    existingSchematicEvaluatorAlreadyDischargesQuantifierCaptureSafetyIsFalse :
      existingSchematicEvaluatorAlreadyDischargesQuantifierCaptureSafety ≡ false

    quantifierFragmentSafetyIsFullHistoricalSubstitutionSafety : Bool
    quantifierFragmentSafetyIsFullHistoricalSubstitutionSafetyIsFalse :
      quantifierFragmentSafetyIsFullHistoricalSubstitutionSafety ≡ false

canonicalWette1969QuantifierCaptureSafetyBoundary :
  Wette1969QuantifierCaptureSafetyBoundary
canonicalWette1969QuantifierCaptureSafetyBoundary =
  wette1969QuantifierCaptureSafetyBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
