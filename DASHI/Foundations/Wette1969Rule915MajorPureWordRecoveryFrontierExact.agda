module DASHI.Foundations.Wette1969Rule915MajorPureWordRecoveryFrontierExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: PURE-WORD RECOVERY FRONTIER FOR PREMISES 18 / 27
--
-- Printed p.145 fixes the two major slots and §1.632 explains their intended
-- meaning, but the repository deliberately still treats the dense quantified
-- consequent words as parameters.  This module turns the remaining source
-- recovery into an explicit typed certificate: a proposed literal source word
-- cannot be consumed by the major-proof lane until it is identified with the
-- exact consequent already occupying the corresponding typed 9.1.5 slot.
--
-- No canonical recovery value is provided here.  In particular, the semantic
-- paraphrases in §1.632 do not by themselves inhabit this record.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later

WordTerm = Signature.WordTerm
Formula = Signature.Formula

record Rule915MajorPureWordRecovery
    (later : Later.Rule915LaterParameters) : Set where
  constructor rule915MajorPureWordRecovery
  field
    premise18PureConsequent : WordTerm
    premise27PureConsequent : WordTerm

    premise18PureConsequentMatchesTypedSlot :
      premise18PureConsequent ≡ Later.predecessorInductionConsequent later

    premise27PureConsequentMatchesTypedSlot :
      premise27PureConsequent ≡ Later.definiensIndependenceConsequent later

open Rule915MajorPureWordRecovery public

premise18PureFormula :
  (later : Later.Rule915LaterParameters) →
  Rule915MajorPureWordRecovery later →
  Formula
premise18PureFormula later recovery =
  Judgment.implies
    (Later.definitionPrerequisiteWord later)
    (premise18PureConsequent recovery)

premise27PureFormula :
  (later : Later.Rule915LaterParameters) →
  Rule915MajorPureWordRecovery later →
  Formula
premise27PureFormula later recovery =
  Judgment.implies
    (Later.definitionPrerequisiteWord later)
    (premise27PureConsequent recovery)

premise18PureFormulaMatchesTypedSlot :
  (later : Later.Rule915LaterParameters) →
  (recovery : Rule915MajorPureWordRecovery later) →
  premise18PureFormula later recovery ≡ Later.premise18 later
premise18PureFormulaMatchesTypedSlot later recovery
  rewrite premise18PureConsequentMatchesTypedSlot recovery = refl

premise27PureFormulaMatchesTypedSlot :
  (later : Later.Rule915LaterParameters) →
  (recovery : Rule915MajorPureWordRecovery later) →
  premise27PureFormula later recovery ≡ Later.premise27 later
premise27PureFormulaMatchesTypedSlot later recovery
  rewrite premise27PureConsequentMatchesTypedSlot recovery = refl

record Wette1969Rule915MajorPureWordRecoveryFrontierBoundary : Set where
  constructor wette1969Rule915MajorPureWordRecoveryFrontierBoundary
  field
    premise18PureWordRequiresExplicitSourceIdentityCertificate : Bool
    premise18PureWordRequiresExplicitSourceIdentityCertificateIsTrue :
      premise18PureWordRequiresExplicitSourceIdentityCertificate ≡ true

    premise27PureWordRequiresExplicitSourceIdentityCertificate : Bool
    premise27PureWordRequiresExplicitSourceIdentityCertificateIsTrue :
      premise27PureWordRequiresExplicitSourceIdentityCertificate ≡ true

    sourceIdentityCertificateWeldsRecoveredWordsToTyped915Slots : Bool
    sourceIdentityCertificateWeldsRecoveredWordsToTyped915SlotsIsTrue :
      sourceIdentityCertificateWeldsRecoveredWordsToTyped915Slots ≡ true

    semanticSection1632ParaphraseAutomaticallySuppliesPureWordRecovery : Bool
    semanticSection1632ParaphraseAutomaticallySuppliesPureWordRecoveryIsFalse :
      semanticSection1632ParaphraseAutomaticallySuppliesPureWordRecovery ≡ false

    denseMajorConsequentsAlreadyRecoveredCanonicallyHere : Bool
    denseMajorConsequentsAlreadyRecoveredCanonicallyHereIsFalse :
      denseMajorConsequentsAlreadyRecoveredCanonicallyHere ≡ false

canonicalWette1969Rule915MajorPureWordRecoveryFrontierBoundary :
  Wette1969Rule915MajorPureWordRecoveryFrontierBoundary
canonicalWette1969Rule915MajorPureWordRecoveryFrontierBoundary =
  wette1969Rule915MajorPureWordRecoveryFrontierBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
