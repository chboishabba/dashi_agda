module DASHI.Foundations.Wette1969Rule915Premise18ImplicationSpineExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5 PREMISE 18: P.145 IMPLICATION SPINE
--
-- Direct inspection of printed p.145 fixes the source-visible outer word of
-- premise 18.  Under antecedent U1, its consequent is
--
--   U3 -> (V1 V3 -> W3 V3)
--
-- where U3 is the abbreviation introduced immediately beforehand by premise
-- 17, V1 V3 is the condition schema at the fresh tuple, and W3 V3 is the
-- predicate-mark instance used as the induction assertion.
--
-- The dense historical word stored in Rule915LaterParameters remains a
-- parameter.  `Premise18P145SpineRecovery` is the explicit source-identity weld
-- needed to identify that parameter with this recovered outer spine.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later

WordTerm = Signature.WordTerm
Formula = Signature.Formula

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

implicationWord : WordTerm → WordTerm → WordTerm
implicationWord left right =
  Signature.binaryWordTerm Signature.implicationFunctor refl left right

conjoin : WordTerm → WordTerm → WordTerm
conjoin left right =
  Signature.binaryWordTerm Signature.conjunctionFunctor refl left right

conditionAtV3 : Later.Rule915LaterParameters → WordTerm
conditionAtV3 later =
  juxtapose (Later.schemaV1 later) (Later.tupleV3 later)

inductionMarkAtV3 : Later.Rule915LaterParameters → WordTerm
inductionMarkAtV3 later =
  juxtapose (Later.predicateMarkW3 later) (Later.tupleV3 later)

sourceOuterConsequent : Later.Rule915LaterParameters → WordTerm
sourceOuterConsequent later =
  implicationWord
    (Later.expansion17 later)
    (implicationWord
      (conditionAtV3 later)
      (inductionMarkAtV3 later))

premise18OuterFormula : Later.Rule915LaterParameters → Formula
premise18OuterFormula later =
  Judgment.implies
    (Later.definitionPrerequisiteWord later)
    (sourceOuterConsequent later)

firstUncurriedAntecedent : Later.Rule915LaterParameters → WordTerm
firstUncurriedAntecedent later =
  conjoin
    (Later.definitionPrerequisiteWord later)
    (Later.expansion17 later)

firstUncurriedGoal : Later.Rule915LaterParameters → Formula
firstUncurriedGoal later =
  Judgment.implies
    (firstUncurriedAntecedent later)
    (implicationWord
      (conditionAtV3 later)
      (inductionMarkAtV3 later))

coreLeafAntecedent : Later.Rule915LaterParameters → WordTerm
coreLeafAntecedent later =
  conjoin
    (firstUncurriedAntecedent later)
    (conditionAtV3 later)

coreLeaf : Later.Rule915LaterParameters → Formula
coreLeaf later =
  Judgment.implies
    (coreLeafAntecedent later)
    (inductionMarkAtV3 later)

record Premise18P145SpineRecovery
    (later : Later.Rule915LaterParameters) : Set where
  constructor premise18P145SpineRecovery
  field
    predecessorInductionConsequentIsRecoveredP145Spine :
      Later.predecessorInductionConsequent later ≡ sourceOuterConsequent later

open Premise18P145SpineRecovery public

premise18OuterFormulaMatchesTypedSlot :
  (later : Later.Rule915LaterParameters) →
  Premise18P145SpineRecovery later →
  premise18OuterFormula later ≡ Later.premise18 later
premise18OuterFormulaMatchesTypedSlot later recovery
  rewrite predecessorInductionConsequentIsRecoveredP145Spine recovery = refl

record Wette1969Rule915Premise18ImplicationSpineBoundary : Set where
  constructor wette1969Rule915Premise18ImplicationSpineBoundary
  field
    p145OuterConsequentRecoveredAsTwoNestedImplications : Bool
    p145OuterConsequentRecoveredAsTwoNestedImplicationsIsTrue :
      p145OuterConsequentRecoveredAsTwoNestedImplications ≡ true
    firstNestedAntecedentIsPremise17Expansion : Bool
    firstNestedAntecedentIsPremise17ExpansionIsTrue :
      firstNestedAntecedentIsPremise17Expansion ≡ true
    secondNestedAntecedentIsV1AtV3 : Bool
    secondNestedAntecedentIsV1AtV3IsTrue :
      secondNestedAntecedentIsV1AtV3 ≡ true
    finalConsequentIsW3AtV3 : Bool
    finalConsequentIsW3AtV3IsTrue :
      finalConsequentIsW3AtV3 ≡ true
    sourceIdentityWeldStillRequiredForOpaqueTypedSlot : Bool
    sourceIdentityWeldStillRequiredForOpaqueTypedSlotIsTrue :
      sourceIdentityWeldStillRequiredForOpaqueTypedSlot ≡ true
    p145SpineRecoveryByItselfProvesCoreLeaf : Bool
    p145SpineRecoveryByItselfProvesCoreLeafIsFalse :
      p145SpineRecoveryByItselfProvesCoreLeaf ≡ false

canonicalWette1969Rule915Premise18ImplicationSpineBoundary :
  Wette1969Rule915Premise18ImplicationSpineBoundary
canonicalWette1969Rule915Premise18ImplicationSpineBoundary =
  wette1969Rule915Premise18ImplicationSpineBoundary
    true refl true refl true refl true refl true refl false refl
