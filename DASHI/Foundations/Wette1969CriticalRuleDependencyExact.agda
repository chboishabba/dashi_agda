module DASHI.Foundations.Wette1969CriticalRuleDependencyExact where

------------------------------------------------------------------------
-- WETTE 1969 CRITICAL RULE DEPENDENCY GEOMETRY
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source loci:
--   printed p.145: literal surface of 9.1.5 and shared-premise 9.3.24/25;
--   printed pp.154--156, section 1.632: Wette's own decomposition of the
--   twenty L-caused premises, the roles of premises 18 and 27, and the
--   ordered-substitution/freshness explanation for 9.3.24/25.
--
-- Kreisel--Zucker source calibration:
-- JSL 37(1), 1972, pp.203--204, DOI 10.2307/2272630.
--
-- This module transcribes dependency structure stated by Wette. It does not
-- claim that the OCR representation of every symbolic formula in 9.1.5 has
-- already been recovered exactly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RulePremiseDependencyGeometryExact as Dependency
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

------------------------------------------------------------------------
-- Source positions 1--27 of rule 9.1.5.
------------------------------------------------------------------------

data Premise915 : Set where
  p01 p02 p03 p04 p05 p06 p07 : Premise915
  p08 p09 p10 p11 p12 p13 p14 p15 : Premise915
  p16 p17 p18 : Premise915
  p19 p20 p21 p22 p23 p24 p25 : Premise915
  p26 p27 : Premise915

data CriticalObligation : Set where
  predicateFormationSurface : CriticalObligation
  predecessorInductionPrerequisite : CriticalObligation
  definiensIndependencePrerequisite : CriticalObligation

-- Wette says the first seven premises form the initial skeletal layer; the
-- remaining twenty premises (lines 2--9 of 9.1.5) are caused by the implication
-- derivability relation L.
data Supports915 : Premise915 → CriticalObligation → Set where
  s01 : Supports915 p01 predicateFormationSurface
  s02 : Supports915 p02 predicateFormationSurface
  s03 : Supports915 p03 predicateFormationSurface
  s04 : Supports915 p04 predicateFormationSurface
  s05 : Supports915 p05 predicateFormationSurface
  s06 : Supports915 p06 predicateFormationSurface
  s07 : Supports915 p07 predicateFormationSurface

  -- Source §1.632: premises 8--15 belong to premise 18; 16 and 17 supply
  -- abbreviations used to express 18; premise 18 is the induction condition.
  s08-18 : Supports915 p08 predecessorInductionPrerequisite
  s09-18 : Supports915 p09 predecessorInductionPrerequisite
  s10-18 : Supports915 p10 predecessorInductionPrerequisite
  s11-18 : Supports915 p11 predecessorInductionPrerequisite
  s12-18 : Supports915 p12 predecessorInductionPrerequisite
  s13-18 : Supports915 p13 predecessorInductionPrerequisite
  s14-18 : Supports915 p14 predecessorInductionPrerequisite
  s15-18 : Supports915 p15 predecessorInductionPrerequisite
  s16-18 : Supports915 p16 predecessorInductionPrerequisite
  s17-18 : Supports915 p17 predecessorInductionPrerequisite
  s18-18 : Supports915 p18 predecessorInductionPrerequisite

  -- Source §1.632: premises 19--25, together with 10--15, belong to premise
  -- 27; premise 26 supplies an abbreviation used to express 27.
  s10-27 : Supports915 p10 definiensIndependencePrerequisite
  s11-27 : Supports915 p11 definiensIndependencePrerequisite
  s12-27 : Supports915 p12 definiensIndependencePrerequisite
  s13-27 : Supports915 p13 definiensIndependencePrerequisite
  s14-27 : Supports915 p14 definiensIndependencePrerequisite
  s15-27 : Supports915 p15 definiensIndependencePrerequisite
  s19-27 : Supports915 p19 definiensIndependencePrerequisite
  s20-27 : Supports915 p20 definiensIndependencePrerequisite
  s21-27 : Supports915 p21 definiensIndependencePrerequisite
  s22-27 : Supports915 p22 definiensIndependencePrerequisite
  s23-27 : Supports915 p23 definiensIndependencePrerequisite
  s24-27 : Supports915 p24 definiensIndependencePrerequisite
  s25-27 : Supports915 p25 definiensIndependencePrerequisite
  s26-27 : Supports915 p26 definiensIndependencePrerequisite
  s27-27 : Supports915 p27 definiensIndependencePrerequisite

critical915DependencyGeometry : Dependency.PremiseDependencyGeometry
critical915DependencyGeometry =
  Dependency.premiseDependencyGeometry
    Premise915
    CriticalObligation
    Supports915

-- The overlap of premises 10--15 is source-significant: the same syntactic
-- freshness/substitution infrastructure contributes to both major obligations.
premise10SupportsInduction :
  Dependency.Supports critical915DependencyGeometry p10 predecessorInductionPrerequisite
premise10SupportsInduction = s10-18

premise10SupportsIndependence :
  Dependency.Supports critical915DependencyGeometry p10 definiensIndependencePrerequisite
premise10SupportsIndependence = s10-27

------------------------------------------------------------------------
-- Source-level semantic roles of the two decisive premises.
--
-- Wette's own prose in §1.632 says:
--   premise 18 expresses that the definition prerequisite implies P-conditioned
--   predecessor induction with respect to R;
--   premise 27 expresses P-conditioned independence of the definiens schema
--   A(x,pi) from non-predecessor values of pi with respect to R.
------------------------------------------------------------------------

record Critical915SourceMeaning : Set where
  constructor mkCritical915SourceMeaning
  field
    rule : Revision.HistoricalRuleAddress
    inductionPremiseNumber : Nat
    independencePremiseNumber : Nat

critical915SourceMeaning : Critical915SourceMeaning
critical915SourceMeaning =
  mkCritical915SourceMeaning Revision.rule9-1-5 18 27

------------------------------------------------------------------------
-- 9.3.24 and 9.3.25 are printed with the same four premises followed by two
-- conclusions. Wette explains that premise 3 is a freshness condition, while
-- premise 4 is an ordered substitution condition: first substitute the new
-- variable tuple for the old tuple in the definiens, then substitute the
-- recursively defined predicate for the predicate mark.
------------------------------------------------------------------------

data Premise9324x25 : Set where
  recursivePredicateFormation : Premise9324x25
  freshVariableTupleFormation : Premise9324x25
  variableFreshnessCondition : Premise9324x25
  orderedSubstitutionCondition : Premise9324x25

data RecursiveApplicationConclusion : Set where
  leftRecursiveApplication : RecursiveApplicationConclusion
  rightRecursiveApplication : RecursiveApplicationConclusion

shared9324x25Surface : Dependency.SharedPremiseRulePair
shared9324x25Surface =
  Dependency.sharedPremiseRulePair
    Premise9324x25
    RecursiveApplicationConclusion
    (recursivePredicateFormation ∷
     freshVariableTupleFormation ∷
     variableFreshnessCondition ∷
     orderedSubstitutionCondition ∷ [])
    leftRecursiveApplication
    rightRecursiveApplication

record CriticalApplicationSurface : Set where
  constructor mkCriticalApplicationSurface
  field
    leftRule : Revision.HistoricalRuleAddress
    rightRule : Revision.HistoricalRuleAddress
    sharedPremiseCount : Nat
    freshnessPremiseNumber : Nat
    orderedSubstitutionPremiseNumber : Nat

criticalApplicationSurface : CriticalApplicationSurface
criticalApplicationSurface =
  mkCriticalApplicationSurface
    Revision.rule9-3-24
    Revision.rule9-3-25
    4
    3
    4

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record Wette1969CriticalRuleDependencyBoundary : Set where
  constructor wette1969CriticalRuleDependencyBoundary
  field
    premise18InductionRoleRecovered : Bool
    premise18InductionRoleRecoveredIsTrue :
      premise18InductionRoleRecovered ≡ true

    premise27IndependenceRoleRecovered : Bool
    premise27IndependenceRoleRecoveredIsTrue :
      premise27IndependenceRoleRecovered ≡ true

    premises10To15SupportBothMajorObligations : Bool
    premises10To15SupportBothMajorObligationsIsTrue :
      premises10To15SupportBothMajorObligations ≡ true

    rules9324And9325ShareFourPremises : Bool
    rules9324And9325ShareFourPremisesIsTrue :
      rules9324And9325ShareFourPremises ≡ true

    orderedSubstitutionRequirementRecovered : Bool
    orderedSubstitutionRequirementRecoveredIsTrue :
      orderedSubstitutionRequirementRecovered ≡ true

    dependencyTranscriptionIsAlreadyExactFormulaBodyTranscription : Bool
    dependencyTranscriptionIsAlreadyExactFormulaBodyTranscriptionIsFalse :
      dependencyTranscriptionIsAlreadyExactFormulaBodyTranscription ≡ false

    sourceMeaningIsAlreadySemanticCorrectnessProof : Bool
    sourceMeaningIsAlreadySemanticCorrectnessProofIsFalse :
      sourceMeaningIsAlreadySemanticCorrectnessProof ≡ false

canonicalWette1969CriticalRuleDependencyBoundary :
  Wette1969CriticalRuleDependencyBoundary
canonicalWette1969CriticalRuleDependencyBoundary =
  wette1969CriticalRuleDependencyBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
