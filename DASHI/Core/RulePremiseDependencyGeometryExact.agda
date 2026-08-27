module DASHI.Core.RulePremiseDependencyGeometryExact where

------------------------------------------------------------------------
-- RULE PREMISE DEPENDENCY GEOMETRY
--
-- Generic owner for a pattern that occurs in large historical and generated
-- calculi: one rule can have many syntactic premises, while different logical
-- obligations depend on overlapping subsets of those premises.
--
-- A premise being listed in a rule is not the same thing as knowing which
-- higher-level obligation it supports.  Conversely, two obligations may share
-- premises without becoming the same obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record PremiseDependencyGeometry : Set₁ where
  constructor premiseDependencyGeometry
  field
    Premise : Set
    Obligation : Set
    Supports : Premise → Obligation → Set

open PremiseDependencyGeometry public

record SharedPremiseRulePair : Set₁ where
  constructor sharedPremiseRulePair
  field
    Premise : Set
    Conclusion : Set
    commonPremises : List Premise
    leftConclusion : Conclusion
    rightConclusion : Conclusion

open SharedPremiseRulePair public

record RulePremiseDependencyBoundary : Set where
  constructor rulePremiseDependencyBoundary
  field
    onePremiseMaySupportMultipleObligations : Bool
    onePremiseMaySupportMultipleObligationsIsTrue :
      onePremiseMaySupportMultipleObligations ≡ true

    overlappingPremiseSupportMakesObligationsDefinitionallyEqual : Bool
    overlappingPremiseSupportMakesObligationsDefinitionallyEqualIsFalse :
      overlappingPremiseSupportMakesObligationsDefinitionallyEqual ≡ false

    sharedPrintedPremisesForceOnePrimitiveMultiConclusionRule : Bool
    sharedPrintedPremisesForceOnePrimitiveMultiConclusionRuleIsFalse :
      sharedPrintedPremisesForceOnePrimitiveMultiConclusionRule ≡ false

canonicalRulePremiseDependencyBoundary : RulePremiseDependencyBoundary
canonicalRulePremiseDependencyBoundary =
  rulePremiseDependencyBoundary
    true refl
    false refl
    false refl
