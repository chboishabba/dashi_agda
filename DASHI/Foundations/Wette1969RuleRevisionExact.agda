module DASHI.Foundations.Wette1969RuleRevisionExact where

------------------------------------------------------------------------
-- WETTE 1969 CRITICAL RULE REVISION SURFACE
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source loci:
--   printed pp. 143--146: pure rule table, especially 9.1.5 and 9.3.24/25;
--   printed pp. 154--155: informal explanation of premises (1),(2) and
--                         conclusion schema (3) behind 9.1.5 / 9.3.24,25;
--   printed pp. 193--194: addendum modifying premise 6 of 9.1.5, adding the
--                         unary _A relator and rules 9.4.1--6, and giving the
--                         final rule-count accounting.
--
-- This module transcribes the *revision geometry and source-visible rule
-- addresses*.  It deliberately does not fabricate unreadable rule bodies from
-- OCR.  Exact historical formula bodies remain a separate transcription task.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.FormalSystemRevisionGeometryExact as Revision

------------------------------------------------------------------------
-- Rule addresses are kept structural so later exact rule bodies can attach to
-- the same source-stable identifiers.
------------------------------------------------------------------------

record HistoricalRuleAddress : Set where
  constructor historicalRuleAddress
  field
    major : Nat
    minor : Nat
    item : Nat

open HistoricalRuleAddress public

rule9-1-5 : HistoricalRuleAddress
rule9-1-5 = historicalRuleAddress 9 1 5

rule9-3-24 : HistoricalRuleAddress
rule9-3-24 = historicalRuleAddress 9 3 24

rule9-3-25 : HistoricalRuleAddress
rule9-3-25 = historicalRuleAddress 9 3 25

rule9-2-0 : HistoricalRuleAddress
rule9-2-0 = historicalRuleAddress 9 2 0

rule9-4-1 : HistoricalRuleAddress
rule9-4-1 = historicalRuleAddress 9 4 1

rule9-4-2 : HistoricalRuleAddress
rule9-4-2 = historicalRuleAddress 9 4 2

rule9-4-3 : HistoricalRuleAddress
rule9-4-3 = historicalRuleAddress 9 4 3

rule9-4-4 : HistoricalRuleAddress
rule9-4-4 = historicalRuleAddress 9 4 4

rule9-4-5 : HistoricalRuleAddress
rule9-4-5 = historicalRuleAddress 9 4 5

rule9-4-6 : HistoricalRuleAddress
rule9-4-6 = historicalRuleAddress 9 4 6

------------------------------------------------------------------------
-- Source-visible critical-rule facts.
------------------------------------------------------------------------

record CriticalRuleSurface : Set where
  constructor criticalRuleSurface
  field
    recursiveDefinitionRule : HistoricalRuleAddress
    recursiveDefinitionPremises : Nat
    recursiveApplicationRuleLeft : HistoricalRuleAddress
    recursiveApplicationRuleRight : HistoricalRuleAddress
    addendumReplacementPremise : Nat
    addendumNewUnaryRelatorRuleCount : Nat

canonicalCriticalRuleSurface : CriticalRuleSurface
canonicalCriticalRuleSurface =
  criticalRuleSurface
    rule9-1-5
    27
    rule9-3-24
    rule9-3-25
    6
    6

------------------------------------------------------------------------
-- The p.193--194 addendum changes the sixth premise of 9.1.5 from the old
-- assertion-schema condition A(U) to the stricter _A(U): "U is an assertion
-- schema over natural numbers without predicate quantification".
--
-- We encode only the historically explicit distinction here.  The symbols are
-- not assigned semantics beyond the source statement.
------------------------------------------------------------------------

data AssertionPremiseKind : Set where
  unrestrictedAssertionSchema : AssertionPremiseKind
  noPredicateQuantificationAssertionSchema : AssertionPremiseKind

record RuleRevision : Set where
  constructor ruleRevision
  field
    revisedRule : HistoricalRuleAddress
    revisedPremise : Nat
    before : AssertionPremiseKind
    after : AssertionPremiseKind

p193Rule915Revision : RuleRevision
p193Rule915Revision =
  ruleRevision
    rule9-1-5
    6
    unrestrictedAssertionSchema
    noPredicateQuantificationAssertionSchema

------------------------------------------------------------------------
-- Exact count accounting from the addendum.
--
-- Wette states that the original compact presentation has 98 rules.  The
-- addendum adds six rules 9.4.1--6 and one bridge rule 9.2.0; six old rules
-- 9.2.1--6 then become dispensable, and two rules under 9.3 are saved.  Hence
-- the final modified presentation has 97 rules.
--
-- Rather than relying on Nat subtraction, the balance is represented as the
-- equivalent positive equation
--
--       98 + 6 + 1 = 97 + 6 + 2.
------------------------------------------------------------------------

originalCompactRuleCount : Nat
originalCompactRuleCount = 98

added94RuleCount : Nat
added94RuleCount = 6

added920RuleCount : Nat
added920RuleCount = 1

removed921To926RuleCount : Nat
removed921To926RuleCount = 6

saved93RuleCount : Nat
saved93RuleCount = 2

finalModifiedRuleCount : Nat
finalModifiedRuleCount = 97

p193RuleCountBalance :
  originalCompactRuleCount + added94RuleCount + added920RuleCount
    ≡ finalModifiedRuleCount + removed921To926RuleCount + saved93RuleCount
p193RuleCountBalance = refl

-- Generic DASHI revision geometry sees exactly the same bookkeeping as
-- seven additions versus eight removals.  This is count reconciliation only;
-- it is not a derivational-equivalence certificate for the two presentations.
p193GenericRuleCountBalance : Revision.RuleCountBalance
p193GenericRuleCountBalance =
  Revision.ruleCountBalance
    originalCompactRuleCount
    (added94RuleCount + added920RuleCount)
    finalModifiedRuleCount
    (removed921To926RuleCount + saved93RuleCount)
    refl

revisionGeometryOwner : Revision.FormalSystemRevisionBoundary
revisionGeometryOwner = Revision.canonicalFormalSystemRevisionBoundary

------------------------------------------------------------------------
-- The source's informal explanation in 1.632 separates three logical roles:
--
--   (1) a predecessor-induction / definition prerequisite;
--   (2) independence of the definiens from non-predecessor predicate values;
--   (3) the recursive application/conversion delivered by 9.3.24/25.
--
-- Capturing these as roles lets later formula transcription connect the exact
-- source strings without prematurely identifying them with semantic truth.
------------------------------------------------------------------------

data RecursiveDefinitionRole : Set where
  predecessorInductionPrerequisite : RecursiveDefinitionRole
  definiensIndependencePrerequisite : RecursiveDefinitionRole
  recursiveApplicationConversion : RecursiveDefinitionRole

record CriticalRuleRoleAssignment : Set where
  constructor criticalRuleRoleAssignment
  field
    rule : HistoricalRuleAddress
    role : RecursiveDefinitionRole

rule915CarriesDefinitionPrerequisites : CriticalRuleRoleAssignment
rule915CarriesDefinitionPrerequisites =
  criticalRuleRoleAssignment rule9-1-5 predecessorInductionPrerequisite

rule9324CarriesRecursiveApplication : CriticalRuleRoleAssignment
rule9324CarriesRecursiveApplication =
  criticalRuleRoleAssignment rule9-3-24 recursiveApplicationConversion

rule9325CarriesRecursiveApplication : CriticalRuleRoleAssignment
rule9325CarriesRecursiveApplication =
  criticalRuleRoleAssignment rule9-3-25 recursiveApplicationConversion

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record Wette1969RuleRevisionBoundary : Set where
  constructor wette1969RuleRevisionBoundary
  field
    p193RevisionTranscribed : Bool
    p193RevisionTranscribedIsTrue : p193RevisionTranscribed ≡ true

    finalRuleCountDerivedFromSourceAccounting : Bool
    finalRuleCountDerivedFromSourceAccountingIsTrue :
      finalRuleCountDerivedFromSourceAccounting ≡ true

    criticalRuleAddressesRecovered : Bool
    criticalRuleAddressesRecoveredIsTrue : criticalRuleAddressesRecovered ≡ true

    criticalRuleBodiesFullyTranscribed : Bool
    criticalRuleBodiesFullyTranscribedIsFalse :
      criticalRuleBodiesFullyTranscribed ≡ false

    countBalanceAlreadyProvesRevisionEquivalence : Bool
    countBalanceAlreadyProvesRevisionEquivalenceIsFalse :
      countBalanceAlreadyProvesRevisionEquivalence ≡ false

    sourceRoleAssignmentIsAlreadySemanticCorrectnessProof : Bool
    sourceRoleAssignmentIsAlreadySemanticCorrectnessProofIsFalse :
      sourceRoleAssignmentIsAlreadySemanticCorrectnessProof ≡ false

canonicalWette1969RuleRevisionBoundary : Wette1969RuleRevisionBoundary
canonicalWette1969RuleRevisionBoundary =
  wette1969RuleRevisionBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
