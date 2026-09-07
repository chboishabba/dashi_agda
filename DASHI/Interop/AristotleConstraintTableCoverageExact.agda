module DASHI.Interop.AristotleConstraintTableCoverageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Source contracts rechecked against RequestProject.Qualifiers.
--
-- Aristotle's executable tables treat a property with no qualifier/scope entry
-- as unconstrained. SensibLaw may use that only when the relevant profile table
-- was itself covered. Missing from an uninspected table remains uninspected.
------------------------------------------------------------------------

data ConstraintProfileCoverage : Set where
  profileComplete profileIncomplete profileUninspected profileInvalid : ConstraintProfileCoverage

data ConstraintAssessment : Set where
  constraintValid constraintInvalid constraintUnconstrained constraintUninspected : ConstraintAssessment

record AristotleConstraintContract : Set where
  constructor aristotle-constraint-contract
  field
    sourceModule : String
    declaration : String
    contractReference : String
open AristotleConstraintContract public

qualifierAbsentProfileContract : AristotleConstraintContract
qualifierAbsentProfileContract =
  aristotle-constraint-contract
    "RequestProject.Qualifiers"
    "Wikidata.qualSetOk_of_not_mem_table"
    "a claim whose property is absent from the supplied qualifier table is not rejected"

scopeMainDefaultContract : AristotleConstraintContract
scopeMainDefaultContract =
  aristotle-constraint-contract
    "RequestProject.Qualifiers"
    "Wikidata.mainAllowed"
    "a property with no declared scope is allowed in the main slot"

scopeQualifierDefaultContract : AristotleConstraintContract
scopeQualifierDefaultContract =
  aristotle-constraint-contract
    "RequestProject.Qualifiers"
    "Wikidata.qualifierAllowed"
    "a property with no declared scope is allowed in the qualifier slot"

noSpecAssessment : ConstraintProfileCoverage → ConstraintAssessment
noSpecAssessment profileComplete = constraintUnconstrained
noSpecAssessment profileIncomplete = constraintUninspected
noSpecAssessment profileUninspected = constraintUninspected
noSpecAssessment profileInvalid = constraintUninspected

completeProfileAbsenceIsUnconstrained :
  noSpecAssessment profileComplete ≡ constraintUnconstrained
completeProfileAbsenceIsUnconstrained = refl

uninspectedProfileAbsenceRemainsUninspected :
  noSpecAssessment profileUninspected ≡ constraintUninspected
uninspectedProfileAbsenceRemainsUninspected = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MissingFromUninspectedTableImpliesUnconstrained : Set where
data UnconstrainedMeansPropertySemanticallyCorrect : Set where
data ConstraintTableCreatesMigrationAuthority : Set where

missingFromUninspectedTableDoesNotMeanUnconstrained :
  MissingFromUninspectedTableImpliesUnconstrained → ⊥
missingFromUninspectedTableDoesNotMeanUnconstrained ()

unconstrainedDoesNotMeanSemanticallyCorrect :
  UnconstrainedMeansPropertySemanticallyCorrect → ⊥
unconstrainedDoesNotMeanSemanticallyCorrect ()

constraintTableDoesNotCreateMigrationAuthority :
  ConstraintTableCreatesMigrationAuthority → ⊥
constraintTableDoesNotCreateMigrationAuthority ()

record ConstraintTableCoverageBoundary : Set where
  constructor constraint-table-coverage-boundary
  field
    completeAbsentProfileMayBeUnconstrained : Bool
    uninspectedAbsentProfileIsUnconstrained : Bool
    unconstrainedEqualsSemanticallyCorrect : Bool
    tableCreatesMigrationAuthority : Bool

canonicalConstraintTableCoverageBoundary : ConstraintTableCoverageBoundary
canonicalConstraintTableCoverageBoundary =
  constraint-table-coverage-boundary true false false false

constraintTableCoverageStatement : String
constraintTableCoverageStatement =
  "Qualifier/scope profile absence is interpreted as unconstrained only relative to a covered profile table. If the table is incomplete or uninspected, absence remains uninspected. Unconstrained means the configured executable table does not reject the property; it does not establish semantic correctness or migration authority."
