module DASHI.Interop.AristotleRankQualifierPropertyEngineBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Source-level contracts rechecked against the attached Aristotle archive.
------------------------------------------------------------------------

record AristotleExecutableContract : Set where
  constructor aristotle-executable-contract
  field
    sourceModule : String
    declaration : String
    contractReference : String
open AristotleExecutableContract public

truthyItemStatementContract : AristotleExecutableContract
truthyItemStatementContract =
  aristotle-executable-contract
    "RequestProject.Ranks"
    "Wikidata.Claim.mem_truthyItemStmts_iff"
    "truthy item-valued statements are exactly the item claims selected by Wikidata rank semantics"

deprecatedExcludedContract : AristotleExecutableContract
deprecatedExcludedContract =
  aristotle-executable-contract
    "RequestProject.Ranks"
    "Wikidata.Claim.not_mem_truthy_of_deprecated"
    "deprecated claims never enter the truthy fragment"

qualifierClaimContract : AristotleExecutableContract
qualifierClaimContract =
  aristotle-executable-contract
    "RequestProject.Qualifiers"
    "Wikidata.QualSpec.claimOk_iff"
    "claim qualifier validity is characterised exactly by the executable allowed and mandatory qualifier checks"

qualifierSetContract : AristotleExecutableContract
qualifierSetContract =
  aristotle-executable-contract
    "RequestProject.Qualifiers"
    "Wikidata.qualSetOk_iff"
    "whole claim-set qualifier validity is characterised exactly by the configured qualifier profile table"

propertyScopeContract : AristotleExecutableContract
propertyScopeContract =
  aristotle-executable-contract
    "RequestProject.Qualifiers"
    "Wikidata.scopeOk_iff"
    "property main-value versus qualifier-slot scope is checked executablely and characterised exactly"

propertyDerivabilitySoundnessContract : AristotleExecutableContract
propertyDerivabilitySoundnessContract =
  aristotle-executable-contract
    "RequestProject.PropertyEngine"
    "Wikidata.PKB.holds_of_relatedB"
    "every relation computed by the property engine is derivable in its abstract property model"

propertyDerivabilityCompletenessContract : AristotleExecutableContract
propertyDerivabilityCompletenessContract =
  aristotle-executable-contract
    "RequestProject.PropertyEngine"
    "Wikidata.PKB.relatedB_of_holds"
    "under the module's stated restrictions, abstract property-layer derivability is recovered by the executable relation"

------------------------------------------------------------------------
-- Nat must not collapse these different executable receipts.
------------------------------------------------------------------------

data TruthyMeansSourceTrue : Set where
data QualifierValidMeansMigrationSafe : Set where
data PKBDerivableMeansCanonicalFact : Set where
data TruthyItemStatementRetainsWholeNativeStatement : Set where
data PropertyConstraintValidityCreatesEditAuthority : Set where

truthyDoesNotCreateSourceTruth : TruthyMeansSourceTrue → ⊥
truthyDoesNotCreateSourceTruth ()

qualifierValidityDoesNotCreateMigrationSafety : QualifierValidMeansMigrationSafe → ⊥
qualifierValidityDoesNotCreateMigrationSafety ()

pkbDerivabilityDoesNotCreateCanonicalFact : PKBDerivableMeansCanonicalFact → ⊥
pkbDerivabilityDoesNotCreateCanonicalFact ()

truthyProjectionDoesNotRetainWholeNativeStatement :
  TruthyItemStatementRetainsWholeNativeStatement → ⊥
truthyProjectionDoesNotRetainWholeNativeStatement ()

constraintValidityDoesNotCreateEditAuthority :
  PropertyConstraintValidityCreatesEditAuthority → ⊥
constraintValidityDoesNotCreateEditAuthority ()

record RankQualifierPropertyBoundary : Set where
  constructor rank-qualifier-property-boundary
  field
    rankFilteringIsSeparateReceipt : Bool
    qualifierConstraintCheckIsSeparateReceipt : Bool
    propertyDerivabilityIsSeparateReceipt : Bool
    truthyMeansSourceTruth : Bool
    qualifierValidityMeansMigrationSafe : Bool
    pkbDerivabilityMeansCanonicalFact : Bool
    constraintValidityCreatesEditAuthority : Bool

canonicalRankQualifierPropertyBoundary : RankQualifierPropertyBoundary
canonicalRankQualifierPropertyBoundary =
  rank-qualifier-property-boundary true true true false false false false

aristotleRankQualifierPropertyStatement : String
aristotleRankQualifierPropertyStatement =
  "Aristotle separates Wikidata rank truthiness, qualifier/scope validity, and executable property-layer derivability. SensibLaw may consume each as a distinct bounded receipt, but none is source truth, migration safety, canonical promotion, or edit authority."
