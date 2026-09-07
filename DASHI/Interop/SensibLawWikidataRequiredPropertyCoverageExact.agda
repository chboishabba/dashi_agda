module DASHI.Interop.SensibLawWikidataRequiredPropertyCoverageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph

------------------------------------------------------------------------
-- Runtime parity owner for SensibLaw item_property_evidence v0_2.
--
-- Meaningful property absence is indexed by QID, property, graph revision and
-- declared coverage policy.  No returned statement row for P is not enough.
------------------------------------------------------------------------

record RequiredPropertyFamily : Set where
  constructor required-property-family
  field
    subjectQidReference : String
    propertyReference : String
    graphRevisionReference : String
    coveragePolicyReference : String
    coverageStatus : Zelph.QueryCoverageStatus
open RequiredPropertyFamily public

data PropertyPresence : Set where
  propertyPresent propertyAbsent propertyPresenceUnresolved : PropertyPresence

presenceFromCoverageAndRows :
  Zelph.QueryCoverageStatus → Bool → PropertyPresence
presenceFromCoverageAndRows Zelph.queryCoverageComplete true = propertyPresent
presenceFromCoverageAndRows Zelph.queryCoverageComplete false = propertyAbsent
presenceFromCoverageAndRows Zelph.queryCoverageIncomplete _ = propertyPresenceUnresolved
presenceFromCoverageAndRows Zelph.queryCoverageUninspected _ = propertyPresenceUnresolved
presenceFromCoverageAndRows Zelph.queryCoverageInvalid _ = propertyPresenceUnresolved

observedMissingRowIsObservedAbsence :
  presenceFromCoverageAndRows Zelph.queryCoverageComplete false ≡ propertyAbsent
observedMissingRowIsObservedAbsence = refl

incompleteMissingRowIsNotAbsence :
  presenceFromCoverageAndRows Zelph.queryCoverageIncomplete false ≡ propertyPresenceUnresolved
incompleteMissingRowIsNotAbsence = refl

uninspectedMissingRowIsNotAbsence :
  presenceFromCoverageAndRows Zelph.queryCoverageUninspected false ≡ propertyPresenceUnresolved
uninspectedMissingRowIsNotAbsence = refl

record RequiredPropertyInventory : Set where
  constructor required-property-inventory
  field
    subjectQidReference : String
    graphRevisionReference : String
    coveragePolicyReference : String
    requiredPropertyReferences : List String
    observedWithStatementReferences : List String
    observedAbsentPropertyReferences : List String
    unresolvedRequiredPropertyReferences : List String
open RequiredPropertyInventory public

------------------------------------------------------------------------
-- Rank truthiness is also property-family coverage dependent.
------------------------------------------------------------------------

data RankVisibilityDecision : Set where
  rankVisibilityDecidable rankVisibilityUnresolved : RankVisibilityDecision

rankVisibilityDecisionForCoverage :
  Zelph.QueryCoverageStatus → RankVisibilityDecision
rankVisibilityDecisionForCoverage Zelph.queryCoverageComplete = rankVisibilityDecidable
rankVisibilityDecisionForCoverage Zelph.queryCoverageIncomplete = rankVisibilityUnresolved
rankVisibilityDecisionForCoverage Zelph.queryCoverageUninspected = rankVisibilityUnresolved
rankVisibilityDecisionForCoverage Zelph.queryCoverageInvalid = rankVisibilityUnresolved

incompleteFamilyBlocksRankVisibility :
  rankVisibilityDecisionForCoverage Zelph.queryCoverageIncomplete ≡ rankVisibilityUnresolved
incompleteFamilyBlocksRankVisibility = refl

uninspectedFamilyBlocksRankVisibility :
  rankVisibilityDecisionForCoverage Zelph.queryCoverageUninspected ≡ rankVisibilityUnresolved
uninspectedFamilyBlocksRankVisibility = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NoReturnedP14143ImpliesP14143Absent : Set where
data ItemWideCoverageImpliesEveryRequiredFamilyCovered : Set where
data ObservedPropertyAbsenceImpliesMigrationSafe : Set where

noReturnedRowDoesNotProvePropertyAbsence :
  NoReturnedP14143ImpliesP14143Absent → ⊥
noReturnedRowDoesNotProvePropertyAbsence ()

itemWideCoverageDoesNotReplaceFamilyCoverage :
  ItemWideCoverageImpliesEveryRequiredFamilyCovered → ⊥
itemWideCoverageDoesNotReplaceFamilyCoverage ()

observedAbsenceDoesNotProveMigrationSafety :
  ObservedPropertyAbsenceImpliesMigrationSafe → ⊥
observedAbsenceDoesNotProveMigrationSafety ()

record RequiredPropertyCoverageBoundary : Set where
  constructor required-property-coverage-boundary
  field
    absenceRequiresPropertyFamilyCoverage : Bool
    incompleteFamilyBlocksTruthyDecision : Bool
    uninspectedFamilyBlocksTruthyDecision : Bool
    observedMissingRowMayCountAsAbsence : Bool
    incompleteMissingRowCountsAsAbsence : Bool
    uninspectedMissingRowCountsAsAbsence : Bool
    observedAbsenceCreatesMigrationSafety : Bool

canonicalRequiredPropertyCoverageBoundary : RequiredPropertyCoverageBoundary
canonicalRequiredPropertyCoverageBoundary =
  required-property-coverage-boundary true true true true false false false

requiredPropertyCoverageStatement : String
requiredPropertyCoverageStatement =
  "For a revision-bound Wikidata item Q, property presence/absence and rank truthiness are decided per required property family Q/P. Only policy-relative complete coverage of Q/P can turn a missing returned row into observed property absence or make rank visibility decidable. Incomplete, uninspected or invalid Q/P coverage remains unresolved and creates no migration authority."
