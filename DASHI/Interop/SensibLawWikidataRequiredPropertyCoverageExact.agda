module DASHI.Interop.SensibLawWikidataRequiredPropertyCoverageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph

record RequiredPropertyFamily : Set where
  constructor required-property-family
  field
    subjectQidReference : String
    propertyReference : String
    graphRevisionReference : String
    coveragePolicyReference : String
    coverageStatus : Zelph.QueryCoverageStatus
open RequiredPropertyFamily public

-- This is statement-family presence, not native Wikibase snak semantics.
data PropertyStatementPresence : Set where
  statementPresent noStatementObserved statementPresenceUnresolved : PropertyStatementPresence

presenceFromCoverageAndRows :
  Zelph.QueryCoverageStatus → Bool → PropertyStatementPresence
presenceFromCoverageAndRows Zelph.queryCoverageComplete true = statementPresent
presenceFromCoverageAndRows Zelph.queryCoverageComplete false = noStatementObserved
presenceFromCoverageAndRows Zelph.queryCoverageIncomplete _ = statementPresenceUnresolved
presenceFromCoverageAndRows Zelph.queryCoverageUninspected _ = statementPresenceUnresolved
presenceFromCoverageAndRows Zelph.queryCoverageInvalid _ = statementPresenceUnresolved

observedMissingRowIsNoStatementObserved :
  presenceFromCoverageAndRows Zelph.queryCoverageComplete false ≡ noStatementObserved
observedMissingRowIsNoStatementObserved = refl

incompleteMissingRowIsUnresolved :
  presenceFromCoverageAndRows Zelph.queryCoverageIncomplete false ≡ statementPresenceUnresolved
incompleteMissingRowIsUnresolved = refl

uninspectedMissingRowIsUnresolved :
  presenceFromCoverageAndRows Zelph.queryCoverageUninspected false ≡ statementPresenceUnresolved
uninspectedMissingRowIsUnresolved = refl

record RequiredPropertyInventory : Set where
  constructor required-property-inventory
  field
    subjectQidReference : String
    graphRevisionReference : String
    coveragePolicyReference : String
    requiredPropertyReferences : List String
    observedWithStatementReferences : List String
    noStatementObservedPropertyReferences : List String
    unresolvedRequiredPropertyReferences : List String
open RequiredPropertyInventory public

data RankVisibilityDecision : Set where
  rankVisibilityDecidable rankVisibilityUnresolved : RankVisibilityDecision

rankVisibilityDecisionForCoverage : Zelph.QueryCoverageStatus → RankVisibilityDecision
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

data NoReturnedP14143ImpliesNativeNoValue : Set where
data ItemWideCoverageImpliesEveryRequiredFamilyCovered : Set where
data NoStatementObservedImpliesMigrationSafe : Set where

noReturnedRowDoesNotCreateNativeNoValue :
  NoReturnedP14143ImpliesNativeNoValue → ⊥
noReturnedRowDoesNotCreateNativeNoValue ()

itemWideCoverageDoesNotReplaceFamilyCoverage :
  ItemWideCoverageImpliesEveryRequiredFamilyCovered → ⊥
itemWideCoverageDoesNotReplaceFamilyCoverage ()

noStatementObservedDoesNotProveMigrationSafety :
  NoStatementObservedImpliesMigrationSafe → ⊥
noStatementObservedDoesNotProveMigrationSafety ()

record RequiredPropertyCoverageBoundary : Set where
  constructor required-property-coverage-boundary
  field
    statementPresenceRequiresPropertyFamilyCoverage : Bool
    incompleteFamilyBlocksTruthyDecision : Bool
    uninspectedFamilyBlocksTruthyDecision : Bool
    observedMissingRowMayCountAsNoStatementObserved : Bool
    observedMissingRowCountsAsNativeNoValue : Bool
    incompleteMissingRowCountsAsNoStatementObserved : Bool
    uninspectedMissingRowCountsAsNoStatementObserved : Bool
    noStatementObservedCreatesMigrationSafety : Bool

canonicalRequiredPropertyCoverageBoundary : RequiredPropertyCoverageBoundary
canonicalRequiredPropertyCoverageBoundary =
  required-property-coverage-boundary true true true true false false false false

requiredPropertyCoverageStatement : String
requiredPropertyCoverageStatement =
  "For a revision-bound Wikidata item Q, statement-family presence and rank truthiness are decided per required property family Q/P. Only policy-relative complete Q/P coverage can turn a missing returned row into noStatementObserved or make rank visibility decidable. noStatementObserved is not a native novalue snak. Incomplete, uninspected or invalid Q/P coverage remains unresolved and creates no migration authority."
