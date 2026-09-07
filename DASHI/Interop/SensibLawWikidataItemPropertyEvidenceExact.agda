module DASHI.Interop.SensibLawWikidataItemPropertyEvidenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Interop.AristotleRankQualifierPropertyEngineBoundary as Aristotle
import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph

------------------------------------------------------------------------
-- Runtime parity owner for SensibLaw src/policy/item_property_evidence.py.
--
-- The observed object is hierarchical:
--   item -> property family -> statement -> value/rank/qualifiers/references.
-- Peer coordinates are conditioned projections of that carrier, not detached
-- labels such as "company" or "ghg_protocol".
--
-- Crucially, rank truthiness is property-family relative.  A partial P-family
-- cannot decide whether a normal statement is truthy because an unseen
-- preferred sibling could suppress it.
------------------------------------------------------------------------

data StatementRank : Set where
  preferredRank normalRank deprecatedRank : StatementRank

data StatementVisibility : Set where
  truthyVisibility nonTruthyVisibility unresolvedVisibility : StatementVisibility

data ConstraintState : Set where
  validConstraint invalidConstraint uninspectedConstraint : ConstraintState

data PropertySlot : Set where
  mainSlot qualifierSlot : PropertySlot

data RelationOrigin : Set where
  assertedRelation derivedRelation unresolvedRelation : RelationOrigin

data ConditionedFeatureKind : Set where
  propertyFamilyCoverageFeature
  statementRankFeature
  statementVisibilityFeature
  qualifierConstraintFeature
  propertyScopeFeature
  propertyRelationFeature
  : ConditionedFeatureKind

record PropertyFamilyCoverage : Set where
  constructor property-family-coverage
  field
    coveredPropertyReference : String
    familyCoverageStatus : Zelph.QueryCoverageStatus
open PropertyFamilyCoverage public

record QualifierObservation : Set where
  constructor qualifier-observation
  field
    qualifierPropertyReference : String
    qualifierValueReference : String
    qualifierScopeState : ConstraintState
open QualifierObservation public

record StatementEvidence : Set where
  constructor statement-evidence
  field
    subjectQidReference : String
    propertyReference : String
    statementReference : String
    valueReference : String
    propertyCoverage : Zelph.QueryCoverageStatus
    rank : StatementRank
    visibility : StatementVisibility
    qualifierConstraint : ConstraintState
    mainPropertyScope : ConstraintState
    qualifiers : List QualifierObservation
    relationOrigin : RelationOrigin
    referenceSurfaceReference : String
open StatementEvidence public

record PropertyInventory : Set where
  constructor property-inventory
  field
    observedPropertyReferences : List String
    truthyPropertyReferences : List String
    coverageByProperty : List PropertyFamilyCoverage
    statementCountReference : String
open PropertyInventory public

record ConditionedPeerFeature : Set where
  constructor conditioned-peer-feature
  field
    featureKind : ConditionedFeatureKind
    conditionReference : String
    featureValueReference : String
open ConditionedPeerFeature public

record ItemPropertyEvidenceSurface : Set where
  constructor item-property-evidence-surface
  field
    subjectQid : String
    sourceRevisionReference : String
    graphCoverage : Zelph.QueryCoverageReceipt
    inventory : PropertyInventory
    statements : List StatementEvidence
    peerFeatures : List ConditionedPeerFeature
    evidenceReference : String
    authorityIsDiagnosticOnly : Bool
    authorityIsDiagnosticOnlyIsTrue : authorityIsDiagnosticOnly ≡ true
    promotionEvaluated : Bool
    promotionEvaluatedIsFalse : promotionEvaluated ≡ false
    editEffect : Bool
    editEffectIsFalse : editEffect ≡ false
open ItemPropertyEvidenceSurface public

------------------------------------------------------------------------
-- Aristotle parity.
------------------------------------------------------------------------

rankSourceContract : Aristotle.AristotleExecutableContract
rankSourceContract = Aristotle.truthyItemStatementContract

deprecatedSourceContract : Aristotle.AristotleExecutableContract
deprecatedSourceContract = Aristotle.deprecatedExcludedContract

qualifierSourceContract : Aristotle.AristotleExecutableContract
qualifierSourceContract = Aristotle.qualifierClaimContract

scopeSourceContract : Aristotle.AristotleExecutableContract
scopeSourceContract = Aristotle.propertyScopeContract

relationSoundnessSourceContract : Aristotle.AristotleExecutableContract
relationSoundnessSourceContract = Aristotle.propertyDerivabilitySoundnessContract

record RankVisibilityCoordinate : Set where
  constructor rank-visibility-coordinate
  field
    coordinateRank : StatementRank
    coordinateVisibility : StatementVisibility
open RankVisibilityCoordinate public

normalTruthyCoordinate : RankVisibilityCoordinate
normalTruthyCoordinate = rank-visibility-coordinate normalRank truthyVisibility

normalNonTruthyCoordinate : RankVisibilityCoordinate
normalNonTruthyCoordinate = rank-visibility-coordinate normalRank nonTruthyVisibility

visibilityForFamilyCoverage :
  Zelph.QueryCoverageStatus →
  StatementVisibility →
  StatementVisibility
visibilityForFamilyCoverage Zelph.queryCoverageComplete visibility = visibility
visibilityForFamilyCoverage Zelph.queryCoverageIncomplete visibility = unresolvedVisibility
visibilityForFamilyCoverage Zelph.queryCoverageInvalid visibility = unresolvedVisibility

incompleteFamilyCoverageMakesVisibilityUnresolved :
  (visibility : StatementVisibility) →
  visibilityForFamilyCoverage Zelph.queryCoverageIncomplete visibility ≡ unresolvedVisibility
incompleteFamilyCoverageMakesVisibilityUnresolved visibility = refl

invalidFamilyCoverageMakesVisibilityUnresolved :
  (visibility : StatementVisibility) →
  visibilityForFamilyCoverage Zelph.queryCoverageInvalid visibility ≡ unresolvedVisibility
invalidFamilyCoverageMakesVisibilityUnresolved visibility = refl

------------------------------------------------------------------------
-- Condition references retain the actual Wikidata location of each feature.
-- Examples at runtime include:
--   property_family_coverage | P5991
--   statement_rank            | P5991|<GUID>
--   statement_visibility      | P5991|<GUID>
--   property_scope            | P459:qualifier
--   property_relation         | P31->Q783794
------------------------------------------------------------------------

data SameSerializedValueImpliesSameEvidenceSurface : Set where
data SameRankForcesSameVisibility : Set where
data IncompleteFamilyCoverageCanAssertTruthyVisibility : Set where
data ItemPropertyPresenceImpliesLocalRole : Set where
data DerivedRelationIsDirectAssertion : Set where
data TruthyStatementImpliesMigrationSafe : Set where
data ItemSurfaceCreatesEditAuthority : Set where

sameSerializedValueDoesNotCollapseEvidence :
  SameSerializedValueImpliesSameEvidenceSurface → ⊥
sameSerializedValueDoesNotCollapseEvidence ()

sameRankDoesNotForceSameVisibility :
  SameRankForcesSameVisibility → ⊥
sameRankDoesNotForceSameVisibility ()

incompleteFamilyCoverageCannotAssertTruthyVisibility :
  IncompleteFamilyCoverageCanAssertTruthyVisibility → ⊥
incompleteFamilyCoverageCannotAssertTruthyVisibility ()

itemPropertyPresenceDoesNotCreateLocalRole :
  ItemPropertyPresenceImpliesLocalRole → ⊥
itemPropertyPresenceDoesNotCreateLocalRole ()

derivedRelationDoesNotBecomeDirectAssertion :
  DerivedRelationIsDirectAssertion → ⊥
derivedRelationDoesNotBecomeDirectAssertion ()

truthyStatementDoesNotProveMigrationSafety :
  TruthyStatementImpliesMigrationSafe → ⊥
truthyStatementDoesNotProveMigrationSafety ()

itemSurfaceDoesNotCreateEditAuthority :
  ItemSurfaceCreatesEditAuthority → ⊥
itemSurfaceDoesNotCreateEditAuthority ()

record ItemPropertyEvidenceBoundary : Set where
  constructor item-property-evidence-boundary
  field
    itemOwnsObservedPropertyInventory : Bool
    propertyFamilyCoverageIsFirstClass : Bool
    statementsRemainPropertyAndGuidConditioned : Bool
    rankAndVisibilityRemainSeparate : Bool
    incompleteFamilyLeavesVisibilityUnresolved : Bool
    qualifierAndScopeReceiptsRemainSeparate : Bool
    assertedAndDerivedRelationsRemainSeparate : Bool
    equalSerializedValuesCollapseEvidence : Bool
    itemPropertiesCreateLocalRole : Bool
    itemSurfaceCreatesPromotion : Bool
    itemSurfaceCreatesEdit : Bool

canonicalItemPropertyEvidenceBoundary : ItemPropertyEvidenceBoundary
canonicalItemPropertyEvidenceBoundary =
  item-property-evidence-boundary
    true true true true true true true false false false false

itemPropertyEvidenceStatement : String
itemPropertyEvidenceStatement =
  "SensibLaw peer evidence is projected from the revision-bound Wikidata item itself. Property inventory and per-property-family coverage are first-class; statement GUIDs, values, ranks, computed truthy visibility, qualifiers, property-slot constraints, references, and asserted/derived relation origin remain distinct conditioned coordinates. Incomplete property-family coverage leaves rank visibility unresolved, because an unseen preferred sibling may exist. Equal-looking climate rows therefore need not collapse. The carrier is diagnostic only and creates no local role, migration safety, promotion, or edit authority."
