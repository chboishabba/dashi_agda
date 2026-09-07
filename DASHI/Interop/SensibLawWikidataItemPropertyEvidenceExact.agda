module DASHI.Interop.SensibLawWikidataItemPropertyEvidenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.AristotleRankQualifierPropertyEngineBoundary as Aristotle
import DASHI.Interop.AristotleSnakStatementPresenceBoundaryExact as Snaks
import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph
import DASHI.Interop.SensibLawWikidataRequiredPropertyCoverageExact as Required

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
  propertyStatementPresenceFeature
  statementSnakTypeFeature
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
    nativeSnakType : Snaks.NativeSnakType
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
    requiredPropertyReferences : List String
    observedPropertyReferences : List String
    truthyPropertyReferences : List String
    noStatementObservedPropertyReferences : List String
    unresolvedRequiredPropertyReferences : List String
    explicitNoValuePropertyReferences : List String
    explicitSomeValuePropertyReferences : List String
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

novalueSourceContract : Snaks.AristotleSnakContract
novalueSourceContract = Snaks.novalueEntailmentContract

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
  Zelph.QueryCoverageStatus → StatementVisibility → StatementVisibility
visibilityForFamilyCoverage Zelph.queryCoverageComplete visibility = visibility
visibilityForFamilyCoverage Zelph.queryCoverageIncomplete _ = unresolvedVisibility
visibilityForFamilyCoverage Zelph.queryCoverageUninspected _ = unresolvedVisibility
visibilityForFamilyCoverage Zelph.queryCoverageInvalid _ = unresolvedVisibility

incompleteFamilyCoverageMakesVisibilityUnresolved :
  (visibility : StatementVisibility) →
  visibilityForFamilyCoverage Zelph.queryCoverageIncomplete visibility ≡ unresolvedVisibility
incompleteFamilyCoverageMakesVisibilityUnresolved visibility = refl

uninspectedFamilyCoverageMakesVisibilityUnresolved :
  (visibility : StatementVisibility) →
  visibilityForFamilyCoverage Zelph.queryCoverageUninspected visibility ≡ unresolvedVisibility
uninspectedFamilyCoverageMakesVisibilityUnresolved visibility = refl

propertyStatementPresenceOwner :
  Zelph.QueryCoverageStatus → Bool → Required.PropertyStatementPresence
propertyStatementPresenceOwner = Required.presenceFromCoverageAndRows

observedMissingRequiredPropertyHasNoStatementObserved :
  propertyStatementPresenceOwner Zelph.queryCoverageComplete false ≡ Required.noStatementObserved
observedMissingRequiredPropertyHasNoStatementObserved = refl

uninspectedMissingRequiredPropertyIsUnresolved :
  propertyStatementPresenceOwner Zelph.queryCoverageUninspected false ≡ Required.statementPresenceUnresolved
uninspectedMissingRequiredPropertyIsUnresolved = refl

data SameSerializedValueImpliesSameEvidenceSurface : Set where
data SameRankForcesSameVisibility : Set where
data IncompleteFamilyCoverageCanAssertTruthyVisibility : Set where
data UninspectedFamilyCoverageCanAssertNoStatementObserved : Set where
data NoStatementObservedIsNativeNoValue : Set where
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

uninspectedFamilyCannotAssertNoStatementObserved :
  UninspectedFamilyCoverageCanAssertNoStatementObserved → ⊥
uninspectedFamilyCannotAssertNoStatementObserved ()

noStatementObservedDoesNotBecomeNativeNoValue :
  NoStatementObservedIsNativeNoValue → ⊥
noStatementObservedDoesNotBecomeNativeNoValue ()

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
    requiredPropertyFamiliesAreFirstClass : Bool
    propertyFamilyCoverageIsFirstClass : Bool
    statementPresenceRequiresFamilyCoverage : Bool
    nativeSnakAndStatementPresenceRemainSeparate : Bool
    statementsRemainPropertyAndGuidConditioned : Bool
    rankAndVisibilityRemainSeparate : Bool
    incompleteFamilyLeavesVisibilityUnresolved : Bool
    uninspectedFamilyLeavesVisibilityUnresolved : Bool
    qualifierAndScopeReceiptsRemainSeparate : Bool
    assertedAndDerivedRelationsRemainSeparate : Bool
    equalSerializedValuesCollapseEvidence : Bool
    itemPropertiesCreateLocalRole : Bool
    itemSurfaceCreatesPromotion : Bool
    itemSurfaceCreatesEdit : Bool

canonicalItemPropertyEvidenceBoundary : ItemPropertyEvidenceBoundary
canonicalItemPropertyEvidenceBoundary =
  item-property-evidence-boundary
    true true true true true true true true true true true false false false false

itemPropertyEvidenceStatement : String
itemPropertyEvidenceStatement =
  "SensibLaw peer evidence is projected from the revision-bound Wikidata item itself. Required property families, per-family coverage, statement-family presence, native snak type, statement GUIDs, ranks, computed truthy visibility, qualifiers, property-slot constraints, references, and asserted/derived relation origin remain distinct conditioned coordinates. Only complete Q/P coverage can establish noStatementObserved or rank visibility; noStatementObserved is not native novalue. The carrier is diagnostic only and creates no local role, migration safety, promotion, or edit authority."
