module DASHI.Interop.SensibLawWikibaseZelphItemSurfaceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph
import DASHI.Interop.SensibLawWikidataItemPropertyEvidenceExact as ItemEvidence
import DASHI.Interop.AristotleSnakStatementPresenceBoundaryExact as Snaks
import DASHI.Interop.AristotleConservativeTypeModuleBoundaryExact as Modules

------------------------------------------------------------------------
-- Runtime parity owner for SensibLaw src/policy/wikibase_zelph_item_surface.py.
--
-- Two evidence planes are joined but not collapsed:
--
--   native revision-pinned Wikibase entity
--     owns GUID / snak / rank / qualifiers / references
--
--   bounded Zelph graph view
--     owns bounded adjacency / graph relation context / derived relations
--
-- A graph artifact revision and an entity lastrevid may be different identifier
-- systems.  When they differ, the join requires an explicit alignment receipt.
------------------------------------------------------------------------

record NativeWikibaseStatementPlane : Set where
  constructor native-wikibase-statement-plane
  field
    subjectQidReference : String
    entityRevisionReference : String
    statementBundleReference : String
    ownsStatementGuid : Bool
    ownsStatementGuidIsTrue : ownsStatementGuid ≡ true
    ownsNativeSnak : Bool
    ownsNativeSnakIsTrue : ownsNativeSnak ≡ true
    ownsRank : Bool
    ownsRankIsTrue : ownsRank ≡ true
    ownsQualifiers : Bool
    ownsQualifiersIsTrue : ownsQualifiers ≡ true
    ownsReferences : Bool
    ownsReferencesIsTrue : ownsReferences ≡ true
open NativeWikibaseStatementPlane public

record ZelphGraphContextPlane : Set where
  constructor zelph-graph-context-plane
  field
    graphView : Zelph.QueryCoverageReceipt
    graphRevisionReference : String
    boundedAdjacencyReference : String
    derivedRelationReference : String
    typeModule : Modules.TypeClosureModuleReceipt
    ownsNativeStatementBundle : Bool
    ownsNativeStatementBundleIsFalse : ownsNativeStatementBundle ≡ false
open ZelphGraphContextPlane public

record RevisionAlignmentReceipt : Set where
  constructor revision-alignment-receipt
  field
    entityRevisionReference : String
    graphRevisionReference : String
    alignmentReference : String
    revisionsAreDefinitionallyEqual : Bool
    revisionsAreDefinitionallyEqualIsFalse : revisionsAreDefinitionallyEqual ≡ false
open RevisionAlignmentReceipt public

record WikibaseZelphItemSurface : Set where
  constructor wikibase-zelph-item-surface
  field
    nativePlane : NativeWikibaseStatementPlane
    graphPlane : ZelphGraphContextPlane
    revisionAlignment : RevisionAlignmentReceipt
    itemSurface : ItemEvidence.ItemPropertyEvidenceSurface
    authorityIsDiagnosticOnly : Bool
    authorityIsDiagnosticOnlyIsTrue : authorityIsDiagnosticOnly ≡ true
    promotionEvaluated : Bool
    promotionEvaluatedIsFalse : promotionEvaluated ≡ false
    editEffect : Bool
    editEffectIsFalse : editEffect ≡ false
open WikibaseZelphItemSurface public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CompleteGraphViewImpliesNativePropertyFamilyComplete : Set where
data ZelphAdjacencyReconstructsNativeRank : Set where
data ZelphAdjacencyReconstructsNativeQualifiers : Set where
data ZelphAdjacencyReconstructsNativeReferences : Set where
data NativeEntityExportCreatesConservativeTypeClosure : Set where
data DifferentRevisionIdentifiersNeedNoAlignmentReceipt : Set where
data JoinedSurfaceCreatesMigrationAuthority : Set where

completeGraphDoesNotCertifyNativePropertyFamily :
  CompleteGraphViewImpliesNativePropertyFamilyComplete → ⊥
completeGraphDoesNotCertifyNativePropertyFamily ()

zelphAdjacencyDoesNotReconstructNativeRank :
  ZelphAdjacencyReconstructsNativeRank → ⊥
zelphAdjacencyDoesNotReconstructNativeRank ()

zelphAdjacencyDoesNotReconstructNativeQualifiers :
  ZelphAdjacencyReconstructsNativeQualifiers → ⊥
zelphAdjacencyDoesNotReconstructNativeQualifiers ()

zelphAdjacencyDoesNotReconstructNativeReferences :
  ZelphAdjacencyReconstructsNativeReferences → ⊥
zelphAdjacencyDoesNotReconstructNativeReferences ()

nativeEntityExportDoesNotCreateTypeClosure :
  NativeEntityExportCreatesConservativeTypeClosure → ⊥
nativeEntityExportDoesNotCreateTypeClosure ()

differentRevisionIdentifiersRequireAlignment :
  DifferentRevisionIdentifiersNeedNoAlignmentReceipt → ⊥
differentRevisionIdentifiersRequireAlignment ()

joinedSurfaceDoesNotCreateMigrationAuthority :
  JoinedSurfaceCreatesMigrationAuthority → ⊥
joinedSurfaceDoesNotCreateMigrationAuthority ()

record WikibaseZelphJoinBoundary : Set where
  constructor wikibase-zelph-join-boundary
  field
    nativeAndGraphPlanesRemainDistinct : Bool
    nativePlaneOwnsStatementBundleSemantics : Bool
    graphPlaneOwnsBoundedRelationContext : Bool
    graphCompletenessCertifiesNativeFamilyCoverage : Bool
    differentRevisionIdentifiersNeedAlignment : Bool
    joinedSurfaceCreatesPromotion : Bool
    joinedSurfaceCreatesEdit : Bool

canonicalWikibaseZelphJoinBoundary : WikibaseZelphJoinBoundary
canonicalWikibaseZelphJoinBoundary =
  wikibase-zelph-join-boundary true true true false true false false

wikibaseZelphJoinStatement : String
wikibaseZelphJoinStatement =
  "SensibLaw joins a revision-pinned native Wikibase statement plane with a bounded Zelph graph-context plane without collapsing their authority or information content. Native Wikibase owns GUID/snak/rank/qualifier/reference semantics; Zelph owns bounded adjacency and derived graph context. Complete graph coverage does not certify native Q/P statement-family completeness, different revision identifiers require an explicit alignment receipt, and the joined surface creates neither promotion nor edit authority."
