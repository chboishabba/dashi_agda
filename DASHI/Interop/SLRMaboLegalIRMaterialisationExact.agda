module DASHI.Interop.SLRMaboLegalIRMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- MABO LEGAL-IR MATERIALISATION PARITY
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-legal-ir-materializer
--
-- Legal semantic owner:
--   chboishabba/SensibLaw
--
-- The runtime persists an already-admitted typed LegalIR projection. It does
-- not infer legal applicability, proposition truth, or legal authority from
-- persistence. Historical JSONB LegalIR tables remain reference surfaces only;
-- production uses append-only binary/scalar v2 tables.
------------------------------------------------------------------------

slriWireVersion : Nat
slriWireVersion = 1

data LegalIrMaterialisationKind : Set where
  semanticBuild projection observation graphRevision : LegalIrMaterialisationKind

legalIrMaterialisationTag : LegalIrMaterialisationKind → Nat
legalIrMaterialisationTag semanticBuild = 1
legalIrMaterialisationTag projection = 2
legalIrMaterialisationTag observation = 3
legalIrMaterialisationTag graphRevision = 4

record SLRIWireParity : Set where
  constructor slriWireParity
  field
    magicIsSLRI : Bool
    versionIsOne : Bool
    littleEndianLengths : Bool
    semanticBuildTagIsOne : Bool
    projectionTagIsTwo : Bool
    observationTagIsThree : Bool
    graphRevisionTagIsFour : Bool
    fieldsAreLengthPrefixed : Bool
    observationBodyMagicIsOBS1 : Bool
    jsonTransportUsed : Bool
    regexSemanticParserUsed : Bool

open SLRIWireParity public

canonicalSLRIWireParity : SLRIWireParity
canonicalSLRIWireParity =
  slriWireParity
    true true true true true true true true true false false

record LegalIrV2StorageParity : Set where
  constructor legalIrV2StorageParity
  field
    semanticBuildV2Present : Bool
    projectionV2Present : Bool
    observationV2Present : Bool
    graphRevisionV2Present : Bool
    payloadUsesBytea : Bool
    provenanceUsesTypedReferenceArrays : Bool
    observationRoleQualifierWrapperStateUsesFixedBinaryBody : Bool
    jsonbUsedByProductionV2 : Bool
    appendOnlyConflictIgnore : Bool
    updateUsed : Bool
    deleteUsed : Bool
    persistenceCreatesSemanticAuthority : Bool
    persistenceCreatesLegalConclusion : Bool

open LegalIrV2StorageParity public

canonicalLegalIrV2StorageParity : LegalIrV2StorageParity
canonicalLegalIrV2StorageParity =
  legalIrV2StorageParity
    true true true true true true true false true false false false false

record ExactSourceWeldParity : Set where
  constructor exactSourceWeldParity
  field
    propositionSubjectRetained : Bool
    graphRevisionRetainsSourceSpanRefs : Bool
    semanticBuildRetainsSourceRevisionRef : Bool
    graphRevisionAndSemanticBuildMustShareBuildRef : Bool
    exactSpanMustBeMemberOfRevisionSourceSpans : Bool
    exactSourcePaymentMayBecomeTrue : Bool
    propositionTruthPaidByExactSourceWeld : Bool
    applicabilityPaidByExactSourceWeld : Bool

open ExactSourceWeldParity public

canonicalExactSourceWeldParity : ExactSourceWeldParity
canonicalExactSourceWeldParity =
  exactSourceWeldParity
    true true true true true true false false

------------------------------------------------------------------------
-- Mabo flagship coordinate anchors.
------------------------------------------------------------------------

record MaboRadicalTitleSourceAnchorParity : Set where
  constructor maboRadicalTitleSourceAnchorParity
  field
    subjectIsRadicalTitleNativeTitle : Bool
    revisionPinnedWikisourceManifestation : Bool
    brennanExactSpanRetained : Bool
    sourceManifestationDistinctFromAuthorityIdentity : Bool
    runnerConsumesAdmittedLegalIrRatherThanSeedingRows : Bool
    pythonLegalSemanticRuntimeUsed : Bool
    runnerClaimsPropositionTruth : Bool
    runnerClaimsApplicability : Bool

open MaboRadicalTitleSourceAnchorParity public

canonicalMaboRadicalTitleSourceAnchorParity : MaboRadicalTitleSourceAnchorParity
canonicalMaboRadicalTitleSourceAnchorParity =
  maboRadicalTitleSourceAnchorParity
    true true true true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data JsonLegalIrProductionTransport : Set where
data JsonbLegalIrProductionPayload : Set where
data RegexLegalIrSemanticParser : Set where
data PersistenceCreatesLegalAuthority : Set where
data ExactSourceWeldCreatesPropositionTruth : Set where
data ExactSourceWeldCreatesApplicability : Set where
data MaboSqlSeedCreatesProofGraph : Set where

jsonLegalIrProductionTransportForbidden : JsonLegalIrProductionTransport → ⊥
jsonLegalIrProductionTransportForbidden ()

jsonbLegalIrProductionPayloadForbidden : JsonbLegalIrProductionPayload → ⊥
jsonbLegalIrProductionPayloadForbidden ()

regexLegalIrSemanticParserForbidden : RegexLegalIrSemanticParser → ⊥
regexLegalIrSemanticParserForbidden ()

persistenceDoesNotCreateLegalAuthority : PersistenceCreatesLegalAuthority → ⊥
persistenceDoesNotCreateLegalAuthority ()

exactSourceWeldDoesNotCreatePropositionTruth : ExactSourceWeldCreatesPropositionTruth → ⊥
exactSourceWeldDoesNotCreatePropositionTruth ()

exactSourceWeldDoesNotCreateApplicability : ExactSourceWeldCreatesApplicability → ⊥
exactSourceWeldDoesNotCreateApplicability ()

maboSqlSeedProofGraphForbidden : MaboSqlSeedCreatesProofGraph → ⊥
maboSqlSeedProofGraphForbidden ()
