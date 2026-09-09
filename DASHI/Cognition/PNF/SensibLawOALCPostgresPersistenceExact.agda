module DASHI.Cognition.PNF.SensibLawOALCPostgresPersistenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact as OALC
import DASHI.Cognition.PNF.SensibLawOALCNativeShardResolutionExact as Native

------------------------------------------------------------------------
-- OALC / LEGALFOLLOW POSTGRES PERSISTENCE
--
-- Runtime parity target: SensibLaw PostgreSQL migration 181.
--
-- Canonical text remains owned by the existing generic corpus.document carrier.
-- This layer retains only provider/dataset/version identity, exact acquisition
-- receipt, and source-preserving section-span linkage.  Existing parser/PNF
-- owners remain downstream.
------------------------------------------------------------------------

record PostgresCanonicalDocumentRef : Set where
  constructor postgres-canonical-document-ref
  field
    documentRef : String
    canonicalContentDigestRef : String
    canonicalisationRef : String

open PostgresCanonicalDocumentRef public

record PersistedExternalSourceRevision
    (dataset : OALC.OALCDatasetSelection)
    (demand : OALC.OALCLegislationSourceDemand) : Set where
  constructor persisted-external-source-revision
  field
    externalSourceRevisionRef : String
    document : PostgresCanonicalDocumentRef
    providerRef : String
    datasetRef : String
    datasetRevisionRef : String
    externalVersionRef : String
    citationRef : String
    sourceRef : String
    jurisdictionRef : String
    documentTypeRef : String
    temporalCoverage : OALC.OALCTemporalCoverage
    resolutionPath : Native.NativeOALCResolutionPath
    sourceURLRef : String
    receiptDigestRef : String

open PersistedExternalSourceRevision public

record PersistedExternalSourceResolution
    {dataset : OALC.OALCDatasetSelection}
    {demand : OALC.OALCLegislationSourceDemand}
    (revision : PersistedExternalSourceRevision dataset demand) : Set where
  constructor persisted-external-source-resolution
  field
    sourceResolutionRef : String
    legalFollowDemandRef : String
    consumerRef : String
    requestedCitationRef : String
    requestedJurisdictionRef : String
    requestedSourceRoleRef : String
    requestedAuthorityLevelRef : String
    requestedTemporalRef : String
    exactDemandMatch : Bool
    acquisitionAuthorityRef : String
    receiptAuthorityRef : String
    networkRequestCount : Nat
    resolverRef : String
    resolutionEvidenceRef : String
    receiptDigestRef : String

open PersistedExternalSourceResolution public

record PostgresCanonicalSpanRef
    (document : PostgresCanonicalDocumentRef) : Set where
  constructor postgres-canonical-span-ref
  field
    spanRef : String
    startChar : Nat
    endChar : Nat
    spanTypeRef : String
    endAfterStartEvidenceRef : String

open PostgresCanonicalSpanRef public

record PersistedExternalSourceSlice
    {dataset : OALC.OALCDatasetSelection}
    {demand : OALC.OALCLegislationSourceDemand}
    (revision : PersistedExternalSourceRevision dataset demand) : Set where
  constructor persisted-external-source-slice
  field
    sourceSliceRef : String
    span : PostgresCanonicalSpanRef (document revision)
    locatorRef : String
    projectionRef : String
    sliceDigestRef : String
    parserAuthorityRef : String
    receiptDigestRef : String

open PersistedExternalSourceSlice public

------------------------------------------------------------------------
-- Runtime ownership boundary.
------------------------------------------------------------------------

data PostgresDuplicatesCanonicalText : Set where
data PostgresPersistenceCreatesLegalAuthority : Set where
data PostgresPersistenceCreatesHistoricalEquivalence : Set where
data PostgresPersistenceCreatesAtomicGate : Set where
data PersistedSliceCreatesPNFMeaning : Set where
data ResolutionPathCreatesAuthority : Set where
data SourceResidualMayBeStoredAsNegativeEvidence : Set where

postgresDoesNotDuplicateCanonicalText : PostgresDuplicatesCanonicalText → ⊥
postgresDoesNotDuplicateCanonicalText ()

postgresPersistenceDoesNotCreateLegalAuthority :
  PostgresPersistenceCreatesLegalAuthority → ⊥
postgresPersistenceDoesNotCreateLegalAuthority ()

postgresPersistenceDoesNotCreateHistoricalEquivalence :
  PostgresPersistenceCreatesHistoricalEquivalence → ⊥
postgresPersistenceDoesNotCreateHistoricalEquivalence ()

postgresPersistenceDoesNotCreateAtomicGate :
  PostgresPersistenceCreatesAtomicGate → ⊥
postgresPersistenceDoesNotCreateAtomicGate ()

persistedSliceDoesNotCreatePNFMeaning : PersistedSliceCreatesPNFMeaning → ⊥
persistedSliceDoesNotCreatePNFMeaning ()

resolutionPathDoesNotCreateAuthority : ResolutionPathCreatesAuthority → ⊥
resolutionPathDoesNotCreateAuthority ()

sourceResidualCannotBeStoredAsNegativeEvidence :
  SourceResidualMayBeStoredAsNegativeEvidence → ⊥
sourceResidualCannotBeStoredAsNegativeEvidence ()

record OALCPostgresPersistenceBoundary : Set where
  constructor oalc-postgres-persistence-boundary
  field
    existingCanonicalDocumentReused : Bool
    existingCanonicalSpanReused : Bool
    providerRevisionIdentityPersisted : Bool
    exactDemandReceiptPersisted : Bool
    sourceSliceWeldPersisted : Bool
    canonicalTextDuplicated : Bool
    persistenceCreatesAuthority : Bool
    persistenceCreatesHistoricalEquivalence : Bool
    persistenceCreatesAtomicGate : Bool

canonicalOALCPostgresPersistenceBoundary : OALCPostgresPersistenceBoundary
canonicalOALCPostgresPersistenceBoundary =
  oalc-postgres-persistence-boundary
    true true true true true false false false false
