module DASHI.Interop.MaboRadicalTitleLegalIRMaterialisationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.MaboRadicalTitleExactSourcePaymentExact as Exact
import DASHI.Interop.MaboRadicalTitlePropositionChainPaymentExact as Chain

------------------------------------------------------------------------
-- P3a: LEGAL-IR MATERIALISATION IS A SUPPORT-COORDINATE PRODUCER
--
-- Runtime counterpart:
--   slr/crates/sl-pg-source-store/src/legal_ir_materialization.rs
--
-- The persistence layer does not derive semantic support from judgment text.
-- It receives a reviewed PNF factor/revision and retains the exact paid source
-- span independently on the observation and graph-revision sides. Only that
-- conjunction may be projected into Chain.PropositionRoleCoordinate.
------------------------------------------------------------------------

and : Bool → Bool → Bool
and false _ = false
and true b = b

record LegalIRMaterialisationReceipt : Set where
  constructor legalIRMaterialisationReceipt
  field
    semanticBuildPersisted : Bool
    projectionPersisted : Bool
    observationPersisted : Bool
    graphRevisionPersisted : Bool
    pnfRevisionPresent : Bool
    observationProvenanceHasExactSpan : Bool
    graphRevisionHasExactSpan : Bool
    applicabilityPaid : Bool
    claimTruthPaid : Bool

open LegalIRMaterialisationReceipt public

observationRowPresent : LegalIRMaterialisationReceipt → Bool
observationRowPresent r =
  and (semanticBuildPersisted r)
    (and (projectionPersisted r) (observationPersisted r))

materialisedSupportCoordinate :
  LegalIRMaterialisationReceipt → Chain.PropositionRoleCoordinate
materialisedSupportCoordinate r =
  Chain.propositionRoleCoordinate
    (observationRowPresent r)
    (pnfRevisionPresent r)
    (observationProvenanceHasExactSpan r)
    (and (graphRevisionPersisted r) (graphRevisionHasExactSpan r))
    false

canonicalMaterialisation : LegalIRMaterialisationReceipt
canonicalMaterialisation =
  legalIRMaterialisationReceipt
    true true true true
    true true true
    false false

rowsWithoutPNFRevision : LegalIRMaterialisationReceipt
rowsWithoutPNFRevision =
  legalIRMaterialisationReceipt
    true true true true
    false true true
    false false

rowsWithoutObservationSpan : LegalIRMaterialisationReceipt
rowsWithoutObservationSpan =
  legalIRMaterialisationReceipt
    true true true true
    true false true
    false false

rowsWithoutGraphSpan : LegalIRMaterialisationReceipt
rowsWithoutGraphSpan =
  legalIRMaterialisationReceipt
    true true true true
    true true false
    false false

canonicalSupport : Chain.PropositionRoleCoordinate
canonicalSupport = materialisedSupportCoordinate canonicalMaterialisation

canonicalSupportPays : Chain.observationPaid canonicalSupport ≡ true
canonicalSupportPays = refl

pnfRevisionIsRequired :
  Chain.observationPaid (materialisedSupportCoordinate rowsWithoutPNFRevision)
    ≡ false
pnfRevisionIsRequired = refl

observationExactSpanIsRequired :
  Chain.observationPaid (materialisedSupportCoordinate rowsWithoutObservationSpan)
    ≡ false
observationExactSpanIsRequired = refl

graphExactSpanIsRequired :
  Chain.observationPaid (materialisedSupportCoordinate rowsWithoutGraphSpan)
    ≡ false
graphExactSpanIsRequired = refl

canonicalMaterialisedBoundedWhy : Chain.RadicalTitlePropositionPayment
canonicalMaterialisedBoundedWhy =
  Chain.radicalTitlePropositionPayment
    "mabo:proposition:radical-title-native-title"
    Exact.canonicalPaidSpan
    canonicalSupport
    Chain.explicitResidual
    Chain.explicitResidual
    Chain.explicitResidual
    false
    false

materialisedRowsPayBoundedWhy :
  Chain.propositionChainPaid canonicalMaterialisedBoundedWhy ≡ true
materialisedRowsPayBoundedWhy = refl

materialisedRowsExecuteWhy :
  Chain.whyDisposition canonicalMaterialisedBoundedWhy ≡ Chain.executeBoundedWhy
materialisedRowsExecuteWhy = refl

materialisedRowsDoNotPayApplicability :
  Chain.applicabilityPaid canonicalMaterialisedBoundedWhy ≡ false
materialisedRowsDoNotPayApplicability = refl

materialisedRowsDoNotPayTruth :
  Chain.claimTruthPaid canonicalMaterialisedBoundedWhy ≡ false
materialisedRowsDoNotPayTruth = refl

------------------------------------------------------------------------
-- Persistence / authority firewalls.
------------------------------------------------------------------------

data PersistedRowsCreatePNFPermission : Set where
data PersistedRowsCreateApplicabilityPermission : Set where
data PersistedRowsCreateTruthPermission : Set where
data ObservationSpanCreatesGraphSpanPermission : Set where
data GraphSpanCreatesObservationSpanPermission : Set where

persistedRowsCannotCreatePNF : PersistedRowsCreatePNFPermission → ⊥
persistedRowsCannotCreatePNF ()

persistedRowsCannotCreateApplicability :
  PersistedRowsCreateApplicabilityPermission → ⊥
persistedRowsCannotCreateApplicability ()

persistedRowsCannotCreateTruth : PersistedRowsCreateTruthPermission → ⊥
persistedRowsCannotCreateTruth ()

observationSpanCannotCreateGraphSpan :
  ObservationSpanCreatesGraphSpanPermission → ⊥
observationSpanCannotCreateGraphSpan ()

graphSpanCannotCreateObservationSpan :
  GraphSpanCreatesObservationSpanPermission → ⊥
graphSpanCannotCreateObservationSpan ()

------------------------------------------------------------------------
-- Execution/certification bookkeeping.
------------------------------------------------------------------------

slrMaterialisationOwner : String
slrMaterialisationOwner =
  "crates/sl-pg-source-store/src/legal_ir_materialization.rs"

postgresSchemaOwner : String
postgresSchemaOwner =
  "SensibLaw database/postgres_migrations/015_legal_ir_federation.sql"

sourceMaterialiserIsSemanticAuthority : Bool
sourceMaterialiserIsSemanticAuthority = false

slrRuntimeReceiptObserved : Bool
slrRuntimeReceiptObserved = false

agdaKernelReceiptObserved : Bool
agdaKernelReceiptObserved = false
