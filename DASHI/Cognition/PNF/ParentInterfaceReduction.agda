module DASHI.Cognition.PNF.ParentInterfaceReduction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- A lookup row is not independent semantic evidence.  It is a searchable
-- projection of an export that the parent interface actually admitted.
------------------------------------------------------------------------

data InterfaceTargetKind : Set where
  objectTarget factorTarget demandTarget : InterfaceTargetKind

record InterfaceMember : Set where
  constructor interfaceMember
  field
    memberInterface : InterfaceId
    memberKind : InterfaceTargetKind
    memberIdentity : Nat

open InterfaceMember public

data ExportAdmission : Set where
  admittedExport rejectedExport : ExportAdmission

data LookupProjection : ExportAdmission → Set where
  lookupOfAdmittedExport :
    (member : InterfaceMember) → LookupProjection admittedExport

rejectedExportCannotProduceLookup : LookupProjection rejectedExport → ⊥
rejectedExportCannotProduceLookup ()

record LookupExportCoherence : Set where
  constructor lookupExportCoherence
  field
    member : InterfaceMember
    exportAdmission : ExportAdmission
    searchableProjection : LookupProjection exportAdmission

open LookupExportCoherence public

canonicalLookupExportCoherence :
  (member : InterfaceMember) → LookupExportCoherence
canonicalLookupExportCoherence member =
  lookupExportCoherence
    member
    admittedExport
    (lookupOfAdmittedExport member)

------------------------------------------------------------------------
-- Rejecting a parent export does not erase the immutable child evidence.  It
-- only removes that member from the parent's compact searchable boundary.
------------------------------------------------------------------------

data ChildEvidenceState : Set where
  retainedChildEvidence : ChildEvidenceState

data ParentBoundaryState : Set where
  parentMemberAdmitted parentMemberRejected : ParentBoundaryState

record ReductiveDisposition : Set where
  constructor reductiveDisposition
  field
    childEvidence : ChildEvidenceState
    parentBoundary : ParentBoundaryState

open ReductiveDisposition public

rejectAtParentRetainInChild : ReductiveDisposition
rejectAtParentRetainInChild =
  reductiveDisposition retainedChildEvidence parentMemberRejected

record ParentCardinalityCertificate : Set where
  constructor parentCardinalityCertificate
  field
    admittedExportCount copiedChildExportCount : Nat
    parentDoesNotExceedCopiedChildren :
      admittedExportCount ≤ᶜ copiedChildExportCount
    lookupRowCount : Nat
    lookupRowsDoNotExceedAdmittedExports :
      lookupRowCount ≤ᶜ admittedExportCount

open ParentCardinalityCertificate public

------------------------------------------------------------------------
-- Runtime correspondence: migration 054 applies the same rule uniformly to
-- object, factor and demand targets and deletes historical lookup rows lacking
-- a matching admitted export.
------------------------------------------------------------------------

record ParentReductionBoundary : Set where
  constructor parentReductionBoundary
  field
    objectLookupRequiresExport : LookupExportCoherence
    factorLookupRequiresExport : LookupExportCoherence
    demandLookupRequiresExport : LookupExportCoherence
    rejectedMembersRetainChildEvidence : ReductiveDisposition

canonicalParentReductionBoundary :
  InterfaceId → Nat → Nat → Nat → ParentReductionBoundary
canonicalParentReductionBoundary interface objectId factorId demandId =
  parentReductionBoundary
    (canonicalLookupExportCoherence
      (interfaceMember interface objectTarget objectId))
    (canonicalLookupExportCoherence
      (interfaceMember interface factorTarget factorId))
    (canonicalLookupExportCoherence
      (interfaceMember interface demandTarget demandId))
    rejectAtParentRetainInChild
