module DASHI.Physics.Closure.YMSprint105CompactSimpleGroupParameterTable where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Sprint 105 compact-simple-group parameter table.
--
-- This file records the supplied Yang-Mills group-parameter data as a
-- concrete finite status/table surface.  It does not assert a Clay proof:
-- the proof spine is recorded as group-agnostic only after parameter checks,
-- while all-compact-simple-G completeness remains an audit obligation unless
-- a complete classification/table coverage surface is supplied.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data CompactSimpleGroupEntry : Set where
  SU2 :
    CompactSimpleGroupEntry
  SU3 :
    CompactSimpleGroupEntry
  SUN :
    CompactSimpleGroupEntry
  G2 :
    CompactSimpleGroupEntry
  E8 :
    CompactSimpleGroupEntry

canonicalCompactSimpleGroupEntries :
  List CompactSimpleGroupEntry
canonicalCompactSimpleGroupEntries =
  SU2
  ∷ SU3
  ∷ SUN
  ∷ G2
  ∷ E8
  ∷ []

data ParameterCoverageStatus : Set where
  suppliedFiniteTableWithSUNFamilyAuditOpen :
    ParameterCoverageStatus

data ProofStructureStatus : Set where
  groupAgnosticAfterParameterChecking :
    ProofStructureStatus

data CompletenessAuditStatus : Set where
  allCompactSimpleGCompletenessAuditRequired :
    CompletenessAuditStatus

record GroupParameterRow : Set where
  constructor mkGroupParameterRow
  field
    groupEntry :
      CompactSimpleGroupEntry
    groupName :
      String
    adjointDimensionText :
      String
    kGText :
      String
    parameterCheckText :
      String

open GroupParameterRow public

su2ParameterRow : GroupParameterRow
su2ParameterRow =
  mkGroupParameterRow
    SU2
    "SU(2)"
    "3"
    "9"
    "SU(2): adjoint dimension 3; k_G approximation/expression 9."

su3ParameterRow : GroupParameterRow
su3ParameterRow =
  mkGroupParameterRow
    SU3
    "SU(3)"
    "8"
    "11"
    "SU(3): adjoint dimension 8; k_G approximation/expression 11."

sunParameterRow : GroupParameterRow
sunParameterRow =
  mkGroupParameterRow
    SUN
    "SU(N)"
    "N^2-1"
    "9 + 2 log2 N"
    "SU(N): adjoint dimension N^2-1; k_G approximation/expression 9 + 2 log2 N."

g2ParameterRow : GroupParameterRow
g2ParameterRow =
  mkGroupParameterRow
    G2
    "G2"
    "14"
    "~12"
    "G2: adjoint dimension 14; k_G approximation/expression ~12."

e8ParameterRow : GroupParameterRow
e8ParameterRow =
  mkGroupParameterRow
    E8
    "E8"
    "248"
    "~18"
    "E8: adjoint dimension 248; k_G approximation/expression ~18."

canonicalGroupParameterRows :
  List GroupParameterRow
canonicalGroupParameterRows =
  su2ParameterRow
  ∷ su3ParameterRow
  ∷ sunParameterRow
  ∷ g2ParameterRow
  ∷ e8ParameterRow
  ∷ []

proofStructureStatement : String
proofStructureStatement =
  "The proof structure is group-agnostic except for parameter checking against the compact-simple-group parameter table."

completenessAuditStatement : String
completenessAuditStatement =
  "All-compact-simple-G completeness remains a required audit unless full classification/table coverage is present."

tableBoundaryStatement : String
tableBoundaryStatement =
  "Concrete Sprint105 table entries: SU(2) dim 3 k_G 9; SU(3) dim 8 k_G 11; SU(N) dim N^2-1 k_G 9 + 2 log2 N; G2 dim 14 k_G ~12; E8 dim 248 k_G ~18."

record YMSprint105CompactSimpleGroupParameterTableReceipt : Setω where
  field
    tableEntries :
      List CompactSimpleGroupEntry

    tableEntriesAreCanonical :
      tableEntries ≡ canonicalCompactSimpleGroupEntries

    parameterRows :
      List GroupParameterRow

    parameterRowsAreCanonical :
      parameterRows ≡ canonicalGroupParameterRows

    coverageStatus :
      ParameterCoverageStatus

    coverageStatusIsSuppliedFiniteAuditOpen :
      coverageStatus ≡ suppliedFiniteTableWithSUNFamilyAuditOpen

    proofStructureStatus :
      ProofStructureStatus

    proofStructureStatusIsGroupAgnostic :
      proofStructureStatus ≡ groupAgnosticAfterParameterChecking

    completenessAuditStatus :
      CompletenessAuditStatus

    completenessAuditStatusIsRequired :
      completenessAuditStatus ≡ allCompactSimpleGCompletenessAuditRequired

    parameterTableConcrete :
      Bool

    parameterTableConcreteIsTrue :
      parameterTableConcrete ≡ true

    fullClassificationTableCoveragePresent :
      Bool

    fullClassificationTableCoveragePresentIsFalse :
      fullClassificationTableCoveragePresent ≡ false

    allCompactSimpleGCompletenessClaimed :
      Bool

    allCompactSimpleGCompletenessClaimedIsFalse :
      allCompactSimpleGCompletenessClaimed ≡ false

    clayYangMillsPromotedHere :
      Bool

    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

    globalClayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    proofStructureText :
      String

    proofStructureTextIsCanonical :
      proofStructureText ≡ proofStructureStatement

    completenessAuditText :
      String

    completenessAuditTextIsCanonical :
      completenessAuditText ≡ completenessAuditStatement

    receiptBoundary :
      List String

open YMSprint105CompactSimpleGroupParameterTableReceipt public

canonicalYMSprint105CompactSimpleGroupParameterTableReceipt :
  YMSprint105CompactSimpleGroupParameterTableReceipt
canonicalYMSprint105CompactSimpleGroupParameterTableReceipt =
  record
    { tableEntries =
        canonicalCompactSimpleGroupEntries
    ; tableEntriesAreCanonical =
        refl
    ; parameterRows =
        canonicalGroupParameterRows
    ; parameterRowsAreCanonical =
        refl
    ; coverageStatus =
        suppliedFiniteTableWithSUNFamilyAuditOpen
    ; coverageStatusIsSuppliedFiniteAuditOpen =
        refl
    ; proofStructureStatus =
        groupAgnosticAfterParameterChecking
    ; proofStructureStatusIsGroupAgnostic =
        refl
    ; completenessAuditStatus =
        allCompactSimpleGCompletenessAuditRequired
    ; completenessAuditStatusIsRequired =
        refl
    ; parameterTableConcrete =
        true
    ; parameterTableConcreteIsTrue =
        refl
    ; fullClassificationTableCoveragePresent =
        false
    ; fullClassificationTableCoveragePresentIsFalse =
        refl
    ; allCompactSimpleGCompletenessClaimed =
        false
    ; allCompactSimpleGCompletenessClaimedIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        false
    ; clayYangMillsPromotedHereIsFalse =
        refl
    ; globalClayYangMillsPromotedIsFalse =
        refl
    ; proofStructureText =
        proofStructureStatement
    ; proofStructureTextIsCanonical =
        refl
    ; completenessAuditText =
        completenessAuditStatement
    ; completenessAuditTextIsCanonical =
        refl
    ; receiptBoundary =
        tableBoundaryStatement
        ∷ proofStructureStatement
        ∷ completenessAuditStatement
        ∷ "clayYangMillsPromoted=false"
        ∷ []
    }

canonicalYMSprint105CompactSimpleGroupParameterRows :
  List GroupParameterRow
canonicalYMSprint105CompactSimpleGroupParameterRows =
  parameterRows canonicalYMSprint105CompactSimpleGroupParameterTableReceipt

canonicalYMSprint105CompletenessAuditRequired :
  CompletenessAuditStatus
canonicalYMSprint105CompletenessAuditRequired =
  completenessAuditStatus canonicalYMSprint105CompactSimpleGroupParameterTableReceipt

canonicalYMSprint105ClayYangMillsPromotedFalse :
  clayYangMillsPromoted ≡ false
canonicalYMSprint105ClayYangMillsPromotedFalse =
  globalClayYangMillsPromotedIsFalse
    canonicalYMSprint105CompactSimpleGroupParameterTableReceipt
