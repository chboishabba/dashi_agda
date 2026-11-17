module DASHI.Cognition.PNF.DeltaNativeParentRuntimeBridgeExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.AffectedBoundaryLocalReductionExact
open import DASHI.Cognition.PNF.BoundedInterfaceSketch
open import DASHI.Cognition.PNF.DreamFlowRuntimeComplexityExact

import DASHI.Cognition.PNF.RelationDeltaReconciliationExact as Reconcile
import DASHI.Core.AuthorityNonPromotionCore as Authority

------------------------------------------------------------------------
-- Runtime correspondence for the SensibLaw delta-native parent frontier.
--
-- These counters are structural witnesses only.  They do not manufacture a
-- wall-clock claim: NearParserWallTarget still requires an independent measured
-- physical receipt.
------------------------------------------------------------------------

record DeltaNativeParentRuntimeCounters : Set where
  constructor deltaNativeParentRuntimeCounters
  field
    parserNumericInputEvents : Nat
    exposedLocalInteractions : Nat
    unresolvedResidualItems : Nat
    transportedBoundaryDeltas : Nat
    coldIdentityMisses : Nat
    globalIndexedOperations : Nat
    fusedDatabaseBatches : Nat
    semanticHierarchyDepth : Nat

    accumulatedBoundaryKeys : Nat
    touchedBoundaryKeys : Nat
    emittedParentBoundaryDeltas : Nat

    objectKeysTouched : Nat
    factorKeysTouched : Nat
    demandKeysTouched : Nat
    actorKeysTouched : Nat
    outwardKeysTouched : Nat

    touchedFamilySum :
      touchedBoundaryKeys ≡
        objectKeysTouched
        + factorKeysTouched
        + demandKeysTouched
        + actorKeysTouched
        + outwardKeysTouched

open DeltaNativeParentRuntimeCounters public

runtimeShape : DeltaNativeParentRuntimeCounters → DreamWorkShape
runtimeShape counters =
  dreamWorkShape
    (parserNumericInputEvents counters)
    (exposedLocalInteractions counters)
    (unresolvedResidualItems counters)
    (transportedBoundaryDeltas counters)
    (coldIdentityMisses counters)
    (globalIndexedOperations counters)
    (fusedDatabaseBatches counters)
    (semanticHierarchyDepth counters)

record DeltaNativeParentRuntimeCertificate : Set where
  constructor deltaNativeParentRuntimeCertificate
  field
    counters : DeltaNativeParentRuntimeCounters
    hierarchyReceipt : DeltaNativeHierarchyReceipt

    receiptInputMatchesRuntime :
      inputDeltaAtoms hierarchyReceipt ≡ transportedBoundaryDeltas counters
    receiptTouchedMatchesRuntime :
      touchedParentKeys hierarchyReceipt ≡ touchedBoundaryKeys counters
    receiptAccumulatedMatchesRuntime :
      accumulatedParentBoundaryKeys hierarchyReceipt ≡
        accumulatedBoundaryKeys counters
    receiptEmittedMatchesRuntime :
      emittedParentDeltas hierarchyReceipt ≡
        emittedParentBoundaryDeltas counters
    receiptDepthMatchesRuntime :
      hierarchyDepth hierarchyReceipt ≡ semanticHierarchyDepth counters

open DeltaNativeParentRuntimeCertificate public

------------------------------------------------------------------------
-- Bounded-key bridge.
--
-- The database/runtime may claim the exact bounded-sketch theorem only when it
-- supplies the same explicit C-bound for each exact key family.  No runtime
-- counter can silently turn unbounded exact keys into bounded exact keys.
------------------------------------------------------------------------

record RuntimeInterfaceKeyBudget (capacity : Nat) : Set where
  constructor runtimeInterfaceKeyBudget
  field
    runtimeObjectKeyCount : Nat
    runtimeFactorKeyCount : Nat
    runtimeDemandKeyCount : Nat
    formalBudget : InterfaceSketchBudget capacity

    objectCountMatches :
      runtimeObjectKeyCount ≡ objectKeyCount formalBudget
    factorCountMatches :
      runtimeFactorKeyCount ≡ factorKeyCount formalBudget
    demandCountMatches :
      runtimeDemandKeyCount ≡ demandKeyCount formalBudget

open RuntimeInterfaceKeyBudget public

------------------------------------------------------------------------
-- Exact-work budget admission.
--
-- The parent-key count is semantic state.  The configured capacity is an
-- execution-policy bound.  Exceeding the bound rejects this execution lane.
-- It never authorizes key truncation and it does not change semantic truth.
------------------------------------------------------------------------

data BudgetAdmissionDisposition : Set where
  exactBudgetAdmitted : BudgetAdmissionDisposition
  exactBudgetRejected : BudgetAdmissionDisposition

data PositiveNat : Nat → Set where
  positive : ∀ {n} → PositiveNat (suc n)

record RuntimeExactBudgetAdmission : Set where
  constructor runtimeExactBudgetAdmission
  field
    parentKeyCount : Nat
    configuredCapacity : Nat
    excessKeyCount : Nat
    excessIsPositive : PositiveNat excessKeyCount
    parentKeyCountIsExcessPlusCapacity :
      parentKeyCount ≡ excessKeyCount + configuredCapacity
    disposition : BudgetAdmissionDisposition

open RuntimeExactBudgetAdmission public

canonical8206Over8192BudgetRejection :
  RuntimeExactBudgetAdmission
canonical8206Over8192BudgetRejection =
  runtimeExactBudgetAdmission
    8206
    8192
    14
    positive
    refl
    exactBudgetRejected

canonicalParentKeyCountIs8206 :
  parentKeyCount canonical8206Over8192BudgetRejection ≡ 8206
canonicalParentKeyCountIs8206 = refl

canonicalConfiguredCapacityIs8192 :
  configuredCapacity canonical8206Over8192BudgetRejection ≡ 8192
canonicalConfiguredCapacityIs8192 = refl

canonicalExcessKeyCountIs14 :
  excessKeyCount canonical8206Over8192BudgetRejection ≡ 14
canonicalExcessKeyCountIs14 = refl

record DeltaReconciliationRuntimeCertification
    (admission : RuntimeExactBudgetAdmission) : Set where
  constructor deltaReconciliationRuntimeCertification
  field
    admissionIsExact :
      disposition admission ≡ exactBudgetAdmitted
    survivingReconciliation :
      Reconcile.PersistedRelationDeltaReceipt

open DeltaReconciliationRuntimeCertification public

exactBudgetRejectedIsNotAdmitted :
  exactBudgetRejected ≡ exactBudgetAdmitted → ⊥
exactBudgetRejectedIsNotAdmitted ()

canonical8206Over8192CannotCertify :
  DeltaReconciliationRuntimeCertification
    canonical8206Over8192BudgetRejection →
  ⊥
canonical8206Over8192CannotCertify certification =
  exactBudgetRejectedIsNotAdmitted
    (admissionIsExact certification)

data BudgetRejectionAuthorizesSemanticTruncation : Set where

data BudgetExpansionCreatesSemanticAuthority : Set where

data RolledBackReceiptCreatesRuntimeCertification : Set where

budgetRejectionDoesNotAuthorizeTruncation :
  BudgetRejectionAuthorizesSemanticTruncation → ⊥
budgetRejectionDoesNotAuthorizeTruncation ()

budgetExpansionDoesNotCreateSemanticAuthority :
  BudgetExpansionCreatesSemanticAuthority → ⊥
budgetExpansionDoesNotCreateSemanticAuthority ()

rolledBackReceiptDoesNotCreateRuntimeCertification :
  RolledBackReceiptCreatesRuntimeCertification → ⊥
rolledBackReceiptDoesNotCreateRuntimeCertification ()

RuntimeBudgetAuthorityBoundary : Set
RuntimeBudgetAuthorityBoundary =
  Authority.AuthorityNonPromotionBundle

runtimeBudgetAuthorityBoundary :
  RuntimeBudgetAuthorityBoundary
runtimeBudgetAuthorityBoundary =
  Authority.mkClosedAuthorityNonPromotionBundle
    "SensibLaw exact parent-key budget admission and relation-delta certification"

runtimeBudgetDoesNotPromoteRuntimeAuthority :
  Authority.runtimeAuthorityFlag runtimeBudgetAuthorityBoundary ≡ false
runtimeBudgetDoesNotPromoteRuntimeAuthority =
  Authority.runtimeAuthorityFlagIsFalse runtimeBudgetAuthorityBoundary

runtimeBudgetDoesNotPromoteEmpiricalAuthority :
  Authority.empiricalAuthorityFlag runtimeBudgetAuthorityBoundary ≡ false
runtimeBudgetDoesNotPromoteEmpiricalAuthority =
  Authority.empiricalAuthorityFlagIsFalse runtimeBudgetAuthorityBoundary

runtimeBudgetDoesNotPromoteLegalAuthority :
  Authority.legalAuthorityFlag runtimeBudgetAuthorityBoundary ≡ false
runtimeBudgetDoesNotPromoteLegalAuthority =
  Authority.legalAuthorityFlagIsFalse runtimeBudgetAuthorityBoundary

runtimeBudgetDoesNotPromoteTheoremAuthority :
  Authority.theoremAuthorityFlag runtimeBudgetAuthorityBoundary ≡ false
runtimeBudgetDoesNotPromoteTheoremAuthority =
  Authority.theoremAuthorityFlagIsFalse runtimeBudgetAuthorityBoundary

------------------------------------------------------------------------
-- Explicit anti-promotion boundaries.
------------------------------------------------------------------------

data StructuralReceiptImpliesWallSpeedup : Set where

data TouchedKeyCountMayBeAccumulatedStateScan : Set where

data RuntimeLookupMayCreateSemanticAuthority : Set where

structuralReceiptCannotManufactureWallSpeedup :
  StructuralReceiptImpliesWallSpeedup → ⊥
structuralReceiptCannotManufactureWallSpeedup ()

touchedKeysDoNotAuthorizeAccumulatedRescan :
  TouchedKeyCountMayBeAccumulatedStateScan → ⊥
touchedKeysDoNotAuthorizeAccumulatedRescan ()

lookupProjectionDoesNotCreateAuthority :
  RuntimeLookupMayCreateSemanticAuthority → ⊥
lookupProjectionDoesNotCreateAuthority ()
