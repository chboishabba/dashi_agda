module DASHI.Cognition.PNF.DeltaNativeParentRuntimeBridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.AffectedBoundaryLocalReductionExact
open import DASHI.Cognition.PNF.BoundedInterfaceSketch
open import DASHI.Cognition.PNF.DreamFlowRuntimeComplexityExact

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
