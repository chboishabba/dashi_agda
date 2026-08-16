module DASHI.Ontology.LeanWikidataExistingContentAudit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.WikidataTypePressureMiniWorldExact as MiniWorld
open import DASHI.Ontology.LeanWikidataSourceSnapshot

------------------------------------------------------------------------
-- Existing DASHI ontology objects do not all live at the same representation
-- level.  James's executable KB expects concrete identifiers and graph facts;
-- our type-pressure mini-world is intentionally an abstract semantic toy.
--
-- This module prevents the bridge from silently pretending that an abstract
-- DASHI world has already been executed by the Lean KB engine.
------------------------------------------------------------------------

data DashiOntologyRepresentation : Set where
  abstractSemanticWorld concreteQidGraph : DashiOntologyRepresentation

data JamesKernelEligibility : Set where
  requiresConcreteTranslation eligibleForExecution : JamesKernelEligibility

kernelEligibility : DashiOntologyRepresentation → JamesKernelEligibility
kernelEligibility abstractSemanticWorld = requiresConcreteTranslation
kernelEligibility concreteQidGraph = eligibleForExecution

-- The current PNF repair mini-world is source-level abstract by construction:
-- its EventType/PredicateRoleEvidence constructors are not Qids/P31/P279 rows.
typePressureMiniWorldRepresentation : DashiOntologyRepresentation
typePressureMiniWorldRepresentation = abstractSemanticWorld

typePressureMiniWorldNeedsTranslation :
  kernelEligibility typePressureMiniWorldRepresentation ≡ requiresConcreteTranslation
typePressureMiniWorldNeedsTranslation = refl

------------------------------------------------------------------------
-- A concrete adapter must identify the exact input graph presented to James's
-- kernel.  The hash prevents a theorem receipt for one KB from being reused as
-- if it had checked a different graph.
------------------------------------------------------------------------

record ConcreteQidGraphAdapter : Set where
  constructor concreteQidGraphAdapter
  field
    graphId : String
    graphSha256 : String
    qidReferences : List String
    p31FactReferences : List String
    p279FactReferences : List String
    disjointFactReferences : List String
    provenanceReferences : List String

open ConcreteQidGraphAdapter public

record JamesKernelExecutionReceipt : Set where
  constructor jamesKernelExecutionReceipt
  field
    adapter : ConcreteQidGraphAdapter
    requestId : String
    sourceArchiveSha256 : String
    inputGraphSha256 : String
    theoremOrChecker : String
    sourceMatched : Bool
    inputMatched : Bool
    executionAccepted : Bool

open JamesKernelExecutionReceipt public

executionReceiptAccepted : JamesKernelExecutionReceipt → Bool
executionReceiptAccepted receipt with
  sourceMatched receipt | inputMatched receipt | executionAccepted receipt
... | true | true | true = true
... | _ | _ | _ = false

sourceMismatchRejectsExecution :
  (receipt : JamesKernelExecutionReceipt) →
  sourceMatched receipt ≡ false →
  executionReceiptAccepted receipt ≡ false
sourceMismatchRejectsExecution receipt refl with inputMatched receipt | executionAccepted receipt
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl

inputMismatchRejectsExecution :
  (receipt : JamesKernelExecutionReceipt) →
  inputMatched receipt ≡ false →
  executionReceiptAccepted receipt ≡ false
inputMismatchRejectsExecution receipt refl with sourceMatched receipt | executionAccepted receipt
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl

------------------------------------------------------------------------
-- There is deliberately no admission constructor for the abstract toy world.
-- Any future execution claim must first supply a ConcreteQidGraphAdapter.
------------------------------------------------------------------------

data TypePressureMiniWorldAlreadyCheckedByJames : Set where

typePressureMiniWorldNotYetKernelChecked :
  TypePressureMiniWorldAlreadyCheckedByJames → ⊥
typePressureMiniWorldNotYetKernelChecked ()

-- Referencing one constructor ensures the audit remains tied to the actual
-- existing mini-world module rather than becoming an orphaned prose boundary.
observedMiniWorldEndpoint : MiniWorld.EventType
observedMiniWorldEndpoint = MiniWorld.typeUnderspecified
