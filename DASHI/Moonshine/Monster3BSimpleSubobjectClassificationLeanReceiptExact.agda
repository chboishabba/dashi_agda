module DASHI.Moonshine.Monster3BSimpleSubobjectClassificationLeanReceiptExact where

------------------------------------------------------------------------
-- GENERIC SIMPLE-SUBOBJECT CLASSIFICATION LEAN SOURCE RECEIPT
--
-- Companion Lean source already writes the generic theorem:
-- if V has whole character a * char(H), U and H are simple, and there is a
-- nonzero equivariant map U -> V, then U is isomorphic to H.
--
-- This pays the generic classifier theorem source, not its actual Monster
-- same-object instantiation.  Actual W_zeta inputs remain proof obligations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record SimpleSubobjectClassificationLeanReceipt : Set where
  constructor simple-subobject-classification-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    theoremName : String
    redCommit : String
    sourceCommit : String
    tacticLightRefactorCommit : String
    rootIntegrationCommit : String
open SimpleSubobjectClassificationLeanReceipt public

currentSimpleSubobjectClassificationLeanReceipt :
  SimpleSubobjectClassificationLeanReceipt
currentSimpleSubobjectClassificationLeanReceipt =
  simple-subobject-classification-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/monster3b-fdrep-groupalgebra-adapter"
    "Synthesis/MonsterWholeCharacterSimpleSubobjectClassification.lean"
    "Synthesis/MonsterWholeCharacterSimpleSubobjectRegression.lean"
    "Synthesis.simple_source_iso_of_nonzero_hom_and_character_eq_smul"
    "fc95ca96d8177a83052c254a24029c6a82279490"
    "e79705763902207938f43a0927b5c05382283adc"
    "54c7974da37979330d0cd37d832fee7da6432d1a"
    "61170f22fd70b851c0e35c48a4355963e1a1f096"

data SourceCreatesKernelReceipt : Set where
data GenericClassifierCreatesActualMonsterClassifier : Set where
data ClassificationCreatesIsotypicAssembly : Set where

genericSourceDoesNotCreateKernelReceipt : SourceCreatesKernelReceipt → ⊥
genericSourceDoesNotCreateKernelReceipt ()

genericClassifierDoesNotCreateActualMonsterClassifier :
  GenericClassifierCreatesActualMonsterClassifier → ⊥
genericClassifierDoesNotCreateActualMonsterClassifier ()

classificationDoesNotCreateIsotypicAssembly :
  ClassificationCreatesIsotypicAssembly → ⊥
classificationDoesNotCreateIsotypicAssembly ()

record Boundary : Set where
  constructor boundary
  field
    sourceWritten : Bool
    nonzeroSimpleSourceClassificationWritten : Bool
    leanKernelReceiptObserved : Bool
    agdaTransportObserved : Bool
    actualMonsterClassifierInstantiatedHere : Bool
    genericClassifierAloneCreatesIsotypicAssembly : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true
  false false false false
