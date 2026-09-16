module DASHI.Wikimedia.IbrahimMonster3BSimpleSubobjectClassificationLeanReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SIMPLE-SUBOBJECT CLASSIFICATION LEAN SOURCE RECEIPT
--
-- Concurrent Lean work has already written the next consumer theorem:
-- if V has whole character a * char(H), U and H are simple, and there is a
-- nonzero equivariant map U -> V, then U is isomorphic to H.
--
-- This is exactly the simple-type classification needed before semisimple
-- isotypic assembly.  It is still weaker than the final isotypic equivalence,
-- and source presence is not kernel certification.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- WrongType / certification firewalls.
------------------------------------------------------------------------

data SourceCreatesKernelReceipt : Set where
data ClassificationCreatesIsotypicAssembly : Set where
data ClassificationCreatesConcreteZetaRecognition : Set where
data OEISCreatesClassification : Set where

sourceDoesNotCreateKernelReceipt : SourceCreatesKernelReceipt -> ⊥
sourceDoesNotCreateKernelReceipt ()

classificationDoesNotCreateIsotypicAssembly :
  ClassificationCreatesIsotypicAssembly -> ⊥
classificationDoesNotCreateIsotypicAssembly ()

classificationDoesNotCreateConcreteRecognition :
  ClassificationCreatesConcreteZetaRecognition -> ⊥
classificationDoesNotCreateConcreteRecognition ()

oeisDoesNotCreateClassification : OEISCreatesClassification -> ⊥
oeisDoesNotCreateClassification ()

record SimpleSubobjectClassificationBoundary : Set where
  constructor simple-subobject-classification-boundary
  field
    sourceWritten : Bool
    nonzeroSimpleSourceClassificationWritten : Bool
    leanKernelReceiptObserved : Bool
    agdaTransportObserved : Bool
    isotypicAssemblyPaid : Bool
    concreteZetaRecognitionPaid : Bool
    oeisCreatesClassification : Bool
    nextResidual : String
open SimpleSubobjectClassificationBoundary public

canonicalSimpleSubobjectClassificationBoundary :
  SimpleSubobjectClassificationBoundary
canonicalSimpleSubobjectClassificationBoundary =
  simple-subobject-classification-boundary
    true true
    false false false false false
    "Kernel-check the simple-source classifier. Then combine it with Maschke/semisimplicity: every simple submodule of the restricted k[G]-module admits a nonzero inclusion into V, so the classifier should identify every occurring simple type with H_zeta. Only after that prove IsIsotypicOfType and use linearEquiv_fun; determine the copy count separately from the repeated-character multiplicity lemma. OEIS and 65610=90*729 remain non-promoting."
