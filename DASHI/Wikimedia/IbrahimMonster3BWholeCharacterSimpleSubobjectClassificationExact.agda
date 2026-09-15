module DASHI.Wikimedia.IbrahimMonster3BWholeCharacterSimpleSubobjectClassificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WHOLE-CHARACTER SIMPLE-SUBOBJECT CLASSIFICATION RECEIPT
--
-- The current Lean branch contains a deliberately narrow generic theorem:
-- if simple U admits a nonzero equivariant map U -> V and
--
--     character V = a * character H,
--
-- with H simple, then U is isomorphic to H.  This is the consumer-relative
-- classification needed after the FDRep/group-algebra action/submodule adapter:
-- every simple type that actually occurs through a nonzero morphism is forced
-- to be H.
--
-- This source theorem is NOT the full semisimple/isotypic assembly theorem.
-- It does not prove multiplicity 90, V ~= H^90, or the concrete X6 x Fin 90
-- Weyl basis/action recognition.  Source presence is also separate from a Lean
-- kernel receipt and from Agda cross-prover transport.
------------------------------------------------------------------------

record LeanSimpleSubobjectClassificationReceipt : Set where
  constructor lean-simple-subobject-classification-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    sourcePath : String
    theoremName : String
    redCommit : String
    currentSourceHead : String
open LeanSimpleSubobjectClassificationReceipt public

currentLeanSimpleSubobjectClassificationReceipt :
  LeanSimpleSubobjectClassificationReceipt
currentLeanSimpleSubobjectClassificationReceipt =
  lean-simple-subobject-classification-receipt
    "chboishabba/dashi_lean4"
    "agent/monster3b-fdrep-groupalgebra-adapter"
    "Synthesis/MonsterWholeCharacterSimpleSubobjectRegression.lean"
    "Synthesis/MonsterWholeCharacterSimpleSubobjectClassification.lean"
    "Synthesis.simple_source_iso_of_nonzero_hom_and_character_eq_smul"
    "fc95ca96d8177a83052c254a24029c6a82279490"
    "61170f22fd70b851c0e35c48a4355963e1a1f096"

------------------------------------------------------------------------
-- WrongType / authority firewalls.
------------------------------------------------------------------------

data SimpleSourceClassifierCreatesSemisimpleAssembly : Set where
data SimpleSourceClassifierCreatesMultiplicityNinety : Set where
data SimpleSourceClassifierCreatesConcreteWeylRecognition : Set where
data LeanSourceCreatesKernelReceipt : Set where
data OEISCreatesSimpleTypeClassification : Set where

simpleSourceClassifierDoesNotCreateSemisimpleAssembly :
  SimpleSourceClassifierCreatesSemisimpleAssembly -> ⊥
simpleSourceClassifierDoesNotCreateSemisimpleAssembly ()

simpleSourceClassifierDoesNotCreateMultiplicityNinety :
  SimpleSourceClassifierCreatesMultiplicityNinety -> ⊥
simpleSourceClassifierDoesNotCreateMultiplicityNinety ()

simpleSourceClassifierDoesNotCreateConcreteWeylRecognition :
  SimpleSourceClassifierCreatesConcreteWeylRecognition -> ⊥
simpleSourceClassifierDoesNotCreateConcreteWeylRecognition ()

leanSourceDoesNotCreateKernelReceipt : LeanSourceCreatesKernelReceipt -> ⊥
leanSourceDoesNotCreateKernelReceipt ()

oeisDoesNotCreateSimpleTypeClassification :
  OEISCreatesSimpleTypeClassification -> ⊥
oeisDoesNotCreateSimpleTypeClassification ()

record SimpleSubobjectClassificationBoundary : Set where
  constructor simple-subobject-classification-boundary
  field
    leanSourceWritten : Bool
    classifiesOnlySimpleSourcesWithNonzeroHom : Bool
    wholeCharacterScalarIdentityConsumed : Bool
    simpleOrthogonalityConsumed : Bool
    literalConstituentEnumerationLogicallyMandatoryAfterClassifier : Bool

    semisisimpleAssemblyWritten : Bool
    multiplicityNinetyPaid : Bool
    directSumNinetyIsoPaid : Bool
    concreteWeylBasisActionRecognitionPaid : Bool
    actualMonsterSameObjectRecognitionPaid : Bool

    leanKernelReceiptObserved : Bool
    agdaTransportObserved : Bool
    oeisCreatesClassificationAuthority : Bool
    nextResidual : String
open SimpleSubobjectClassificationBoundary public

canonicalSimpleSubobjectClassificationBoundary :
  SimpleSubobjectClassificationBoundary
canonicalSimpleSubobjectClassificationBoundary =
  simple-subobject-classification-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    "kernel-check the narrow Lean simple-source classifier, then use Maschke semisimplicity to assemble V from simple subobjects whose type is now forced to be H_zeta. Only after that pay multiplicity 90 / V ~= H_zeta^90. Concrete X6 x Fin 90 basis and translation/modulation action recognition remains a separate same-object downstream weld."
