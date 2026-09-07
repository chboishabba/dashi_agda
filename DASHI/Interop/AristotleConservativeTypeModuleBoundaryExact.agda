module DASHI.Interop.AristotleConservativeTypeModuleBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph

------------------------------------------------------------------------
-- Source contracts rechecked against RequestProject.Modules in the attached
-- Aristotle archive.
--
-- Aristotle's moduleOf theorem has both soundness and, under its own full-base
-- membership hypotheses, conservativity.  SensibLaw's *pruned Zelph* runtime
-- must keep those strengths separate: a sound-only preservation receipt can
-- justify positive P31/P279 answers without justifying negative completeness.
------------------------------------------------------------------------

record AristotleModuleContract : Set where
  constructor aristotle-module-contract
  field
    sourceModule : String
    declaration : String
    contractReference : String
open AristotleModuleContract public

subclassSoundnessContract : AristotleModuleContract
subclassSoundnessContract =
  aristotle-module-contract
    "RequestProject.Modules"
    "Wikidata.KB.moduleOf_isSubclassOf_le"
    "every subclass fact derived by the extracted module is derived by the full base"

instanceSoundnessContract : AristotleModuleContract
instanceSoundnessContract =
  aristotle-module-contract
    "RequestProject.Modules"
    "Wikidata.KB.moduleOf_isInstanceOf_le"
    "every instance fact derived by the extracted module is derived by the full base"

subclassConservativityContract : AristotleModuleContract
subclassConservativityContract =
  aristotle-module-contract
    "RequestProject.Modules"
    "Wikidata.KB.moduleOf_isSubclassOf"
    "for an item in the certified full-base module, subclass answers agree exactly with the full base"

instanceConservativityContract : AristotleModuleContract
instanceConservativityContract =
  aristotle-module-contract
    "RequestProject.Modules"
    "Wikidata.KB.moduleOf_isInstanceOf"
    "for an item in the certified full-base module, instance answers agree exactly with the full base"

moduleEntailmentContract : AristotleModuleContract
moduleEntailmentContract =
  aristotle-module-contract
    "RequestProject.Modules"
    "Wikidata.KB.entails_moduleOf"
    "the full base entails every extracted module; extraction does not add knowledge"

------------------------------------------------------------------------
-- Runtime-strength receipt: positive answers are sound; negative completeness
-- is a separate bit and is NOT required to be true.
------------------------------------------------------------------------

record TypeClosureSoundnessReceipt : Set where
  constructor type-closure-soundness-receipt
  field
    seedReference : String
    graphRevisionReference : String
    graphCoverage : Zelph.QueryCoverageReceipt
    queryFamilyReference : String
    p31CoverageReference : String
    p279CoverageReference : String
    moduleReference : String
    positiveAnswersSound : Bool
    positiveAnswersSoundIsTrue : positiveAnswersSound ≡ true
    negativeAnswersComplete : Bool
    isWholeGraph : Bool
    isWholeGraphIsFalse : isWholeGraph ≡ false
    createsTruthAuthority : Bool
    createsTruthAuthorityIsFalse : createsTruthAuthority ≡ false
open TypeClosureSoundnessReceipt public

------------------------------------------------------------------------
-- Stronger receipt: available only when completeness has independently been
-- certified for the declared type-query family.
------------------------------------------------------------------------

record TypeClosureModuleReceipt : Set where
  constructor type-closure-module-receipt
  field
    soundnessReceipt : TypeClosureSoundnessReceipt
    completenessReference : String
    conservativeForInstanceAndSubclass : Bool
    conservativeForInstanceAndSubclassIsTrue : conservativeForInstanceAndSubclass ≡ true
    negativeAnswersComplete : Bool
    negativeAnswersCompleteIsTrue : negativeAnswersComplete ≡ true
open TypeClosureModuleReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SoundTypeModuleIsWholeWikidata : Set where
data SoundTypeModulePreservesEveryProperty : Set where
data PositiveSoundnessImpliesNegativeCompleteness : Set where
data TypeClosureCreatesNativeStatementBundle : Set where
data TypeClosureCreatesMigrationAuthority : Set where

soundTypeModuleIsNotWholeWikidata :
  SoundTypeModuleIsWholeWikidata → ⊥
soundTypeModuleIsNotWholeWikidata ()

soundnessIsRelationFamilyScoped :
  SoundTypeModulePreservesEveryProperty → ⊥
soundnessIsRelationFamilyScoped ()

positiveSoundnessDoesNotGiveNegativeCompleteness :
  PositiveSoundnessImpliesNegativeCompleteness → ⊥
positiveSoundnessDoesNotGiveNegativeCompleteness ()

typeClosureDoesNotCreateNativeStatementBundle :
  TypeClosureCreatesNativeStatementBundle → ⊥
typeClosureDoesNotCreateNativeStatementBundle ()

typeClosureDoesNotCreateMigrationAuthority :
  TypeClosureCreatesMigrationAuthority → ⊥
typeClosureDoesNotCreateMigrationAuthority ()

record ConservativeTypeModuleBoundary : Set where
  constructor conservative-type-module-boundary
  field
    p31P279ModuleMayBeSmallerThanItemGraph : Bool
    positiveAnswersMayBeSoundWithoutNegativeCompleteness : Bool
    completeReceiptMayPreserveDeclaredTypeClosure : Bool
    modulePreservesEveryPropertyFamily : Bool
    moduleReconstructsNativeStatementBundles : Bool
    moduleCreatesMigrationAuthority : Bool

canonicalConservativeTypeModuleBoundary : ConservativeTypeModuleBoundary
canonicalConservativeTypeModuleBoundary =
  conservative-type-module-boundary true true true false false false

conservativeTypeModuleStatement : String
conservativeTypeModuleStatement =
  "For subject typing, SensibLaw may consume a bounded P31/P279 type module rather than the whole item graph. A sound-only pruned-query receipt supports positive retained instance/subclass answers but does not establish negative completeness. Full conservativity is a strictly stronger receipt requiring independent completeness for the same query family. Neither strength preserves every property family, reconstructs native statement bundles, or creates migration authority."
