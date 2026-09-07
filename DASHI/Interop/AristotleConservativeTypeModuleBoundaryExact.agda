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
-- For a chosen seed signature, moduleOf follows direct P279/P31 dependencies.
-- About items in the module it preserves exactly the subclass/instance answers
-- of the full validated base, while never inventing a fact.
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
    "for an item in the module, subclass answers agree exactly with the full base"

instanceConservativityContract : AristotleModuleContract
instanceConservativityContract =
  aristotle-module-contract
    "RequestProject.Modules"
    "Wikidata.KB.moduleOf_isInstanceOf"
    "for an item in the module, instance answers agree exactly with the full base"

moduleEntailmentContract : AristotleModuleContract
moduleEntailmentContract =
  aristotle-module-contract
    "RequestProject.Modules"
    "Wikidata.KB.entails_moduleOf"
    "the full base entails every extracted module; extraction does not add knowledge"

record TypeClosureModuleReceipt : Set where
  constructor type-closure-module-receipt
  field
    seedReference : String
    graphRevisionReference : String
    graphCoverage : Zelph.QueryCoverageReceipt
    p31CoverageReference : String
    p279CoverageReference : String
    moduleReference : String
    conservativeForInstanceAndSubclass : Bool
    conservativeForInstanceAndSubclassIsTrue : conservativeForInstanceAndSubclass ≡ true
    isWholeGraph : Bool
    isWholeGraphIsFalse : isWholeGraph ≡ false
    createsTruthAuthority : Bool
    createsTruthAuthorityIsFalse : createsTruthAuthority ≡ false
open TypeClosureModuleReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ConservativeTypeModuleIsWholeWikidata : Set where
data ConservativeTypeModulePreservesEveryProperty : Set where
data TypeClosureCreatesNativeStatementBundle : Set where
data TypeClosureCreatesMigrationAuthority : Set where

conservativeTypeModuleIsNotWholeWikidata :
  ConservativeTypeModuleIsWholeWikidata → ⊥
conservativeTypeModuleIsNotWholeWikidata ()

conservativityIsRelationFamilyScoped :
  ConservativeTypeModulePreservesEveryProperty → ⊥
conservativityIsRelationFamilyScoped ()

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
    modulePreservesDeclaredTypeClosure : Bool
    modulePreservesEveryPropertyFamily : Bool
    moduleReconstructsNativeStatementBundles : Bool
    moduleCreatesMigrationAuthority : Bool

canonicalConservativeTypeModuleBoundary : ConservativeTypeModuleBoundary
canonicalConservativeTypeModuleBoundary =
  conservative-type-module-boundary true true false false false

conservativeTypeModuleStatement : String
conservativeTypeModuleStatement =
  "For subject typing, SensibLaw may consume a bounded conservative P31/P279 module rather than the whole item graph when the module's revision and coverage receipt establish the declared type-closure boundary. The module preserves the relevant instance/subclass answers without inventing facts, but it does not preserve every property family, reconstruct native statement bundles, or create migration authority."
