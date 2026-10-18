module DASHI.Wikimedia.JmdLeanIntegratedMachineLineageValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.JmdLeanIntegratedMachineLineageExact

_ : archiveSourceRetained canonicalJmdLeanIntegratedMachine ≡ true
_ = refl

_ : integratedRepositoryIsCanonicalExecutionSurface canonicalJmdLeanIntegratedMachine ≡ true
_ = refl

_ : rootDeclaresAgdaVendor canonicalJmdLeanIntegratedMachine ≡ true
_ = refl

_ : rootDeclaresAgdaCheck canonicalJmdLeanIntegratedMachine ≡ true
_ = refl

_ : rootDeclaresWikidataExecutable canonicalJmdLeanIntegratedMachine ≡ true
_ = refl

_ : rootDefaultBuildIncludesAgdaVendor canonicalJmdLeanIntegratedMachine ≡ false
_ = refl

_ : rootDefaultBuildIncludesAgdaCheck canonicalJmdLeanIntegratedMachine ≡ false
_ = refl

_ : rootDefaultBuildIncludesWikidataExecutable canonicalJmdLeanIntegratedMachine ≡ false
_ = refl

_ : executionObserved canonicalJmdLeanMachineExecutionStatus ≡ false
_ = refl

_ : executionCreatesWorldTruth canonicalJmdLeanMachineExecutionStatus ≡ false
_ = refl

_ : executionCreatesAgdaProof canonicalJmdLeanMachineExecutionStatus ≡ false
_ = refl
