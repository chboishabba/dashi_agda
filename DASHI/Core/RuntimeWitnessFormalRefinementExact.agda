module DASHI.Core.RuntimeWitnessFormalRefinementExact where

-- Runtime evidence is source/provenance-bearing data. It is not itself
-- a proof term for an arbitrary formal premise. Refinement requires the
-- premise to be supplied independently.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)

data RuntimeWitnessKind : Set where
  subjectIdentity propertyAlignment scopeComparability
    leftApplicability rightApplicability valueDistinctness
    positiveOutsideScope consumerObservationPreservation
    heterogeneousObservableBridge : RuntimeWitnessKind

record CheckedRuntimeWitness : Set where
  constructor checked-runtime-witness
  field
    witnessRef : String
    kind : RuntimeWitnessKind
    consumerRef : String
    sourceRevisionRefs : List String
    validationReceiptRef : String
    payloadDigestRef : String
    runtimeValidated : Bool
    runtimeValidatedTrue : runtimeValidated ≡ true
open CheckedRuntimeWitness public

-- The proposition/evidence object is indexed separately from runtime metadata.
record RefinedWitness (Premise : Set) : Set where
  constructor refined-witness
  field
    runtime : CheckedRuntimeWitness
    premise : Premise
open RefinedWitness public

refineWitness :
  ∀ {Premise : Set} →
  CheckedRuntimeWitness →
  Premise →
  RefinedWitness Premise
refineWitness runtime proof = refined-witness runtime proof

refinedCarriesPremise :
  ∀ {Premise : Set} →
  RefinedWitness Premise →
  Premise
refinedCarriesPremise = premise

forgetFormalPremise :
  ∀ {Premise : Set} →
  RefinedWitness Premise →
  CheckedRuntimeWitness
forgetFormalPremise = runtime

-- There is intentionally no CheckedRuntimeWitness → Premise function.
-- A domain-specific refinement procedure has to validate evidence and
-- separately construct the actual premise required by its theorem.
