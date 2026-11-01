module DASHI.Physics.Closure.NSTriadKNValidatedPhysicalClassCode where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation
import DASHI.Physics.Closure.NSTriadKNPhysicalClassEncoding as Encoding

------------------------------------------------------------------------
-- Raw Cartesian class coordinates are not presumed physical.
--
-- The canonical code carrier is the sparse subtype
--
--   Sigma code . CodeValid code.
--
-- This makes resonance, cutoff, parity, orientation, and retained-state
-- validity proof-relevant.  The stronger statement that every old raw code
-- is physical is isolated as a separate proposition and can be falsified by
-- one counterexample.
------------------------------------------------------------------------

record ValidatedPhysicalCode
    (N : Nat)
    (CodeValid :
      Relation.ConcreteNonResidualTriadIncidence N → Set) : Set where
  constructor validated-code
  field
    rawCode : Relation.ConcreteNonResidualTriadIncidence N
    validity : CodeValid rawCode

open ValidatedPhysicalCode public

AllRawCodesPhysical :
  (N : Nat) →
  (Relation.ConcreteNonResidualTriadIncidence N → Set) →
  Set
AllRawCodesPhysical N CodeValid =
  (code : Relation.ConcreteNonResidualTriadIncidence N) →
  CodeValid code

record InvalidRawCode
    (N : Nat)
    (CodeValid :
      Relation.ConcreteNonResidualTriadIncidence N → Set) : Set where
  constructor invalid-raw-code
  field
    invalidCode : Relation.ConcreteNonResidualTriadIncidence N
    invalidity : CodeValid invalidCode → ⊥

open InvalidRawCode public

oneInvalidCodeRefutesAllRawCodesPhysical :
  ∀ {N CodeValid} →
  InvalidRawCode N CodeValid →
  AllRawCodesPhysical N CodeValid →
  ⊥
oneInvalidCodeRefutesAllRawCodesPhysical counterexample allPhysical =
  invalidity counterexample
    (allPhysical (invalidCode counterexample))

validatedCodeAlwaysCarriesPhysicalEvidence :
  ∀ {N CodeValid} →
  (code : ValidatedPhysicalCode N CodeValid) →
  CodeValid (rawCode code)
validatedCodeAlwaysCarriesPhysicalEvidence = validity

------------------------------------------------------------------------
-- Decode only validated coordinates.
------------------------------------------------------------------------

decodeValidated :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  ValidatedPhysicalCode N (Encoding.CodeValid representation) →
  Allocation.RetainedPhysicalTriad retainedPolicy
decodeValidated representation code =
  Encoding.decode representation
    (rawCode code)
    (validity code)

validatedDecodeIsNonResidual :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (code : ValidatedPhysicalCode N (Encoding.CodeValid representation)) →
  Allocation.NonResidualAllocation geometry
    (decodeValidated representation code)
validatedDecodeIsNonResidual representation code =
  Encoding.decodedNonResidual representation
    (rawCode code)
    (validity code)

encodeValidated :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
  Allocation.NonResidualAllocation geometry τ →
  ValidatedPhysicalCode N (Encoding.CodeValid representation)
encodeValidated representation τ allocation =
  validated-code
    (Encoding.encode representation τ allocation)
    (Encoding.encodeValid representation τ allocation)

validatedEncodeDecodeRawRoundtrip :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (code : ValidatedPhysicalCode N (Encoding.CodeValid representation)) →
  Encoding.encode representation
    (decodeValidated representation code)
    (validatedDecodeIsNonResidual representation code)
  ≡ rawCode code
validatedEncodeDecodeRawRoundtrip representation code =
  Encoding.encodeDecodeCanonical representation
    (rawCode code)
    (validity code)

validatedSparseCodeArchitectureImplemented : Bool
validatedSparseCodeArchitectureImplemented = true

validatedSparseCodeArchitectureImplementedIsTrue :
  validatedSparseCodeArchitectureImplemented ≡ true
validatedSparseCodeArchitectureImplementedIsTrue = refl

allOldRawCodesDeclaredPhysical : Bool
allOldRawCodesDeclaredPhysical = false

allOldRawCodesDeclaredPhysicalIsFalse :
  allOldRawCodesDeclaredPhysical ≡ false
allOldRawCodesDeclaredPhysicalIsFalse = refl
