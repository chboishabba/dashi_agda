module DASHI.Physics.Closure.NSTriadKNValidatedPhysicalFiberImage where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation
import DASHI.Physics.Closure.NSTriadKNPhysicalClassEncoding as Encoding
import DASHI.Physics.Closure.NSTriadKNValidatedPhysicalClassCode as Validated
import DASHI.Physics.Closure.NSTriadKNExactPhysicalKernelIdentification as Exact

------------------------------------------------------------------------
-- Construct the canonical code fibre from the physical fibre.
--
-- This reverses the unsafe direction used by the old raw coordinate product.
-- The code list is definitionally the image of physically allocated retained
-- incidences, so completeness and the fibre-image theorem do not need an
-- "all raw codes are physical" assumption.
------------------------------------------------------------------------

record AllocatedPhysicalIncidence
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    (geometry : Allocation.Stage3GeometricPredicates retainedPolicy) : Set where
  constructor allocated-physical-incidence
  field
    physical : Allocation.RetainedPhysicalTriad retainedPolicy
    allocation : Allocation.NonResidualAllocation geometry physical

open AllocatedPhysicalIncidence public

encodeAllocated :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  AllocatedPhysicalIncidence geometry →
  Validated.ValidatedPhysicalCode N (Encoding.CodeValid representation)
encodeAllocated representation item =
  Validated.encodeValidated representation
    (physical item)
    (allocation item)

allocatedPhysicalWeight :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    (weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)) →
  AllocatedPhysicalIncidence geometry → Nat
allocatedPhysicalWeight weightDerivation item =
  Encoding.physicalWeight weightDerivation (physical item)

validatedCodeWeight :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  Validated.ValidatedPhysicalCode N (Encoding.CodeValid representation) →
  Nat
validatedCodeWeight representation code =
  Encoding.abstractCodeWeight representation
    (Validated.rawCode code)

encodeAllocatedPreservesWeight :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (item : AllocatedPhysicalIncidence geometry) →
  validatedCodeWeight representation (encodeAllocated representation item)
  ≡ allocatedPhysicalWeight weightDerivation item
encodeAllocatedPreservesWeight representation item =
  Encoding.physicalWeightPreserved representation
    (physical item)
    (allocation item)

record PhysicalFiberSource
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    (geometry : Allocation.Stage3GeometricPredicates retainedPolicy) : Set₁ where
  constructor physical-fiber-source
  field
    Index : Set
    physicalFiber :
      Index → Index → List (AllocatedPhysicalIncidence geometry)

open PhysicalFiberSource public

canonicalValidatedCodeFiber :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (source : PhysicalFiberSource geometry) →
  Index source → Index source →
  List (Validated.ValidatedPhysicalCode N
    (Encoding.CodeValid representation))
canonicalValidatedCodeFiber representation source i j =
  Exact.mapList (encodeAllocated representation)
    (physicalFiber source i j)

canonicalValidatedFiberIsPhysicalImage :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (source : PhysicalFiberSource geometry) →
  (i j : Index source) →
  canonicalValidatedCodeFiber representation source i j
  ≡
  Exact.mapList (encodeAllocated representation)
    (physicalFiber source i j)
canonicalValidatedFiberIsPhysicalImage representation source i j = refl

physicalFiberKernel :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    (weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)) →
  (source : PhysicalFiberSource geometry) →
  Index source → Index source → Nat
physicalFiberKernel weightDerivation source i j =
  KernelFormula.weightedListSum
    (allocatedPhysicalWeight weightDerivation)
    (physicalFiber source i j)

validatedCodeKernel :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (source : PhysicalFiberSource geometry) →
  Index source → Index source → Nat
validatedCodeKernel representation source i j =
  KernelFormula.weightedListSum
    (validatedCodeWeight representation)
    (canonicalValidatedCodeFiber representation source i j)

validatedKernelEqualsPhysicalKernel :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      Encoding.PhysicalStage3Representation geometry weightDerivation) →
  (source : PhysicalFiberSource geometry) →
  (i j : Index source) →
  validatedCodeKernel representation source i j
  ≡ physicalFiberKernel weightDerivation source i j
validatedKernelEqualsPhysicalKernel representation source i j =
  Exact.weightedListSumMap
    (encodeAllocated representation)
    (allocatedPhysicalWeight weightDerivation)
    (validatedCodeWeight representation)
    (encodeAllocatedPreservesWeight representation)
    (physicalFiber source i j)

validatedPhysicalFiberImageConstructed : Bool
validatedPhysicalFiberImageConstructed = true

validatedPhysicalFiberImageConstructedIsTrue :
  validatedPhysicalFiberImageConstructed ≡ true
validatedPhysicalFiberImageConstructedIsTrue = refl

oldRawFiberIdentifiedWithoutValidityProof : Bool
oldRawFiberIdentifiedWithoutValidityProof = false

oldRawFiberIdentifiedWithoutValidityProofIsFalse :
  oldRawFiberIdentifiedWithoutValidityProof ≡ false
oldRawFiberIdentifiedWithoutValidityProofIsFalse = refl
