{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.PackedOperatorKernelSWARExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- A2: FIRST PACKED-MEMORY PNF OPERATION
--
-- The semantic kernel is deliberately smaller than full sentence closure.
-- It classifies token lanes into the operator roles needed by the existing
-- sentence composer while dependency topology remains a separate fibre-local
-- input.  Scalar packed execution is the physical reference.  SWAR may refine
-- only the classification masks and earns no authority merely by being packed.
------------------------------------------------------------------------

data OperatorClass : Set where
  modalAux
  negation
  conditionMarker
  exceptionMarker
  transitionPredicate
  subjectDependency
  objectDependency : OperatorClass

record PackedOperatorKernel (Input Mask Topology : Set) : Set₁ where
  constructor packedOperatorKernel
  field
    scalarMask : Input → OperatorClass → Mask
    localTopology : Input → Topology

open PackedOperatorKernel public

------------------------------------------------------------------------
-- SWAR correctness is pointwise refinement of the scalar mask semantics.
-- Topology is intentionally not duplicated by the SWAR implementation: head
-- navigation continues to use the same fibre-local ordinal/delta carrier.
------------------------------------------------------------------------

record SWARMaskRefinement
    {Input Mask Topology : Set}
    (kernel : PackedOperatorKernel Input Mask Topology) : Set₁ where
  constructor swarMaskRefinement
  field
    swarMask : Input → OperatorClass → Mask
    maskExact :
      (input : Input) →
      (operator : OperatorClass) →
      swarMask input operator ≡ scalarMask kernel input operator

open SWARMaskRefinement public

scalarTopology :
  ∀ {Input Mask Topology : Set} →
  (kernel : PackedOperatorKernel Input Mask Topology) →
  Input → Topology
scalarTopology kernel = localTopology kernel

swarSharesScalarTopology :
  ∀ {Input Mask Topology : Set}
    (kernel : PackedOperatorKernel Input Mask Topology)
    (refinement : SWARMaskRefinement kernel)
    (input : Input) →
  scalarTopology kernel input ≡ localTopology kernel input
swarSharesScalarTopology kernel refinement input = refl

------------------------------------------------------------------------
-- Classification equivalence is exactly what downstream factor construction
-- may consume.  It does not prove a runtime win, authorize a second sentence
-- semantics, or move variable factor/residual/digest construction into SWAR.
------------------------------------------------------------------------

data SWARMaskParityImpliesRuntimeWin : Set where

data SWARMaskParityAuthorizesIndependentSemanticAuthority : Set where

data SWARMaskParityRequiresFactorConstructionInSWAR : Set where

parityDoesNotProveRuntimeWin : SWARMaskParityImpliesRuntimeWin → ⊥
parityDoesNotProveRuntimeWin ()

parityDoesNotCreateSecondAuthority :
  SWARMaskParityAuthorizesIndependentSemanticAuthority → ⊥
parityDoesNotCreateSecondAuthority ()

factorConstructionNeedNotMoveIntoSWAR :
  SWARMaskParityRequiresFactorConstructionInSWAR → ⊥
factorConstructionNeedNotMoveIntoSWAR ()

------------------------------------------------------------------------
-- Physical measurements remain data, not semantic constructors.  The runtime
-- engine tournament decides whether a semantically exact SWAR candidate earns
-- its keep on the same already-packed input.
------------------------------------------------------------------------

record SWARPhysicalReceipt : Set where
  constructor swarPhysicalReceipt
  field
    inputFingerprint : Nat
    scalarWallWork : Nat
    swarWallWork : Nat
    scalarCpuWork : Nat
    swarCpuWork : Nat

open SWARPhysicalReceipt public
