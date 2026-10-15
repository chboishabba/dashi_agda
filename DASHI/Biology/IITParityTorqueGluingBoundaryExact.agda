module DASHI.Biology.IITParityTorqueGluingBoundaryExact where

------------------------------------------------------------------------
-- PARITY INTEGRATION != TORQUE HANDEDNESS
--
-- The IIT branch now has a precise Boolean minimal-sufficiency statement:
-- among essential balanced two-input Boolean laws, parity/complement is the
-- entire class.  Separately, sibling PR #1164 source-writes the physical torque
-- specialization of the existing SO(3) 9/18/27 + pants/C3 machinery:
-- swapping lever and force negates Levi-Civita orientation and conjugates the
-- C3 phase, and nested torque cells build T^9/T^18 compatible boundaries.
--
-- This owner records the non-collapse between those two results.  XOR is
-- commutative, so parity output alone cannot remember input ordering.  Any
-- torque/handedness observer therefore needs ordered gluing/orientation data in
-- addition to parity synthesis.  The sibling PR is recorded as source evidence;
-- its unmerged theorem objects are not imported as authority here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITBooleanParityMinimalSufficiencyExact as Parity

------------------------------------------------------------------------
-- 1. XOR itself is swap-invariant.
------------------------------------------------------------------------

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

xorSwapInvariant : (a b : Bool) → xor a b ≡ xor b a
xorSwapInvariant false false = refl
xorSwapInvariant false true = refl
xorSwapInvariant true false = refl
xorSwapInvariant true true = refl

------------------------------------------------------------------------
-- 2. Any observer that sees only XOR output receives the same value after swap.
------------------------------------------------------------------------

xorOnlyObserverSwapInvariant :
  {Observation : Set} →
  (observer : Bool → Observation) →
  (a b : Bool) →
  observer (xor a b) ≡ observer (xor b a)
xorOnlyObserverSwapInvariant observer a b
  rewrite xorSwapInvariant a b = refl

------------------------------------------------------------------------
-- 3. Sibling torque source receipt.  No theorem import from the sibling branch.
------------------------------------------------------------------------

record TorqueSiblingSourceReceipt : Set where
  constructor torque-sibling-source-receipt
  field
    siblingPR : Nat
    observedHead : String
    sourceWritesOrderedOutputLeverForceVoxel : Bool
    sourceWritesSwapNegatesOrientation : Bool
    sourceWritesSwapConjugatesC3Phase : Bool
    sourceWritesDepthThreePantsRechart : Bool
    sourceWritesNestedT9Dialectic : Bool
    sourceWritesCompatibleT18Boundary : Bool
    sourceKeepsIrreducibleTriadicFaceSeparate : Bool
    siblingTheoremAuthorityImportedHere : Bool

canonicalTorqueSiblingSourceReceipt : TorqueSiblingSourceReceipt
canonicalTorqueSiblingSourceReceipt =
  torque-sibling-source-receipt
    1164
    "90706035851c3164a105ff326186be6afe620aa1"
    true true true true true true true false

------------------------------------------------------------------------
-- 4. Combined conjecture boundary.
------------------------------------------------------------------------

record ParityTorqueGluingBoundary : Set where
  constructor parity-torque-gluing-boundary
  field
    essentialBalancedBooleanClassIsParity : Bool
    parityOutputAloneDistinguishesInputOrder : Bool
    orderedGluingNeededForHandedness : Bool
    torqueMagnitudeIdentifiedWithParityBit : Bool
    localParityManufacturesIrreducibleTriadicFace : Bool
    siblingTorqueAuthorityImported : Bool

canonicalParityTorqueGluingBoundary : ParityTorqueGluingBoundary
canonicalParityTorqueGluingBoundary =
  parity-torque-gluing-boundary
    true false true false false false

parityStructuralWitness : Parity.ParityOrComplement Parity.xorGate
parityStructuralWitness = Parity.xorParity
